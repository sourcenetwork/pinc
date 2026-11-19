//! The lenient scan of a message and the fault injection of `trace_reconcile`.
use pinc_tests::SplitMix64;
use pinc_wire::varint;

type Item = Vec<u8>;

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

// ---- a lenient scan of a message -----------------------------------------------------------------------------------

/// What a lenient scan of a message found: the items of its item lists, the span of each part, where the count is.
#[derive(Default)]
pub struct Scan {
    pub items: Vec<Item>,
    pub big: bool,
    pub count_at: Option<usize>,
    pub parts: Vec<(usize, usize)>,
}

const BIG: u64 = 1 << 31;

fn var(m: &[u8], p: &mut usize, s: &mut Scan) -> Option<usize> {
    let (v, used) = varint::decode(m.get(*p..)?).ok()?;
    *p += used;
    if v >= BIG {
        s.big = true;
        return None;
    }
    Some(v as usize)
}

fn skip(m: &[u8], p: &mut usize, n: usize) -> Option<()> {
    let end = p.checked_add(n)?;
    (end <= m.len()).then(|| *p = end)
}

pub fn scan_items(m: &[u8], p: &mut usize, s: &mut Scan) -> Option<()> {
    let n = var(m, p, s)?;
    for _ in 0..n {
        let len = var(m, p, s)?;
        let start = *p;
        skip(m, p, len)?;
        s.items.push(m[start..*p].to_vec());
    }
    Some(())
}

pub fn scan_inner(m: &[u8], first: bool, s: &mut Scan) -> Option<()> {
    let mut p = 3;
    if first {
        let l = var(m, &mut p, s)?;
        skip(m, &mut p, l)?;
        var(m, &mut p, s)?;
    }
    s.count_at = Some(p);
    let raw = var(m, &mut p, s)?;
    for _ in 0..(raw >> 1).min(m.len()) {
        let start = p;
        let tag = *m.get(p)?;
        p += 1;
        let bounds = if tag & 0x80 != 0 { 1 } else { 2 };
        for _ in 0..bounds {
            p += 1;
            let n = var(m, &mut p, s)?;
            skip(m, &mut p, n)?;
        }
        match tag & 0x7f {
            1 | 6 => skip(m, &mut p, 16)?,
            2 => {
                let c = var(m, &mut p, s)?;
                skip(m, &mut p, c.checked_mul(8)?)?;
            }
            3 | 5 => scan_items(m, &mut p, s)?,
            4 => {
                let c = var(m, &mut p, s)?;
                skip(m, &mut p, c.div_ceil(8))?;
                scan_items(m, &mut p, s)?;
            }
            7 => {}
            _ => return None,
        }
        s.parts.push((start, p));
    }
    Some(())
}

pub fn scan(m: &[u8], first: bool) -> Scan {
    let mut s = Scan::default();
    if m.len() >= 3 {
        let _ = scan_inner(m, first, &mut s);
    }
    s
}

pub fn fix_len(m: &mut [u8]) {
    if m.len() >= 3 {
        let n = m.len() - 3;
        m[0] = (n >> 16) as u8;
        m[1] = (n >> 8) as u8;
        m[2] = n as u8;
    }
}

pub fn mutate_msg(kind: u32, m: &mut Vec<u8>, first: bool, rng: &mut SplitMix64) {
    let sc = scan(m, first);
    let body_len = m.len().saturating_sub(3);
    let rnd = |rng: &mut SplitMix64, n: usize| below(rng, n.max(1) as u64) as usize;
    match kind {
        0 | 12 if body_len > 0 => {
            let at = 3 + rnd(rng, body_len);
            if kind == 0 {
                m[at] ^= 1 << below(rng, 8);
            } else {
                m[at] = rng.next_u64() as u8;
            }
        }
        1 if m.len() >= 3 => m[rnd(rng, 3)] ^= 1 << below(rng, 8),
        2 | 3 if body_len > 0 => {
            m.truncate(3 + rnd(rng, body_len));
            if kind == 2 {
                fix_len(m);
            }
        }
        4 | 5 => {
            for _ in 0..=rnd(rng, 8) {
                m.push(rng.next_u64() as u8);
            }
            if kind == 4 {
                fix_len(m);
            }
        }
        6..=9 if !sc.parts.is_empty() => {
            let (s, e) = sc.parts[rnd(rng, sc.parts.len())];
            let part = m[s..e].to_vec();
            if kind == 6 || kind == 7 {
                m.drain(s..e);
            } else {
                m.splice(e..e, part);
            }
            if let Some(c) = sc.count_at
                && (kind == 7 || kind == 9)
                && m[c] < 0x80
            {
                if kind == 7 {
                    m[c] = m[c].saturating_sub(2);
                } else {
                    m[c] = m[c].saturating_add(2).min(0x7f);
                }
            }
            fix_len(m);
        }
        10 if !sc.parts.is_empty() => {
            let (s, _) = sc.parts[rnd(rng, sc.parts.len())];
            m[s] = [0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87][rnd(rng, 17)];
        }
        13 => {
            // A count of 2^63 - 1 or so: nine bytes of a varint.
            if let Some(c) = sc.count_at {
                m.splice(c..=c, [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
                fix_len(m);
            }
        }
        14 if body_len > 0 => {
            let at = 3 + rnd(rng, body_len);
            let end = (at + 9).min(m.len());
            m.splice(
                at..end,
                [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f][..end - at]
                    .iter()
                    .copied(),
            );
            if rng.next_u64() & 1 == 0 {
                fix_len(m);
            }
        }
        11 => {
            if let Some(c) = sc.count_at {
                m[c] = rnd(rng, 40) as u8;
            }
        }
        _ => {
            if body_len > 0 {
                let at = 3 + rnd(rng, body_len);
                m[at] = m[at].wrapping_add(1);
            }
        }
    }
}
