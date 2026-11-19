//! Trace generation for the byte-text helpers of the `UPnP` leg (`pinc_portmap::text_trace`, the probe of the crate's
//! `trace` feature over `text.rs`): the real bounded writer (`Out::put`, `dec`, `ip4`, `done`), `parse_u32`,
//! `parse_ip4`, `trim`, `find`, `header` and `element`, recorded as ndjson (`portmap/text.ndjson` under
//! `PINC_TRACE_DIR`) for the TLA+ trace check (`TracePortMapText.tla`).
//!
//! A `u32` is written as `[hi, lo]` (`hi = v >> 16`), because TLC's integers are 32 bits wide; byte strings are arrays of
//! 0..=255. One event is written per call, with its input and its result (for the writer the whole buffer after the run,
//! which was filled with `fill` before, and `done`, -1 for `None`). The inputs are the boundary sets of
//! `PortMapText.tla` (every capacity 0 to 6 with every run of up to 4 puts of 0 to 4 bytes, `dec` of the boundary
//! numbers into every capacity 0 to 11, every address over a few octets, every short string over the parser alphabets)
//! and seeded random ones. Every call is also checked here against the documented rule computed independently of the
//! code, so the test is meaningful without the proof tools. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::needless_range_loop,
    unreachable_pub,
    clippy::cast_possible_wrap,
    clippy::items_after_statements,
    clippy::manual_is_multiple_of
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::net::Ipv4Addr;

use pinc_portmap::text_trace as t;
use pinc_tests::SplitMix64;

/// A JSON array of the bytes.
fn arr(b: &[u8]) -> String {
    let body: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// A `u32` as `[hi, lo]`.
fn u(v: u32) -> String {
    format!("[{},{}]", v >> 16, v & 0xffff)
}

/// `done` as the model has it: the length, or -1.
fn dn(d: Option<usize>) -> i64 {
    d.map_or(-1, |n| n as i64)
}

/// Every string of 0 to `max` bytes over `alpha`.
fn strings(alpha: &[u8], max: usize) -> Vec<Vec<u8>> {
    let mut all = vec![Vec::new()];
    let mut layer = vec![Vec::new()];
    for _ in 0..max {
        layer = layer
            .iter()
            .flat_map(|s: &Vec<u8>| {
                alpha.iter().map(move |c| {
                    let mut n = s.clone();
                    n.push(*c);
                    n
                })
            })
            .collect();
        all.extend(layer.iter().cloned());
    }
    all
}

/// The writer's result for a run of puts, from the rule: every put before the first that does not fit, in order, then
/// nothing more; `done` is the total, or `None` after an overflow.
fn model_put(cap: usize, fill: u8, ps: &[Vec<u8>]) -> (Option<usize>, Vec<u8>) {
    let mut buf = vec![fill; cap];
    let (mut n, mut ok) = (0, true);
    for p in ps {
        if ok && n + p.len() <= cap {
            buf[n..n + p.len()].copy_from_slice(p);
            n += p.len();
        } else {
            ok = false;
        }
    }
    (ok.then_some(n), buf)
}

fn put_event(out: &mut String, cap: usize, fill: u8, ps: &[Vec<u8>]) {
    let mut buf = vec![fill; cap];
    let refs: Vec<&[u8]> = ps.iter().map(Vec::as_slice).collect();
    let done = t::out_run(&mut buf, &refs);
    let (want_done, want_buf) = model_put(cap, fill, ps);
    assert_eq!(done, want_done, "writer run of cap {cap}: {ps:?}");
    assert_eq!(buf, want_buf, "writer run of cap {cap}: {ps:?}");
    let list: Vec<String> = ps.iter().map(|p| arr(p)).collect();
    let _ = writeln!(
        out,
        r#"{{"op":"put","cap":{cap},"fill":{fill},"ps":[{}],"buf":{},"done":{}}}"#,
        list.join(","),
        arr(&buf),
        dn(done)
    );
}

fn dec_event(out: &mut String, cap: usize, v: u32) {
    let mut buf = vec![0xaa; cap];
    let done = t::out_dec(&mut buf, v);
    let want = v.to_string().into_bytes();
    if want.len() <= cap {
        assert_eq!(done, Some(want.len()), "dec of {v} into {cap}");
        assert_eq!(&buf[..want.len()], want.as_slice());
        assert_eq!(t::parse_u32(&buf[..want.len()]), Some(v));
    } else {
        assert_eq!(done, None, "dec of {v} into {cap}");
        assert!(buf.iter().all(|b| *b == 0xaa), "a dec that did not fit wrote");
    }
    if let Some(n) = done {
        assert!(buf[n..].iter().all(|b| *b == 0xaa), "dec of {v} wrote past its length");
    }
    let _ = writeln!(
        out,
        r#"{{"op":"dec","cap":{cap},"fill":170,"v":{},"buf":{},"done":{}}}"#,
        u(v),
        arr(&buf),
        dn(done)
    );
}

fn ip4_event(out: &mut String, cap: usize, o: [u8; 4]) {
    let ip = Ipv4Addr::from(o);
    let mut buf = vec![0xaa; cap];
    let done = t::out_ip4(&mut buf, ip);
    let want = ip.to_string().into_bytes();
    if want.len() <= cap {
        assert_eq!(done, Some(want.len()), "ip4 of {ip} into {cap}");
        assert_eq!(&buf[..want.len()], want.as_slice());
        assert_eq!(t::parse_ip4(&buf[..want.len()]), Some(ip));
    } else {
        assert_eq!(done, None, "ip4 of {ip} into {cap}");
    }
    let _ = writeln!(
        out,
        r#"{{"op":"ip4","cap":{cap},"fill":170,"o":[{},{},{},{}],"buf":{},"done":{}}}"#,
        o[0],
        o[1],
        o[2],
        o[3],
        arr(&buf),
        dn(done)
    );
}

fn pu32_event(out: &mut String, b: &[u8]) {
    let got = t::parse_u32(b);
    let want = (!b.is_empty() && b.len() <= 10 && b.iter().all(u8::is_ascii_digit))
        .then(|| b.iter().fold(0u64, |a, c| a * 10 + u64::from(c - b'0')))
        .and_then(|v| u32::try_from(v).ok());
    assert_eq!(got, want, "parse_u32 of {b:?}");
    match got {
        Some(v) => {
            let _ = writeln!(out, r#"{{"op":"pu32","b":{},"ok":true,"v":{}}}"#, arr(b), u(v));
        }
        None => {
            let _ = writeln!(out, r#"{{"op":"pu32","b":{},"ok":false}}"#, arr(b));
        }
    }
}

fn pip4_event(out: &mut String, b: &[u8]) {
    let got = t::parse_ip4(b);
    let parts: Vec<&[u8]> = b.split(|c| *c == b'.').collect();
    // each part: 1 to 3 ASCII digits of value at most 255
    let part = |p: &[u8]| -> Option<u8> {
        if !(1..=3).contains(&p.len()) || !p.iter().all(u8::is_ascii_digit) {
            return None;
        }
        std::str::from_utf8(p).unwrap().parse().ok()
    };
    let want = match parts.as_slice() {
        [a, b, c, d] => match (part(a), part(b), part(c), part(d)) {
            (Some(a), Some(b), Some(c), Some(d)) => Some(Ipv4Addr::new(a, b, c, d)),
            _ => None,
        },
        _ => None,
    };
    assert_eq!(got, want, "parse_ip4 of {b:?}");
    match got {
        Some(ip) => {
            let o = ip.octets();
            let _ = writeln!(
                out,
                r#"{{"op":"pip4","b":{},"ok":true,"o":[{},{},{},{}]}}"#,
                arr(b),
                o[0],
                o[1],
                o[2],
                o[3]
            );
        }
        None => {
            let _ = writeln!(out, r#"{{"op":"pip4","b":{},"ok":false}}"#, arr(b));
        }
    }
}

fn trim_event(out: &mut String, b: &[u8]) {
    let got = t::trim(b);
    let is_ws = |c: &u8| *c == b' ' || *c == b'\t';
    let mut s = 0;
    while s < b.len() && is_ws(&b[s]) {
        s += 1;
    }
    let mut e = b.len();
    while e > s && is_ws(&b[e - 1]) {
        e -= 1;
    }
    assert_eq!(got, &b[s..e], "trim of {b:?}");
    let _ = writeln!(out, r#"{{"op":"trim","b":{},"r":{}}}"#, arr(b), arr(got));
}

fn find_event(out: &mut String, h: &[u8], n: &[u8]) {
    let got = t::find(h, n);
    let want = if n.is_empty() {
        Some(0)
    } else {
        (0..=h.len().saturating_sub(n.len())).find(|p| p + n.len() <= h.len() && &h[*p..p + n.len()] == n)
    };
    assert_eq!(got, want, "find {n:?} in {h:?}");
    let _ = writeln!(out, r#"{{"op":"find","h":{},"n":{},"p":{}}}"#, arr(h), arr(n), dn(got));
}

fn header_event(out: &mut String, h: &[u8], name: &[u8]) {
    match t::header(h, name) {
        Some(v) => {
            let _ = writeln!(
                out,
                r#"{{"op":"header","h":{},"name":{},"ok":true,"v":{}}}"#,
                arr(h),
                arr(name),
                arr(v)
            );
        }
        None => {
            let _ = writeln!(
                out,
                r#"{{"op":"header","h":{},"name":{},"ok":false}}"#,
                arr(h),
                arr(name)
            );
        }
    }
}

fn element_event(out: &mut String, b: &[u8], from: usize, name: &[u8]) {
    match t::element(b, from, name) {
        Some((text, next)) => {
            let _ = writeln!(
                out,
                r#"{{"op":"element","b":{},"from":{from},"name":{},"ok":true,"text":{},"next":{next}}}"#,
                arr(b),
                arr(name),
                arr(text)
            );
        }
        None => {
            let _ = writeln!(
                out,
                r#"{{"op":"element","b":{},"from":{from},"name":{},"ok":false}}"#,
                arr(b),
                arr(name)
            );
        }
    }
}

/// The values `dec` is run on: 0 to 999, every `2^j - 1`, `2^j`, `2^j + 1` and `10^k - 1`, `10^k`, `10^k + 1` within a
/// `u32`, and `u32::MAX`.
fn edges() -> BTreeSet<u32> {
    let mut s: BTreeSet<u32> = (0..=999).collect();
    s.insert(u32::MAX);
    for j in 0..32 {
        let p = 1u64 << j;
        s.extend([p - 1, p, p + 1].into_iter().filter_map(|v| u32::try_from(v).ok()));
    }
    for k in 0..=9 {
        let p = 10u64.pow(k);
        s.extend([p - 1, p, p + 1].into_iter().filter_map(|v| u32::try_from(v).ok()));
    }
    s
}

/// The alphabet of the random strings, biased to what the parsers read.
const ALPHA: &[u8] = b"00112233445566778899..:::<<>>//  \t\r\naa";

fn random_bytes(rng: &mut SplitMix64, max: usize) -> Vec<u8> {
    let n = (rng.next_u64() % (max as u64 + 1)) as usize;
    (0..n)
        .map(|_| ALPHA[(rng.next_u64() % ALPHA.len() as u64) as usize])
        .collect()
}

#[test]
fn the_text_helpers_match_the_models() {
    let mut out = String::new();

    // the writer: every capacity 0..=6 with every run of up to 4 puts of 0..=4 bytes, put j (counted from 1) writing j
    let mut runs: Vec<Vec<usize>> = vec![Vec::new()];
    let mut layer: Vec<Vec<usize>> = vec![Vec::new()];
    for _ in 0..4 {
        layer = layer
            .iter()
            .flat_map(|r| {
                (0..=4).map(move |l| {
                    let mut n = r.clone();
                    n.push(l);
                    n
                })
            })
            .collect();
        runs.extend(layer.iter().cloned());
    }
    let mut count = 0;
    for cap in 0..=6 {
        for r in &runs {
            let ps: Vec<Vec<u8>> = r.iter().enumerate().map(|(j, l)| vec![(j + 1) as u8; *l]).collect();
            put_event(&mut out, cap, 0, &ps);
            count += 1;
        }
    }
    assert_eq!(count, 5467);
    let mut rng = SplitMix64::traced(0x7465_7874);
    for _ in 0..64 {
        let cap = (rng.next_u64() % 129) as usize;
        let n = 1 + (rng.next_u64() % 6) as usize;
        let ps: Vec<Vec<u8>> = (0..n)
            .map(|_| {
                let mut p = vec![0u8; (rng.next_u64() % 41) as usize];
                rng.fill(&mut p);
                p
            })
            .collect();
        put_event(&mut out, cap, 0xff, &ps);
    }

    // dec and ip4
    let values = edges();
    for v in &values {
        for cap in 0..=11 {
            dec_event(&mut out, cap, *v);
        }
    }
    const OCT: [u8; 6] = [0, 9, 10, 99, 100, 255];
    for a in OCT {
        for b in OCT {
            for c in OCT {
                for d in OCT {
                    for cap in 6..=15 {
                        ip4_event(&mut out, cap, [a, b, c, d]);
                    }
                }
            }
        }
    }

    // parse_u32
    let short = strings(b"/0159: ", 3);
    assert_eq!(short.len(), 400);
    for s in &short {
        pu32_event(&mut out, s);
    }
    for v in &values {
        let d = v.to_string().into_bytes();
        pu32_event(&mut out, &d);
        pu32_event(&mut out, &[b"0".as_slice(), d.as_slice()].concat());
        pu32_event(&mut out, &[d.as_slice(), b":".as_slice()].concat());
    }
    for s in ["4294967295", "4294967296", "9999999999", "10000000000", "00000000001"] {
        pu32_event(&mut out, s.as_bytes());
    }

    // parse_ip4
    for a in [0u8, 9, 10, 255] {
        for b in [0u8, 9, 10, 255] {
            for c in [0u8, 9, 10, 255] {
                for d in [0u8, 9, 10, 255] {
                    pip4_event(&mut out, format!("{a}.{b}.{c}.{d}").as_bytes());
                }
            }
        }
    }
    for s in [
        "1.2.3",
        "1.2.3.4.",
        "1.2.3.4.5",
        "256.1.1.1",
        "1..2.3",
        "0001.1.1.1",
        "01.1.1.1",
        ".1.1.1",
        "1.1.1.1 ",
        "a.1.1.1",
        "999.1.1.1",
        "",
    ] {
        pip4_event(&mut out, s.as_bytes());
    }

    // trim and find
    for s in strings(b" \tab", 4) {
        trim_event(&mut out, &s);
    }
    let hays = strings(b"ab", 5);
    let needles = strings(b"ab", 2);
    for h in &hays {
        for n in &needles {
            find_event(&mut out, h, n);
        }
    }

    // header: every head of 0..=3 lines, each ended by CRLF or LF
    const LINES: [&str; 5] = [
        "Content-Length: 12",
        "content-length:7",
        " Location : x ",
        "X:",
        "nocolon",
    ];
    const ENDS: [&str; 2] = ["\r\n", "\n"];
    let pieces: Vec<String> = LINES
        .iter()
        .flat_map(|l| ENDS.iter().map(move |e| format!("{l}{e}")))
        .collect();
    let mut heads = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..3 {
        layer = layer
            .iter()
            .flat_map(|h| pieces.iter().map(move |p| format!("{h}{p}")))
            .collect();
        heads.extend(layer.iter().cloned());
    }
    for h in &heads {
        for name in ["content-length", "location", "x", "missing"] {
            header_event(&mut out, h.as_bytes(), name.as_bytes());
        }
    }

    // element
    for body in [
        "<a>t</a>",
        "<u:a x=\"1\">t</u:a>",
        "<a>t",
        "<a",
        "</a>",
        "<b><a> t </a></b>",
        "<a>1</a><a>2</a>",
    ] {
        for from in 0..=body.len() + 1 {
            element_event(&mut out, body.as_bytes(), from, b"a");
        }
    }

    // seeded random strings
    let mut rng = SplitMix64::traced(0x7465_7874_0002);
    for _ in 0..2048 {
        let b = random_bytes(&mut rng, 24);
        pu32_event(&mut out, &b);
        pip4_event(&mut out, &b);
        trim_event(&mut out, &b);
        let n = random_bytes(&mut rng, 3);
        find_event(&mut out, &b, &n);
        let name: &[u8] = [b"content-length".as_slice(), b"location", b"x", b"a"][(rng.next_u64() % 4) as usize];
        header_event(&mut out, &b, name);
        let from = (rng.next_u64() % (b.len() as u64 + 2)) as usize;
        element_event(&mut out, &b, from, if rng.next_u64() % 2 == 0 { b"a" } else { b"x" });
    }

    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        let dir = std::path::PathBuf::from(dir).join("portmap");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("text.ndjson"), out).unwrap();
    }
}
