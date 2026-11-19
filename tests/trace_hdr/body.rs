//! The Handshake body of the trace: real clients and servers, and seeded bodies through `Handshake::on_fragment`.

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_security::ClientTickets;
use pinc_tests::{SplitMix64, Store, T0, World};
use pinc_transport::conn::{FragmentView, ReasmProbe};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_wire::Writer;

use super::headers::{arr, bytes, pick};

pub fn view_json(v: &pinc_transport::conn::ReasmView) -> String {
    let runs: Vec<String> = v.runs.iter().map(|(s, e)| format!("[{s},{e}]")).collect();
    format!(r#"{{"runs":[{}],"total":{}}}"#, runs.join(","), v.total)
}

/// The body of a Handshake packet as `write_handshake` puts it: `varint(total) varint(off) fragment`.
pub fn hs_body(total: u64, off: u64, data: &[u8]) -> Vec<u8> {
    let mut b = vec![0u8; 18 + data.len()];
    let mut w = Writer::new(&mut b);
    w.put_varint(total).unwrap();
    w.put_varint(off).unwrap();
    w.put_slice(data).unwrap();
    let n = w.written().len();
    b.truncate(n);
    b
}

pub type Srv<'a> = pinc_tests::Node<'a>;

/// One body handed to `Handshake::on_fragment` of a real connection: the event has the body, the reassembly before
/// and after, the length of the message if it completed, and the first bytes of the message buffer at the offset the
/// body names (the whole window is compared here, against the bytes of the fragment).
pub fn frag(out: &mut String, srv: &mut Srv<'_>, body: &[u8]) -> FragmentView {
    let v = srv.conn.trace_fragment(body);
    let mut r = pinc_wire::Reader::new(body);
    let parsed = r.read_varint().ok().and_then(|t| r.read_varint().ok().map(|o| (t, o)));
    let data = r.read_bytes(r.remaining()).unwrap_or_default();
    let mut mo = 0;
    if let Some((t, o)) = parsed {
        let (t, o) = (usize::try_from(t).unwrap(), usize::try_from(o).unwrap_or(usize::MAX));
        let stop = o.saturating_add(data.len()).min(t);
        let kept = v.ret == Some(t) || (v.after.total == t && v.after.runs.iter().any(|&(s, e)| s <= o && stop <= e));
        if o < stop && kept {
            assert_eq!(
                v.message[o..stop],
                data[..stop - o],
                "the buffer does not hold the fragment"
            );
        }
        if o < v.message.len() {
            mo = o;
        }
    }
    let w = &v.message[mo..v.message.len().min(mo + 48)];
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"hf","body":{},"max":{},"nr":{},"b":{},"a":{},"ret":{},"mo":{mo},"w":{}}}"#,
        arr(body),
        ReasmProbe::MAX_MESSAGE,
        ReasmProbe::RUNS,
        view_json(&v.before),
        view_json(&v.after),
        v.ret.map_or(-1, |t| i64::try_from(t).unwrap()),
        arr(w)
    );
    v
}

/// A datagram a real client built: its Handshake packet is a long header and the three parts of the body, and the
/// body, cut where the header says, is what a server hands to the reassembly.
pub fn hw_event(out: &mut String, d: &[u8], win: usize, srv: &mut Srv<'_>) {
    if d.first().is_none_or(|b| b & 0xc0 != 0xc0) {
        return;
    }
    let (h, hl) = LongHeader::parse(d).unwrap();
    assert_eq!(h.ty, LongType::Handshake);
    let body = &d[hl..hl + h.body_len];
    let mut r = pinc_wire::Reader::new(body);
    let total = usize::try_from(r.read_varint().unwrap()).unwrap();
    let off = usize::try_from(r.read_varint().unwrap()).unwrap();
    let data = r.read_bytes(r.remaining()).unwrap();
    assert!(!data.is_empty() && off + data.len() <= total && total <= ReasmProbe::MAX_MESSAGE);
    assert_eq!(
        h.body_len,
        pinc_wire::varint::encoded_len(total as u64) + pinc_wire::varint::encoded_len(off as u64) + data.len()
    );
    assert!(hl + h.body_len <= win);
    let _ = writeln!(out, r#"{{"t":"txhd","op":"hw","d":{},"win":{win}}}"#, arr(d));
    let v = frag(out, srv, body);
    // what a server keeps of the fragment is the bytes the client wrote
    if v.ret.is_none() {
        assert_eq!(
            v.message.get(off..off + data.len()),
            Some(data),
            "the buffer lost the fragment"
        );
    }
}

/// Bodies that are no fragment, or one the reassembly refuses.
pub fn junk(out: &mut String, rng: &mut SplitMix64, srv: &mut Srv<'_>, avoid: u64) {
    let max = ReasmProbe::MAX_MESSAGE as u64;
    let dlen = 1 + pick(rng, 30) as usize;
    let data = bytes(rng, dlen);
    let body = match pick(rng, 16) {
        0 => vec![],
        1 => vec![0x80],
        2 => vec![0x80, 0x00],
        3 => vec![0x80; 9],
        4 => vec![0x80; 8],
        5 => vec![0xff; 12],
        6 => hs_body(10, 0, &[])[..1].to_vec(),
        7 => {
            let mut b = hs_body(10, 0, &[]);
            b.truncate(1);
            b.push(0x80);
            b
        }
        8 => hs_body(0, 0, &data),
        9 => hs_body(max + 1 + pick(rng, 3), 0, &data),
        10 => hs_body(1 << 40, 0, &data),
        11 => hs_body(max, max + pick(rng, 3), &data),
        12 => hs_body(100, 100 + pick(rng, 3), &data),
        13 => hs_body(100, (1 << 62) + pick(rng, 3), &data),
        14 => hs_body(100, (1 << 63) - 1, &data),
        _ => {
            let t = 1 + pick(rng, 300);
            let mut b = hs_body(if t == avoid { t + 1 } else { t }, pick(rng, 100), &data);
            b[0] |= 0x80;
            b
        }
    };
    frag(out, srv, &body);
}

pub fn hs_run(seed: u64, runs: u32) -> String {
    let mut rng = SplitMix64::new(seed);
    let mut out = String::new();
    // the writer: a real client, in windows from the smallest to a jumbo one, over the first flight and its resends,
    // every datagram handed on to a real server
    for (n, alg) in [IdentityAlg::Ed25519, IdentityAlg::Hybrid].into_iter().enumerate() {
        for (i, win) in [64usize, 90, 150, 300, 700, 1200, 1452, 2000].into_iter().enumerate() {
            let mut world = World::new(alg);
            world.seed = u8::try_from(n * 16 + i).unwrap();
            let (mut cs, mut ss) = (Store::new(true), Store::new(false));
            let mut client = world.client(&mut cs, None, ClientTickets::new());
            let mut server = world.server(&mut ss);
            let mut now = T0;
            for (round, ms) in [0u64, 600, 2000, 5000].into_iter().enumerate() {
                if round > 0 {
                    now += ms * 1_000_000;
                    client.with_env(now, |c, env| c.handle_timeout(env));
                }
                for _ in 0..60 {
                    let mut buf = vec![0u8; win];
                    let Some(tx) = client.with_env(now, |c, env| c.poll_transmit(env, &mut buf)) else {
                        break;
                    };
                    hw_event(&mut out, &buf[..tx.len], win, &mut server);
                }
            }
        }
    }
    // the reader: bodies a server is handed, cut from messages of every length, in every order, with refused ones
    // in between
    let world = World::new(IdentityAlg::Ed25519);
    let max = ReasmProbe::MAX_MESSAGE;
    for run in 0..runs {
        let mut ss = Store::new(false);
        let mut srv = world.server(&mut ss);
        for _ in 0..4 {
            let total = match pick(&mut rng, 8) {
                0 => 1 + pick(&mut rng, 12) as usize,
                1 => max,
                2 => max + 1 + pick(&mut rng, 4) as usize,
                _ => 1 + pick(&mut rng, 2400) as usize,
            };
            let msg = bytes(&mut rng, total);
            // a message of another length first, so that no run of the last message is taken for a run of this one
            frag(&mut out, &mut srv, &hs_body(if total == 1 { 2 } else { 1 }, 0, &[]));
            let size = [3usize, 40, 200, 700, 1300][pick(&mut rng, 5) as usize].max(total / 30);
            let mut frags: Vec<(usize, usize)> = Vec::new();
            let mut at = 0;
            while at < total {
                let len = (1 + pick(&mut rng, size as u64) as usize).min(total - at);
                frags.push((at, len));
                at += len;
            }
            let mode = (run + pick(&mut rng, 6) as u32) % 6;
            match mode {
                1 => frags.reverse(),
                2 => {
                    for i in (1..frags.len()).rev() {
                        frags.swap(i, pick(&mut rng, i as u64 + 1) as usize);
                    }
                }
                3 => {
                    let odd: Vec<_> = frags.iter().copied().skip(1).step_by(2).collect();
                    let even: Vec<_> = frags.iter().copied().step_by(2).collect();
                    frags = [odd, even].concat();
                }
                4 => frags = frags.iter().flat_map(|f| [*f, *f]).collect(),
                5 => {
                    // overlapping, and running past the end of the message
                    for f in &mut frags {
                        let back = pick(&mut rng, 40) as usize;
                        f.0 = f.0.saturating_sub(back);
                        f.1 += back + pick(&mut rng, 20) as usize;
                    }
                }
                _ => {}
            }
            for (i, (off, len)) in frags.into_iter().enumerate() {
                if pick(&mut rng, 5) == 0 {
                    junk(&mut out, &mut rng, &mut srv, total as u64);
                }
                let end = (off + len).min(total);
                let mut data = msg[off.min(total)..end].to_vec();
                if off + len > total {
                    data.extend(bytes(&mut rng, off + len - total));
                }
                let body = hs_body(total as u64, off as u64, &data);
                let v = frag(&mut out, &mut srv, &body);
                if total <= max && v.ret == Some(total) {
                    assert_eq!(v.message, msg, "a completed message is not the message cut ({i})");
                }
            }
        }
        junk(&mut out, &mut rng, &mut srv, 0);
    }
    out
}
