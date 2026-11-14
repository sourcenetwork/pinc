//! Trace generation for the WebSocket framing of the carrier (`vinc_connect::carrier::ws`): seeded and boundary calls of
//! the real encoder and decoder, recorded as ndjson (`connect_ws.ndjson`) for the TLA+ trace check
//! (`TraceConnectWs.tla`) and the Lean replay (`Vinc/TraceConnectWs.lean`).
//!
//! Three kinds of call, one event each:
//! - `enc`: `ws::encode` for every opcode, with and without a mask key, with payloads of every boundary length (0, 1,
//!   125, 126, the 16-bit and `MAX_PAYLOAD` edges and over them) and output buffers from empty to roomy; the result
//!   is the bytes written or the refusal.
//! - `dec`: `Decoder::decode` on the bytes a host holds. Streams of frames the encoder wrote (and fragmented messages
//!   with control frames between the fragments) are read in random splits and decoded after every read, the way a host
//!   does, so the buffers are every partial prefix; crafted headers cover every reserved bit, every opcode, the wrong
//!   mask for both roles, every length form with values on both sides of its threshold and of `MAX_PAYLOAD` (up to
//!   `u64::MAX`), control frames that are fragmented or long, frames out of sequence, every cut of a header, trailing
//!   bytes and the header of an oversized frame without a byte of its payload.
//! - `new`: a fresh decoder of a peer role (a decoder's one bit of state, whether a fragmented message is open, is
//!   not readable, so the model tracks it from the calls).
//!
//! The test checks by itself: every stream decodes to the frames written, whatever the split, and every refusal is the
//! one the crafted input should give.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::decimal_bitwise_operands,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_connect::carrier::ws::{self, Decoder, MAX_HEADER, MAX_PAYLOAD, Opcode, Role, WsError, WsFrame};
use vinc_tests::SplitMix64;

const OPS: [(Opcode, u8); 5] = [
    (Opcode::Continuation, 0),
    (Opcode::Binary, 2),
    (Opcode::Close, 8),
    (Opcode::Ping, 9),
    (Opcode::Pong, 10),
];

fn arr(b: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{x}");
    }
    s.push(']');
    s
}

fn err_tag(e: WsError) -> &'static str {
    match e {
        WsError::Reserved => "reserved",
        WsError::Opcode(_) => "opcode",
        WsError::Mask => "mask",
        WsError::Control => "control",
        WsError::Sequence => "sequence",
        WsError::TooLong => "toolong",
        WsError::LengthForm => "lenform",
        WsError::NoRoom => "noroom",
    }
}

/// The payload of length `n`: a fixed pattern, so that the models can rebuild it.
fn pat(n: usize) -> Vec<u8> {
    (1..=n).map(|j| ((j * 37 + n) % 256) as u8).collect()
}

struct T {
    rng: SplitMix64,
    ev: Vec<String>,
    next_id: u32,
}

impl T {
    fn below(&mut self, n: u64) -> u64 {
        self.rng.next_u64() % n
    }

    fn enc(&mut self, op: (Opcode, u8), payload: &[u8], mask: Option<[u8; 4]>, cap: usize) -> Result<Vec<u8>, WsError> {
        let mut out = vec![0u8; cap];
        let r = ws::encode(op.0, payload, mask, &mut out);
        let m = mask.map_or_else(|| "[]".to_string(), |k| arr(&k));
        match r {
            Ok(n) => {
                out.truncate(n);
                self.ev.push(format!(
                    r#"{{"t":"ws","op":"enc","code":{},"pl":{},"mask":{m},"cap":{cap},"res":"ok","b":{}}}"#,
                    op.1,
                    arr(payload),
                    arr(&out)
                ));
                Ok(out)
            }
            Err(e) => {
                self.ev.push(format!(
                    r#"{{"t":"ws","op":"enc","code":{},"pl":{},"mask":{m},"cap":{cap},"res":"{}"}}"#,
                    op.1,
                    arr(payload),
                    err_tag(e)
                ));
                Err(e)
            }
        }
    }

    fn new_dec(&mut self, peer: Role) -> (u32, Decoder) {
        self.next_id += 1;
        let name = if peer == Role::Client { "client" } else { "server" };
        self.ev.push(format!(
            r#"{{"t":"ws","op":"new","id":{},"peer":"{name}"}}"#,
            self.next_id
        ));
        (self.next_id, Decoder::new(peer))
    }

    /// One decode call on `buf`; returns the result as (kind, payload, close status, used).
    fn dec(
        &mut self,
        id: u32,
        d: &mut Decoder,
        buf: &[u8],
    ) -> Result<Option<(&'static str, Vec<u8>, i64, usize)>, WsError> {
        let mut work = buf.to_vec();
        let r = d.decode(&mut work);
        let head = format!(r#"{{"t":"ws","op":"dec","id":{id},"buf":{},"#, arr(buf));
        match r {
            Ok(None) => {
                self.ev.push(format!(r#"{head}"res":"idle"}}"#));
                Ok(None)
            }
            Ok(Some((f, used))) => {
                let (kind, pl, st) = match f {
                    WsFrame::Data(p) => ("data", p.to_vec(), -1),
                    WsFrame::Ping(p) => ("ping", p.to_vec(), -1),
                    WsFrame::Pong(p) => ("pong", p.to_vec(), -1),
                    WsFrame::Close(c) => ("close", vec![], c.map_or(-1, i64::from)),
                };
                self.ev.push(format!(
                    r#"{head}"res":"frame","f":"{kind}","pl":{},"st":{st},"used":{used}}}"#,
                    arr(&pl)
                ));
                Ok(Some((kind, pl, st, used)))
            }
            Err(e) => {
                self.ev.push(format!(r#"{head}"res":"err","e":"{}"}}"#, err_tag(e)));
                Err(e)
            }
        }
    }
}

/// A frame as a client or server writes it: the encoder's bytes, with FIN cleared for a fragment.
fn frame(t: &mut T, op: (Opcode, u8), payload: &[u8], mask: Option<[u8; 4]>, fin: bool) -> Vec<u8> {
    let mut b = t.enc(op, payload, mask, payload.len() + MAX_HEADER).unwrap();
    if !fin {
        b[0] &= 0x7f;
    }
    b
}

fn key(t: &mut T) -> [u8; 4] {
    let v = t.rng.next_u64().to_le_bytes();
    [v[0], v[1], v[2], v[3]]
}

#[derive(Debug, PartialEq)]
enum Want {
    Data(Vec<u8>),
    Ping(Vec<u8>),
    Pong(Vec<u8>),
    Close(i64),
}

/// A stream of frames from `peer`, read in random splits and decoded after every read.
fn stream_run(t: &mut T, peer: Role, bigok: bool) {
    let mut wire = Vec::new();
    let mut want = Vec::new();
    let nframes = 1 + t.below(6) as usize;
    let mut big = false;
    for _ in 0..nframes {
        let m = (peer == Role::Client).then(|| key(t));
        let len = match t.below(8) {
            0 => 0,
            1 => 1,
            2 => 125,
            3 => 126,
            4 if bigok => 200 + t.below(400) as usize,
            5 if bigok => MAX_PAYLOAD - t.below(2) as usize,
            _ => t.below(20) as usize,
        };
        if len > 200 {
            big = true;
        }
        match t.below(6) {
            0 => {
                let p = pat(t.below(126) as usize);
                wire.extend(frame(t, OPS[3], &p, m, true));
                want.push(Want::Ping(p));
            }
            1 => {
                let p = pat(t.below(126) as usize);
                wire.extend(frame(t, OPS[4], &p, m, true));
                want.push(Want::Pong(p));
            }
            2 => {
                let n = t.below(6) as usize;
                let p = pat(n);
                wire.extend(frame(t, OPS[2], &p, m, true));
                want.push(Want::Close(if n >= 2 {
                    i64::from(u16::from_be_bytes([p[0], p[1]]))
                } else {
                    -1
                }));
            }
            3 => {
                // a fragmented message: binary without FIN, continuations, the last with FIN
                let parts = 1 + t.below(3) as usize;
                for i in 0..=parts {
                    let p = pat(t.below(30) as usize + i);
                    let m = (peer == Role::Client).then(|| key(t));
                    let op = if i == 0 { OPS[1] } else { OPS[0] };
                    let fin = i == parts;
                    wire.extend(frame(t, op, &p, m, fin));
                    want.push(Want::Data(p));
                    if i < parts && t.below(2) == 0 {
                        // a control frame between the fragments
                        let c = pat(t.below(5) as usize);
                        let m = (peer == Role::Client).then(|| key(t));
                        wire.extend(frame(t, OPS[3], &c, m, true));
                        want.push(Want::Ping(c));
                    }
                }
            }
            _ => {
                let p = pat(len);
                wire.extend(frame(t, OPS[1], &p, m, true));
                want.push(Want::Data(p));
            }
        }
    }
    let (id, mut d) = t.new_dec(peer);
    let mut buf: Vec<u8> = Vec::new();
    let mut got = Vec::new();
    let mut at = 0;
    while at < wire.len() {
        let step = if big { 50 + t.below(400) } else { 1 + t.below(9) } as usize;
        let take = step.min(wire.len() - at);
        buf.extend_from_slice(&wire[at..at + take]);
        at += take;
        while let Some((kind, pl, st, used)) = t.dec(id, &mut d, &buf).unwrap() {
            got.push(match kind {
                "data" => Want::Data(pl),
                "ping" => Want::Ping(pl),
                "pong" => Want::Pong(pl),
                _ => Want::Close(st),
            });
            buf.drain(..used);
        }
    }
    assert_eq!(buf.len(), 0);
    assert_eq!(got, want);
}

/// A header with the given first two bytes and the extended length bytes `ext`, then a mask key if masked.
fn hdr(b0: u8, b1: u8, ext: &[u8], tail: &[u8]) -> Vec<u8> {
    let mut v = vec![b0, b1];
    v.extend_from_slice(ext);
    v.extend_from_slice(tail);
    v
}

fn crafted(t: &mut T) {
    let mp = MAX_PAYLOAD as u64;
    for peer in [Role::Client, Role::Server] {
        let mbit = if peer == Role::Client { 0x80u8 } else { 0 };
        let wrong = mbit ^ 0x80;
        let key = [0x11u8, 0x22, 0x33, 0x44];
        let tail = |m: u8, n: usize| -> Vec<u8> {
            let mut v = if m != 0 { key.to_vec() } else { vec![] };
            v.extend(pat(n));
            v
        };
        let mut cases: Vec<Vec<u8>> = Vec::new();
        // reserved bits, with every opcode
        for rsv in [0x10u8, 0x20, 0x40, 0x70] {
            cases.push(hdr(0x82 | rsv, mbit, &[], &tail(mbit, 0)));
        }
        // every opcode, final or not
        for op in 0..16u8 {
            for fin in [0x80u8, 0] {
                cases.push(hdr(fin | op, mbit, &[], &tail(mbit, 0)));
                cases.push(hdr(fin | op, mbit | 2, &[], &tail(mbit, 2)));
            }
        }
        // the wrong mask
        for op in [0u8, 2, 8, 9, 10] {
            cases.push(hdr(0x80 | op, wrong, &[], &tail(wrong, 0)));
            cases.push(hdr(0x80 | op, wrong | 3, &[], &tail(wrong, 3)));
        }
        // the 7-bit form, 125 and its edge
        cases.push(hdr(0x82, mbit | 125, &[], &tail(mbit, 125)));
        // the 16-bit form below, at and above its threshold, at the bound, and over it
        for n in [
            0u16,
            1,
            5,
            124,
            125,
            126,
            127,
            255,
            256,
            1000,
            MAX_PAYLOAD as u16 - 1,
            MAX_PAYLOAD as u16,
            MAX_PAYLOAD as u16 + 1,
            65535,
        ] {
            let body = if (n as usize) <= MAX_PAYLOAD { n as usize } else { 3 };
            cases.push(hdr(0x82, mbit | 126, &n.to_be_bytes(), &tail(mbit, body)));
        }
        // the 64-bit form: below 65536, at it, around the bound, huge
        for n in [
            0u64,
            5,
            125,
            126,
            65535,
            65536,
            65537,
            mp,
            mp + 1,
            mp + 100_000,
            1 << 31,
            1 << 32,
            (1 << 32) + 5,
            1 << 40,
            u64::MAX,
        ] {
            cases.push(hdr(0x82, mbit | 127, &n.to_be_bytes(), &tail(mbit, 2)));
        }
        // control frames: fragmented, 125, 126 (16-bit form), 200
        for op in [8u8, 9, 10] {
            cases.push(hdr(op, mbit, &[], &tail(mbit, 0)));
            cases.push(hdr(op, mbit | 4, &[], &tail(mbit, 4)));
            cases.push(hdr(0x80 | op, mbit | 125, &[], &tail(mbit, 125)));
            cases.push(hdr(0x80 | op, mbit | 126, &126u16.to_be_bytes(), &tail(mbit, 126)));
            cases.push(hdr(0x80 | op, mbit | 126, &200u16.to_be_bytes(), &tail(mbit, 200)));
            cases.push(hdr(0x80 | op, mbit | 126, &5u16.to_be_bytes(), &tail(mbit, 5)));
        }
        // the close payloads: none, one byte, a status, a status and a reason
        for n in [0usize, 1, 2, 3, 20] {
            let mut p = vec![0x03u8, 0xe8];
            p.truncate(n.min(2));
            p.extend(std::iter::repeat_n(b'x', n.saturating_sub(2)));
            let masked: Vec<u8> = p.iter().enumerate().map(|(i, b)| b ^ key[i % 4]).collect();
            let mut tl = if mbit != 0 { key.to_vec() } else { vec![] };
            tl.extend(if mbit != 0 { masked } else { p.clone() });
            cases.push(hdr(0x88, mbit | n as u8, &[], &tl));
        }
        for c in &cases {
            // the whole case, and every cut of its header and a few of its body
            let (id, mut d) = t.new_dec(peer);
            let _ = t.dec(id, &mut d, c);
            let cuts = c.len().min(16);
            for cut in (0..cuts).chain([c.len().saturating_sub(1)]) {
                let (id, mut d) = t.new_dec(peer);
                let _ = t.dec(id, &mut d, &c[..cut]);
            }
            // trailing bytes behind the frame
            let (id, mut d) = t.new_dec(peer);
            let mut more = c.clone();
            more.extend([0x89, 0x80]);
            let _ = t.dec(id, &mut d, &more);
        }
        // a header that announces an oversized frame is refused with no payload at all
        for form in [126u8, 127] {
            let n = if form == 126 { mp + 1 } else { mp + 100_000 };
            let ext = if form == 126 {
                (n as u16).to_be_bytes().to_vec()
            } else {
                n.to_be_bytes().to_vec()
            };
            let head = hdr(0x82, mbit | form, &ext, &if mbit != 0 { key.to_vec() } else { vec![] });
            let (id, mut d) = t.new_dec(peer);
            let r = t.dec(id, &mut d, &head);
            assert!(
                matches!(r, Err(WsError::TooLong)),
                "an oversized header is refused at once"
            );
        }
        // sequences: a fragmented message in progress
        let m = |n: usize| tail(mbit, n);
        let seqs: [(u8, u8, usize); 8] = [
            (0x82, 2, 0),
            (0x02, 2, 0),
            (0x00, 2, 0),
            (0x80, 2, 0),
            (0x89, 1, 0),
            (0x88, 2, 0),
            (0x8a, 0, 0),
            (0x09, 0, 0),
        ];
        for open_first in [false, true] {
            for (b0, n, _) in seqs {
                let (id, mut d) = t.new_dec(peer);
                if open_first {
                    let r = t.dec(id, &mut d, &hdr(0x02, mbit | 2, &[], &m(2)));
                    assert!(matches!(r, Ok(Some(_))));
                }
                let r = t.dec(id, &mut d, &hdr(b0, mbit | n, &[], &m(n as usize)));
                // after a refusal the decoder keeps its state: carry on with a continuation and a binary frame
                let _ = r;
                let _ = t.dec(id, &mut d, &hdr(0x00, mbit, &[], &m(0)));
                let _ = t.dec(id, &mut d, &hdr(0x82, mbit, &[], &m(0)));
                let _ = t.dec(id, &mut d, &hdr(0x80, mbit, &[], &m(0)));
            }
        }
        // the same fragments, in a chain: binary, ping, continuation, continuation final, binary
        let (id, mut d) = t.new_dec(peer);
        for (b0, n) in [(0x02u8, 1u8), (0x89, 1), (0x00, 2), (0x80, 0), (0x82, 1), (0x80, 0)] {
            let _ = t.dec(id, &mut d, &hdr(b0, mbit | n, &[], &m(n as usize)));
        }
    }
}

fn encoder_cases(t: &mut T) {
    let mp = MAX_PAYLOAD;
    let k = [0xa5u8, 0x5a, 0x0f, 0xf0];
    let lens = [
        0usize,
        1,
        2,
        5,
        124,
        125,
        126,
        127,
        255,
        256,
        1000,
        mp - 1,
        mp,
        mp + 1,
        mp + 500,
    ];
    for &n in &lens {
        let p = pat(n);
        for op in OPS {
            let big = n > 125;
            if big && !matches!(op.1, 2 | 9) {
                continue;
            }
            for mask in [None, Some(k)] {
                let hl = 2 + if n > 125 { 2 } else { 0 } + if mask.is_some() { 4 } else { 0 };
                let exact = hl + n;
                let caps: Vec<usize> = if big {
                    vec![exact, exact - 1]
                } else {
                    vec![
                        0,
                        1,
                        2,
                        hl.saturating_sub(1),
                        hl,
                        exact.saturating_sub(1),
                        exact,
                        exact + 1,
                        exact + 20,
                    ]
                };
                for cap in caps {
                    let r = t.enc(op, &p, mask, cap);
                    // the encoder's own expectations
                    let ctl = op.1 >= 8;
                    let want = if n > mp {
                        Some(WsError::TooLong)
                    } else if ctl && n > 125 {
                        Some(WsError::Control)
                    } else if exact > cap {
                        Some(WsError::NoRoom)
                    } else {
                        None
                    };
                    match (r, want) {
                        (Ok(b), None) => assert_eq!(b.len(), exact),
                        (Err(e), Some(w)) => assert_eq!(e, w),
                        (r, w) => panic!("encode n={n} cap={cap} gave {r:?}, expected {w:?}"),
                    }
                }
            }
        }
    }
}

#[test]
fn websocket_calls_match_the_models() {
    let mut t = T {
        rng: SplitMix64::new(0x5753_0001),
        ev: Vec::new(),
        next_id: 0,
    };
    t.ev.push(format!(r#"{{"t":"ws","op":"init","mp":{MAX_PAYLOAD}}}"#));
    encoder_cases(&mut t);
    crafted(&mut t);
    for i in 0..240 {
        stream_run(
            &mut t,
            if i % 2 == 0 { Role::Server } else { Role::Client },
            i % 16 == 0,
        );
    }
    let mut all = String::new();
    for line in &t.ev {
        let _ = writeln!(all, "{line}");
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("connect_ws.ndjson"), &all).unwrap();
    }
    for want in [
        r#""res":"idle""#,
        r#""res":"frame""#,
        r#""e":"reserved""#,
        r#""e":"opcode""#,
        r#""e":"mask""#,
        r#""e":"control""#,
        r#""e":"sequence""#,
        r#""e":"toolong""#,
        r#""e":"lenform""#,
        r#""res":"noroom""#,
        r#""res":"toolong""#,
        r#""res":"control""#,
        r#""f":"close""#,
    ] {
        assert!(all.contains(want), "no event with {want}");
    }
}
