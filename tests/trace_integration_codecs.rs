//! Trace generation for the small round trips of the integration layer: the relay path addresses
//! (`vinc_core::relay_addr`, `relay_parts`), the stream tag (`vinc::write_tag`, `read_tag`, driven over a real
//! loopback connection) and the stream id at the head of a range-proof body (`vinc-node`'s `head_sid`, `with_sid`, through
//! the `trace` view). Recorded as ndjson (`codecs_relay.ndjson`, `codecs_tag.ndjson`, `codecs_sid.ndjson`) for the TLA+
//! trace check (`TraceIntegrationCodecs.tla`) and the Lean replay (`Vinc/TraceIntegrationCodecs.lean`).
//!
//! Every event is one call of the real code on boundary, mutated and seeded random inputs: the arguments and the
//! result. The test asserts what each codec must satisfy on its own (a decoded value re-encodes to its input, a refusal
//! changes nothing). The trace is written to `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
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
    clippy::type_complexity,
    clippy::single_match_else,
    clippy::manual_is_multiple_of,
    clippy::format_push_string,
    clippy::assert_is_empty,
    unreachable_pub
)]

#[macro_use]
mod vinc_common;

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use vinc::{ErrorKind, read_tag, write_tag};
use vinc_common::{ECHO, bind, within};
use vinc_core::{is_relay_addr, relay_addr, relay_parts};
use vinc_node::values_frames_probe as frames;
use vinc_tests::SplitMix64;

fn arr(b: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn write_out(name: &str, out: &str) {
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join(name), out).unwrap();
    }
}

// ---- relay path addresses ----

/// The octets or segments of an address, as the JSON array of the event.
fn segs(a: &SocketAddr) -> (bool, Vec<u32>) {
    match a.ip() {
        IpAddr::V4(ip) => (false, ip.octets().iter().map(|&o| u32::from(o)).collect()),
        IpAddr::V6(ip) => (true, ip.segments().iter().map(|&o| u32::from(o)).collect()),
    }
}

fn from_segs(v6: bool, s: &[u32], port: u16) -> SocketAddr {
    if v6 {
        let g: Vec<u16> = s.iter().map(|&x| x as u16).collect();
        SocketAddr::new(
            IpAddr::V6(Ipv6Addr::new(g[0], g[1], g[2], g[3], g[4], g[5], g[6], g[7])),
            port,
        )
    } else {
        SocketAddr::new(
            IpAddr::V4(Ipv4Addr::new(s[0] as u8, s[1] as u8, s[2] as u8, s[3] as u8)),
            port,
        )
    }
}

fn nums(s: &[u32]) -> String {
    let v: Vec<String> = s.iter().map(ToString::to_string).collect();
    format!("[{}]", v.join(","))
}

#[derive(Default)]
struct Relay {
    out: String,
    built: usize,
    read_some: usize,
    read_none: usize,
}

impl Relay {
    fn build(&mut self, v6: bool, relay: u8, peer: u16) {
        let a = relay_addr(v6, relay, peer);
        let (f, s) = segs(&a);
        assert_eq!(f, v6);
        assert_eq!(a.port(), 0, "the port of a relay path address is not used");
        assert_eq!(relay_parts(&a), Some((relay, peer)), "relay_parts inverts relay_addr");
        assert!(is_relay_addr(&a));
        writeln!(
            self.out,
            "{{\"t\":\"raddr\",\"v6\":{v6},\"relay\":{relay},\"peer\":{peer},\"s\":{},\"port\":{}}}",
            nums(&s),
            a.port()
        )
        .unwrap();
        self.built += 1;
    }

    fn parts(&mut self, v6: bool, s: &[u32], port: u16) {
        let a = from_segs(v6, s, port);
        let r = relay_parts(&a);
        assert_eq!(is_relay_addr(&a), r.is_some());
        match r {
            Some((relay, peer)) => {
                // What relay_parts finds, relay_addr writes back as the same IP, at port 0.
                let back = relay_addr(v6, relay, peer);
                assert_eq!(back.ip(), a.ip());
                assert_eq!(back.port(), 0);
                self.read_some += 1;
                writeln!(
                    self.out,
                    "{{\"t\":\"rparts\",\"v6\":{v6},\"s\":{},\"port\":{port},\"some\":true,\"relay\":{relay},\"peer\":{peer}}}",
                    nums(s)
                )
                .unwrap();
            }
            None => {
                self.read_none += 1;
                writeln!(
                    self.out,
                    "{{\"t\":\"rparts\",\"v6\":{v6},\"s\":{},\"port\":{port},\"some\":false}}",
                    nums(s)
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn relay_paths() {
    let mut rng = SplitMix64::new(0x7e1a_4001);
    let mut t = Relay::default();
    let relays: [u8; 7] = [0, 1, 127, 128, 239, 240, 255];
    let peers: [u16; 9] = [0, 1, 255, 256, 257, 0x1234, 0xff00, 0xfffe, 0xffff];
    for v6 in [false, true] {
        for &r in &relays {
            for &p in &peers {
                t.build(v6, r, p);
            }
        }
        for _ in 0..300 {
            t.build(v6, rng.next_u64() as u8, rng.next_u64() as u16);
        }
    }
    // Reading: every built address at several ports, and every single-field change of one.
    let ports = [0u16, 1, 4433, 65535];
    let alt4: [u32; 7] = [0, 1, 127, 239, 240, 241, 255];
    let alt6: [u32; 13] = [
        0, 1, 0x42, 0x43, 0x44, 0xff, 0x100, 0x101, 0x494d, 0x494e, 0xfd55, 0xfd56, 0xffff,
    ];
    for v6 in [false, true] {
        for &r in &[0u8, 7, 255] {
            for &p in &[0u16, 513, 0xffff] {
                let (_, s) = segs(&relay_addr(v6, r, p));
                for &port in &ports {
                    t.parts(v6, &s, port);
                }
                for i in 0..s.len() {
                    for &x in if v6 { &alt6[..] } else { &alt4[..] } {
                        let mut m = s.clone();
                        m[i] = x;
                        t.parts(v6, &m, 0);
                    }
                }
            }
        }
    }
    // Random addresses: a few with the right prefix and random tails, most arbitrary.
    for _ in 0..1500 {
        let v6 = rng.next_u64() & 1 == 1;
        let n = if v6 { 8 } else { 4 };
        let mut s: Vec<u32> = (0..n)
            .map(|_| {
                if v6 {
                    (rng.next_u64() & 0xffff) as u32
                } else {
                    (rng.next_u64() & 0xff) as u32
                }
            })
            .collect();
        if rng.next_u64() % 3 != 0 {
            if v6 {
                s[0] = 0xfd56;
                s[1] = 0x494e;
                s[2] = 0x43;
                s[3] = 0;
                s[4] = 0;
                if rng.next_u64() % 2 == 0 {
                    s[6] = 0;
                }
                if rng.next_u64() % 2 == 0 {
                    s[5] &= 0x1ff;
                }
            } else {
                s[0] = 240;
            }
        }
        t.parts(v6, &s, (rng.next_u64() & 0xffff) as u16);
    }
    assert!(
        t.built > 700 && t.read_some > 100 && t.read_none > 300,
        "{} {} {}",
        t.built,
        t.read_some,
        t.read_none
    );
    write_out("codecs_relay.ndjson", &t.out);
}

// ---- the stream id at the head of a range-proof body ----

fn varint(v: u64) -> Vec<u8> {
    let mut b = [0u8; 9];
    let n = vinc_wire::varint::encode(v, &mut b).unwrap();
    b[..n].to_vec()
}

#[derive(Default)]
struct Sid {
    out: String,
    heads: usize,
    ok: usize,
    refused: usize,
    full: usize,
}

impl Sid {
    fn head(&mut self, body: &[u8]) {
        let r = frames::head(body);
        self.heads += 1;
        match r {
            Some(v) => {
                // The head is the one canonical encoding of what it reads.
                assert_eq!(body[..varint(v).len()], varint(v)[..]);
                writeln!(
                    self.out,
                    "{{\"t\":\"hsid\",\"b\":{},\"ok\":true,\"sid\":{}}}",
                    arr(body),
                    limbs(v)
                )
                .unwrap();
            }
            None => {
                writeln!(self.out, "{{\"t\":\"hsid\",\"b\":{},\"ok\":false}}", arr(body)).unwrap();
            }
        }
    }

    fn with(&mut self, body: &[u8], sid: u64) {
        let r = frames::with(body, sid);
        match r {
            Some(out) => {
                assert!(out.len() <= frames::BUF);
                assert_eq!(frames::head(&out), Some(sid));
                let used = varint(frames::head(body).unwrap()).len();
                assert_eq!(out[varint(sid).len()..], body[used..], "the rest is copied unchanged");
                self.ok += 1;
                if out.len() == frames::BUF {
                    self.full += 1;
                }
                writeln!(
                    self.out,
                    "{{\"t\":\"wsid\",\"b\":{},\"sid\":{},\"ok\":true,\"out\":{}}}",
                    arr(body),
                    limbs(sid),
                    arr(&out)
                )
                .unwrap();
            }
            None => {
                self.refused += 1;
                writeln!(
                    self.out,
                    "{{\"t\":\"wsid\",\"b\":{},\"sid\":{},\"ok\":false}}",
                    arr(body),
                    limbs(sid)
                )
                .unwrap();
            }
        }
    }
}

#[test]
fn stream_id_heads() {
    let mut rng = SplitMix64::new(0x51d_0001);
    let mut t = Sid::default();
    // The ids: the edges of every varint width, 2^63 and the largest u64.
    let mut ids: Vec<u64> = vec![0, 1, 2, 127, 128, 129];
    for k in [14u32, 21, 28, 35, 42, 49, 56, 62] {
        let p = 1u64 << k;
        ids.extend([p - 1, p, p + 1]);
    }
    ids.extend([(1u64 << 63) - 1, 1 << 63, (1 << 63) + 1, u64::MAX]);
    for _ in 0..8 {
        ids.push(rng.next_u64() >> (rng.next_u64() % 64));
    }
    let rest_of = |rng: &mut SplitMix64, n: usize| -> Vec<u8> { (0..n).map(|_| rng.next_u64() as u8).collect() };
    // Valid heads with rests, and every new id.
    for &old in ids.iter().filter(|&&v| v < 1 << 63) {
        for &sid in &ids {
            for n in [0usize, 1, 20] {
                let mut body = varint(old);
                body.extend(rest_of(&mut rng, n));
                t.with(&body, sid);
            }
        }
        for n in [0usize, 5, 300] {
            let mut body = varint(old);
            body.extend(rest_of(&mut rng, n));
            t.head(&body);
        }
    }
    // The buffer boundary: the rest that fills it exactly, one more, and one less, for ids of every width.
    for &sid in ids.iter().filter(|&&v| v < 1 << 63) {
        let head = varint(sid).len();
        for old in [1u64, 1 << 20, 1 << 62] {
            for n in [frames::BUF - head - 1, frames::BUF - head, frames::BUF - head + 1] {
                let mut body = varint(old);
                body.extend(rest_of(&mut rng, n));
                t.with(&body, sid);
            }
        }
    }
    // Heads that are not varints: empty, short, too long, not minimal, and random garbage.
    let junk: Vec<Vec<u8>> = vec![
        vec![],
        vec![0x80],
        vec![0xff; 8],
        vec![0xff; 9],
        vec![0xff; 12],
        vec![0x80, 0x00],
        vec![0x81, 0x00],
        vec![0xff, 0xff, 0x00],
        vec![0x80; 9],
        vec![0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00],
        vec![0x00, 0x00],
        vec![0x7f, 0x80],
    ];
    for b in junk {
        t.head(&b);
        for &sid in &[0u64, 5, 1 << 40] {
            t.with(&b, sid);
        }
    }
    for _ in 0..600 {
        let n = (rng.next_u64() % 14) as usize;
        let b: Vec<u8> = (0..n)
            .map(|_| {
                let x = rng.next_u64() as u8;
                if rng.next_u64() % 2 == 0 { x | 0x80 } else { x }
            })
            .collect();
        t.head(&b);
        t.with(&b, rng.next_u64() >> (rng.next_u64() % 64));
    }
    assert!(
        t.ok > 500 && t.refused > 100 && t.full >= 3 && t.heads > 300,
        "{} {} {} {}",
        t.ok,
        t.refused,
        t.full,
        t.heads
    );
    write_out("codecs_sid.ndjson", &t.out);
}

// ---- the stream tag ----

#[nuclei::test]
async fn stream_tags() {
    let server = bind(vinc_common::builder().alpn(ECHO)).await;
    let client = bind(vinc_common::builder().alpn(ECHO)).await;
    let mut out = String::new();
    let (mut ok_n, mut cfg_n, mut eof_n, mut wcfg_n) = (0usize, 0usize, 0usize, 0usize);
    within(300, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        // The session reaches the server's queue once the client opened a stream.
        let (mut tx, _rx) = c.open_bi().await.unwrap();
        tx.write_all(b"hi").await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        let (_stx, mut srx) = s.accept_bi().await.unwrap();
        let mut two = [0u8; 2];
        srx.read_exact(&mut two).await.unwrap();

        let mut rng = SplitMix64::new(0x7a6_0001);
        // Writing: tags of every length from 0 to 70, each through the real write_tag onto a real stream.
        for n in 0..=70usize {
            let tag: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
            let (mut tx, _rx) = c.open_bi().await.unwrap();
            match write_tag(&mut tx, &tag).await {
                Ok(()) => {
                    assert!((1..=64).contains(&n));
                    tx.finish().await.unwrap();
                    let (_stx, mut rx) = s.accept_bi().await.unwrap();
                    let got = rx.read_to_end(4096).await.unwrap();
                    assert_eq!(got.len(), n + 1);
                    ok_n += 1;
                    out.push_str(&format!(
                        "{{\"t\":\"wtag\",\"tag\":{},\"ok\":true,\"b\":{}}}\n",
                        arr(&tag),
                        arr(&got)
                    ));
                    // Reading what was written gives the tag back.
                    let (mut tx2, _rx2) = c.open_bi().await.unwrap();
                    tx2.write_all(&got).await.unwrap();
                    tx2.write_all(b"after").await.unwrap();
                    tx2.finish().await.unwrap();
                    let (_stx2, mut rx2) = s.accept_bi().await.unwrap();
                    assert_eq!(read_tag(&mut rx2).await.unwrap(), tag);
                    assert_eq!(rx2.read_to_end(64).await.unwrap(), b"after");
                }
                Err(e) => {
                    assert!(n == 0 || n > 64);
                    assert_eq!(e.kind(), ErrorKind::Config);
                    wcfg_n += 1;
                    out.push_str(&format!(
                        "{{\"t\":\"wtag\",\"tag\":{},\"err\":\"config\"}}\n",
                        arr(&tag)
                    ));
                    // Nothing was written: the stream is empty.
                    tx.finish().await.unwrap();
                    let (_stx, mut rx) = s.accept_bi().await.unwrap();
                    assert!(rx.read_to_end(64).await.unwrap().is_empty());
                }
            }
        }
        // Reading: byte strings behind a stream that then ends.
        let mut inputs: Vec<Vec<u8>> = Vec::new();
        for n in [0u8, 1, 2, 3, 31, 32, 63, 64, 65, 66, 100, 127, 128, 200, 255] {
            for k in [0usize, 1, 2, 30, 63, 64, 65, 66, 255] {
                let k = if k == 0 {
                    0
                } else {
                    (n as usize).saturating_add(k).min(300) - 1
                };
                let mut b = vec![n];
                b.extend((0..k).map(|_| rng.next_u64() as u8));
                inputs.push(b);
            }
            for k in [
                0usize,
                1,
                n as usize / 2,
                (n as usize).saturating_sub(1),
                n as usize,
                n as usize + 1,
                n as usize + 7,
            ] {
                let mut b = vec![n];
                b.extend((0..k).map(|_| rng.next_u64() as u8));
                inputs.push(b);
            }
        }
        for _ in 0..150 {
            let n = (rng.next_u64() % 70) as usize;
            inputs.push((0..n).map(|_| rng.next_u64() as u8).collect());
        }
        // Valid encodings with every cut and a changed length byte.
        for n in [1usize, 2, 5, 64] {
            let tag: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
            let mut b = vec![n as u8];
            b.extend(&tag);
            for cut in 0..b.len() {
                inputs.push(b[..cut].to_vec());
            }
            for d in [1u8, 255] {
                let mut m = b.clone();
                m[0] = m[0].wrapping_add(d);
                inputs.push(m);
            }
            let mut tail = b.clone();
            tail.extend(b"xyz");
            inputs.push(tail);
        }
        for b in inputs {
            let (mut tx, _rx) = c.open_bi().await.unwrap();
            if !b.is_empty() {
                tx.write_all(&b).await.unwrap();
            }
            tx.finish().await.unwrap();
            let (_stx, mut rx) = s.accept_bi().await.unwrap();
            match read_tag(&mut rx).await {
                Ok(tag) => {
                    let rest = rx.read_to_end(4096).await.unwrap();
                    assert_eq!(b.len(), 1 + tag.len() + rest.len(), "exactly the tag is consumed");
                    assert_eq!(b[1..=tag.len()], tag[..]);
                    ok_n += 1;
                    out.push_str(&format!(
                        "{{\"t\":\"rtag\",\"b\":{},\"ok\":true,\"tag\":{},\"rest\":{}}}\n",
                        arr(&b),
                        arr(&tag),
                        arr(&rest)
                    ));
                }
                Err(e) if e.kind() == ErrorKind::Config => {
                    // Only the length byte was read: the rest of the stream is still there.
                    let rest = rx.read_to_end(4096).await.unwrap();
                    assert_eq!(rest, b[1..], "a refused length byte leaves the stream unread");
                    cfg_n += 1;
                    out.push_str(&format!(
                        "{{\"t\":\"rtag\",\"b\":{},\"err\":\"config\",\"rest\":{}}}\n",
                        arr(&b),
                        arr(&rest)
                    ));
                }
                Err(_) => {
                    eof_n += 1;
                    out.push_str(&format!("{{\"t\":\"rtag\",\"b\":{},\"err\":\"eof\"}}\n", arr(&b)));
                }
            }
        }
    })
    .await;
    assert!(
        ok_n > 120 && cfg_n > 60 && eof_n > 60 && wcfg_n == 7,
        "{ok_n} {cfg_n} {eof_n} {wcfg_n}"
    );
    write_out("codecs_tag.ndjson", &out);
}
