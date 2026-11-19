//! Trace generation for which hosts the port-mapping client trusts (`pinc_portmap::addr`): the real `is_shared`,
//! `is_private`, `usable_host` and `external_ok`, recorded as ndjson (`portmap/addr.ndjson` under `PINC_TRACE_DIR`) for
//! the TLA+ trace check (`TracePortMapAddr.tla`).
//!
//! One event is written per address: an IPv4 address with what the three IPv4 functions and `external_ok` return, or an
//! IPv6 address (IPv4-mapped ones included) as its eight 16-bit segments with what `external_ok` returns. The addresses
//! are the boundary set of `PortMapAddr.tla` (every IPv4 address over the octets on both sides of each range edge, each
//! also IPv4-mapped, and the IPv6 first segments around fc00::/7, fe80::/10 and ff00::/8 with every tail) and 8192
//! seeded random ones. Every answer is also checked here against the documented rule written out as prefix tests, so
//! the test is meaningful without the proof tools. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::fn_params_excessive_bools,
    unreachable_pub,
    clippy::doc_markdown,
    clippy::items_after_statements,
    clippy::many_single_char_names
)]

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use pinc_portmap::addr::{external_ok, is_private, is_shared, usable_host};
use pinc_tests::SplitMix64;

/// 100.64.0.0/10, as a prefix test.
fn shared_rule(o: [u8; 4]) -> bool {
    o[0] == 100 && (64..=127).contains(&o[1])
}

/// 10/8, 172.16/12, 192.168/16 or the shared range.
fn private_rule(o: [u8; 4]) -> bool {
    o[0] == 10 || (o[0] == 172 && (16..=31).contains(&o[1])) || (o[0] == 192 && o[1] == 168) || shared_rule(o)
}

/// Not 0.0.0.0, 127/8, 224/4, 255.255.255.255 or 169.254/16.
fn host_rule(o: [u8; 4]) -> bool {
    !(o == [0; 4] || o[0] == 127 || (224..=239).contains(&o[0]) || o == [255; 4] || (o[0] == 169 && o[1] == 254))
}

/// The external rule for an IPv6 address, an IPv4-mapped one judged as the IPv4 it maps.
fn external_rule_v6(s: [u16; 8]) -> bool {
    if s[..5] == [0; 5] && s[5] == 0xffff {
        let [a, b] = s[6].to_be_bytes();
        let [c, d] = s[7].to_be_bytes();
        let o = [a, b, c, d];
        return host_rule(o) && !private_rule(o);
    }
    !(s == [0; 8]
        || s == [0, 0, 0, 0, 0, 0, 0, 1]
        || s[0] >> 8 == 0xff
        || s[0] & 0xffc0 == 0xfe80
        || s[0] & 0xfe00 == 0xfc00)
}

/// One IPv4 event; the answers are checked against the rules.
fn v4(out: &mut String, o: [u8; 4]) {
    let ip = Ipv4Addr::from(o);
    let (sh, pr, uh, ex) = (
        is_shared(ip),
        is_private(ip),
        usable_host(ip),
        external_ok(IpAddr::V4(ip)),
    );
    assert_eq!(sh, shared_rule(o), "is_shared of {ip}");
    assert_eq!(pr, private_rule(o), "is_private of {ip}");
    assert_eq!(uh, host_rule(o), "usable_host of {ip}");
    assert_eq!(ex, host_rule(o) && !private_rule(o), "external_ok of {ip}");
    assert_eq!(
        external_ok(IpAddr::V6(ip.to_ipv6_mapped())),
        ex,
        "external_ok of the mapped form of {ip}"
    );
    let _ = writeln!(
        out,
        r#"{{"v":4,"o":[{},{},{},{}],"sh":{sh},"pr":{pr},"uh":{uh},"ex":{ex}}}"#,
        o[0], o[1], o[2], o[3]
    );
}

/// One IPv6 event.
fn v6(out: &mut String, s: [u16; 8]) {
    let ip = Ipv6Addr::from(s);
    let ex = external_ok(IpAddr::V6(ip));
    assert_eq!(ex, external_rule_v6(s), "external_ok of {ip}");
    let _ = writeln!(
        out,
        r#"{{"v":6,"s":[{},{},{},{},{},{},{},{}],"ex":{ex}}}"#,
        s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]
    );
}

#[test]
fn the_address_rules_match_the_models() {
    let mut out = String::new();

    // the boundary set of PortMapAddr.tla
    const A: [u8; 27] = [
        0, 1, 9, 10, 11, 99, 100, 101, 126, 127, 128, 168, 169, 170, 171, 172, 173, 191, 192, 193, 223, 224, 225, 239,
        240, 254, 255,
    ];
    const B: [u8; 15] = [0, 15, 16, 31, 32, 63, 64, 127, 128, 167, 168, 169, 253, 254, 255];
    const C: [u8; 2] = [0, 255];
    const D: [u8; 3] = [0, 1, 255];
    let mut octets = Vec::new();
    for a in A {
        for b in B {
            for c in C {
                for d in D {
                    octets.push([a, b, c, d]);
                }
            }
        }
    }
    assert_eq!(octets.len(), 2430);
    for o in &octets {
        v4(&mut out, *o);
    }
    for o in &octets {
        let s = Ipv4Addr::from(*o).to_ipv6_mapped().segments();
        v6(&mut out, s);
    }
    const HEADS: [u16; 14] = [
        0x0000, 0x0001, 0x2001, 0xfbff, 0xfc00, 0xfdff, 0xfe00, 0xfe7f, 0xfe80, 0xfebf, 0xfec0, 0xfeff, 0xff00, 0xffff,
    ];
    const TAILS: [[u16; 7]; 5] = [
        [0; 7],
        [0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0xffff, 0, 0],
        [0xffff; 7],
        [0, 0, 0, 0, 0, 0x0a00, 1],
    ];
    for h in HEADS {
        for t in TAILS {
            v6(&mut out, [h, t[0], t[1], t[2], t[3], t[4], t[5], t[6]]);
        }
    }
    assert_eq!(out.lines().count(), 2430 * 2 + 70);

    // seeded random addresses
    let mut rng = SplitMix64::traced(0x5eed_add0);
    for _ in 0..4096 {
        v4(&mut out, (rng.next_u64() as u32).to_be_bytes());
    }
    for i in 0..4096u32 {
        let (x, y) = (rng.next_u64(), rng.next_u64());
        let mut s = [0u16; 8];
        for (k, seg) in s.iter_mut().enumerate() {
            let w = if k < 4 { x } else { y };
            *seg = (w >> (16 * (k % 4))) as u16;
        }
        match i % 4 {
            0 => {
                s[..5].fill(0);
                s[5] = 0xffff;
            }
            1 => s[0] = 0xfc00 + (s[0] & 0x3ff),
            _ => {}
        }
        v6(&mut out, s);
    }

    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        let dir = std::path::PathBuf::from(dir).join("portmap");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("addr.ndjson"), out).unwrap();
    }
}
