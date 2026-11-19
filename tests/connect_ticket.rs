//! Tickets: the binary form, the base32 text form and refusals.
#![allow(
    clippy::doc_markdown,
    clippy::unnested_or_patterns,
    clippy::nonminimal_bool,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::many_single_char_names
)]

mod connect_common;

use std::net::SocketAddr;

use connect_common::nid;
use pinc_connect::ticket::{MAX_LEN, MAX_TEXT, Ticket, TicketError, VERSION};
use pinc_crypto::{IdentityAlg, NodeId};
use proptest::prelude::*;

fn node(tag: u8, alg: IdentityAlg) -> NodeId {
    NodeId { alg, bytes: [tag; 32] }
}

fn full() -> Ticket {
    let mut t = Ticket::new(nid(1)).with_home(nid(2));
    for a in ["198.51.100.7:4433", "[2001:db8::1]:443", "10.0.0.1:1", "[fe80::1]:9"] {
        t = t.with_addr(a.parse::<SocketAddr>().unwrap()).unwrap();
    }
    t
}

#[test]
fn a_bare_ticket_is_the_version_the_flags_and_the_node() {
    let t = Ticket::new(nid(7));
    let mut b = [0u8; MAX_LEN];
    let n = t.encode(&mut b).unwrap();
    assert_eq!(n, 2 + 33);
    assert_eq!(b[0], VERSION);
    assert_eq!(b[1], 0);
    assert_eq!(Ticket::parse(&b[..n]), Ok(t));
}

#[test]
fn a_full_ticket_round_trips_in_binary_and_text() {
    let t = full();
    let mut b = [0u8; MAX_LEN];
    let n = t.encode(&mut b).unwrap();
    assert!(n <= MAX_LEN);
    assert_eq!(Ticket::parse(&b[..n]), Ok(t));
    let mut txt = [0u8; MAX_TEXT];
    let m = t.to_text(&mut txt).unwrap();
    assert!(
        txt[..m]
            .iter()
            .all(|c| c.is_ascii_lowercase() || (b'2'..=b'7').contains(c))
    );
    assert_eq!(Ticket::from_text(&txt[..m]), Ok(t));
    let upper = txt[..m].to_ascii_uppercase();
    assert_eq!(Ticket::from_text(&upper), Ok(t), "either case reads");
}

#[test]
fn the_text_form_matches_a_known_base32_vector() {
    let t = Ticket::new(nid(0));
    let mut txt = [0u8; MAX_TEXT];
    let m = t.to_text(&mut txt).unwrap();
    // 35 bytes: version 1, flags 0, tag 1 (Ed25519 is tag 1? the tag is whatever the id writes), 32 zero bytes
    let mut b = [0u8; MAX_LEN];
    let n = t.encode(&mut b).unwrap();
    let want = base32(&b[..n]);
    assert_eq!(&txt[..m], want.as_bytes());
}

fn base32(b: &[u8]) -> String {
    const A: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";
    let mut out = String::new();
    let (mut acc, mut bits) = (0u32, 0u32);
    for &x in b {
        acc = acc << 8 | u32::from(x);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(A[(acc >> bits & 31) as usize] as char);
        }
    }
    if bits > 0 {
        out.push(A[(acc << (5 - bits) & 31) as usize] as char);
    }
    out
}

#[test]
fn every_identity_algorithm_has_a_ticket() {
    for alg in [
        IdentityAlg::Ed25519,
        IdentityAlg::EcdsaP256,
        IdentityAlg::MlDsa65,
        IdentityAlg::Hybrid,
    ] {
        let t = Ticket::new(node(3, alg));
        let mut b = [0u8; MAX_LEN];
        let n = t.encode(&mut b).unwrap();
        assert_eq!(Ticket::parse(&b[..n]), Ok(t));
    }
}

#[test]
fn malformed_tickets_are_refused() {
    let mut b = [0u8; MAX_LEN];
    let n = full().encode(&mut b).unwrap();
    let ok = b[..n].to_vec();
    let mut bad = ok.clone();
    bad[0] = 2;
    assert_eq!(Ticket::parse(&bad), Err(TicketError::Version(2)));
    let mut bad = ok.clone();
    bad[1] |= 0x80;
    assert!(matches!(Ticket::parse(&bad), Err(TicketError::Flags(_))));
    let mut bad = ok.clone();
    bad[1] = 1 | (5 << 1);
    assert!(
        matches!(Ticket::parse(&bad), Err(TicketError::Flags(_))),
        "five addresses"
    );
    let mut bad = ok.clone();
    bad.push(0);
    assert!(matches!(Ticket::parse(&bad), Err(TicketError::Wire(_))));
    for cut in 0..ok.len() {
        assert!(Ticket::parse(&ok[..cut]).is_err(), "cut at {cut}");
    }
    assert!(matches!(
        full().with_addr("1.1.1.1:1".parse().unwrap()),
        Err(TicketError::TooManyAddrs)
    ));
    assert_eq!(Ticket::from_text(b"abc!"), Err(TicketError::Text));
    assert_eq!(
        Ticket::from_text(b"a"),
        Err(TicketError::Text),
        "a lone symbol holds no whole byte and leaves bits"
    );
    let mut small = [0u8; 4];
    assert!(full().encode(&mut small).is_err());
    assert!(full().to_text(&mut small).is_err());
}

#[test]
fn non_zero_padding_bits_are_refused() {
    let t = Ticket::new(nid(9));
    let mut txt = [0u8; MAX_TEXT];
    let m = t.to_text(&mut txt).unwrap();
    // flip the last symbol so a padding bit is set
    let last = txt[m - 1];
    let alt = if last == b'a' { b'b' } else { b'a' };
    txt[m - 1] = alt;
    if Ticket::from_text(&txt[..m]).is_ok() {
        // only if the changed symbol differs in data bits, in which case the node differs
        assert_ne!(Ticket::from_text(&txt[..m]).unwrap(), t);
    }
}

proptest! {
    #[test]
    fn round_trip_any_ticket(tag in any::<u8>(), home in proptest::option::of(any::<u8>()), n in 0usize..=4, port in any::<u16>(), v6 in any::<bool>()) {
        let mut t = Ticket::new(nid(tag));
        if let Some(h) = home { t = t.with_home(nid(h)); }
        for i in 0..n {
            let a: SocketAddr = if v6 { SocketAddr::from(([i as u16, 2, 3, 4, 5, 6, 7, 8], port)) } else { SocketAddr::from(([i as u8, 2, 3, 4], port)) };
            t = t.with_addr(a).unwrap();
        }
        let mut b = [0u8; MAX_LEN];
        let len = t.encode(&mut b).unwrap();
        prop_assert_eq!(Ticket::parse(&b[..len]), Ok(t));
        let mut txt = [0u8; MAX_TEXT];
        let m = t.to_text(&mut txt).unwrap();
        prop_assert_eq!(Ticket::from_text(&txt[..m]), Ok(t));
    }

    #[test]
    fn parse_and_text_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..160)) {
        let _ = Ticket::parse(&bytes);
        let _ = Ticket::from_text(&bytes);
    }
}
