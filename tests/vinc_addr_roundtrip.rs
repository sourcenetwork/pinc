//! A node address prints to a ticket that parses back to it, and a node id has one text.
#![allow(clippy::unwrap_used)]

use vinc::{ErrorKind, NodeAddr};

fn id() -> vinc::NodeId {
    vinc::node_from_str(&"ab".repeat(32)).unwrap()
}

#[test]
fn a_relay_the_ticket_cannot_give_back_is_refused_where_it_enters() {
    for relay in ["https://a,b", "relay-no-scheme", ""] {
        let e = NodeAddr::new(id()).with_relay(relay).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Config, "{relay:?}");
    }
}

#[test]
fn every_relay_that_is_accepted_survives_the_ticket() {
    for relay in ["https://u@h", "wss://relay", "https://relay.example/path?x=1"] {
        let a = NodeAddr::new(id())
            .with_direct("10.0.0.7:4433".parse().unwrap())
            .with_relay(relay)
            .unwrap();
        assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a, "{relay}");
    }
}

#[test]
fn node_id_text_is_exactly_64_lowercase_hex_characters() {
    let plus = format!("+a{}", "ab".repeat(31));
    let upper = "AB".repeat(32);
    let tagged_plus = format!("+1.{}", "ab".repeat(32));
    for t in [plus, upper, tagged_plus] {
        assert_eq!(vinc::node_from_str(&t).unwrap_err().kind(), ErrorKind::Config, "{t}");
    }
    let n = vinc::node_from_str(&"ab".repeat(32)).unwrap();
    assert_eq!(vinc::node_from_str(&vinc::node_to_string(&n)).unwrap(), n);
}
