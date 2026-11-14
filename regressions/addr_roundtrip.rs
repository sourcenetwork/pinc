//! Probe: `NodeAddr::parse(&a.ticket()) == Ok(a)` fails for relay strings the builder accepts.
use vinc::NodeAddr;

fn id() -> vinc::NodeId {
    vinc::node_from_str(&"ab".repeat(32)).unwrap()
}

#[test]
fn relay_with_a_comma_round_trips() {
    let a = NodeAddr::new(id()).with_relay("https://a,b");
    assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a); // Err: "b" is not ip:port
}

#[test]
fn relay_without_a_scheme_round_trips() {
    let a = NodeAddr::new(id()).with_relay("relay-no-scheme");
    assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a); // Err: read as a direct address
}

#[test]
fn empty_relay_round_trips() {
    let a = NodeAddr::new(id()).with_relay("");
    assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a); // Ok but relays is empty
}

#[test]
fn node_id_text_with_a_plus_sign_is_not_canonical() {
    let t = format!("+a{}", "ab".repeat(31));
    let n = vinc::node_from_str(&t).unwrap();
    assert_eq!(vinc::node_to_string(&n), t); // "0aab.." printed: two texts, one id
}
