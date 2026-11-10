//! First-flight rules: B8 (direct first) and B9 (THIN_HS, RLY_ONCE, THIN_HS0).
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

use vinc_connect::client::dial::{
    Cand, HUB_RELAY_DELAY, RelayView, TG_SLOW, THIN_HS0_WAIT, Try, direct_first, hs0, select,
};

const S: u64 = 1_000_000_000;
const MS: u64 = 1_000_000;

fn udp(p: u16) -> Cand {
    Cand::Udp(([192, 0, 2, 1], p).into())
}

fn base() -> Try {
    Try {
        now: 100 * S,
        dialer: true,
        tries: 1,
        link_rtt: 50 * MS,
        no_rtt: false,
        hs0: false,
        last_relay: None,
    }
}

fn pick(c: &[Cand], t: &Try, live: bool, generation: u64) -> Vec<Cand> {
    let mut out = [Cand::Relay(0); 16];
    let (n, _) = select(c, t, |_| Some(RelayView { live, generation }), &mut out);
    out[..n].to_vec()
}

#[test]
fn b8_direct_first_applies_to_a_hub_first_try_of_a_late_start() {
    assert_eq!(HUB_RELAY_DELAY, 300 * MS);
    let started = 0;
    assert!(
        !direct_first(true, true, 10 * S, started),
        "a dial at exactly 10 s is not late"
    );
    assert!(direct_first(true, true, 10 * S + 1, started));
    assert!(!direct_first(false, true, 20 * S, started), "only the first try");
    assert!(!direct_first(true, false, 20 * S, started), "only a hub");
}

#[test]
fn a_fast_link_sends_every_path_at_once() {
    let c = [udp(1), udp(2), Cand::Relay(0)];
    assert_eq!(pick(&c, &base(), true, 1), c.to_vec());
}

#[test]
fn thin_hs_sends_one_path_per_try_rotating_on_a_slow_link() {
    let c = [udp(1), udp(2), Cand::Relay(0)];
    let mut t = base();
    t.link_rtt = TG_SLOW;
    for tries in 1..=7u32 {
        t.tries = tries;
        assert_eq!(pick(&c, &t, false, 1), vec![c[tries as usize % 3]], "try {tries}");
    }
    t.link_rtt = TG_SLOW - 1;
    assert_eq!(pick(&c, &t, false, 1).len(), 3, "249.999 ms is not slow");
    // no round trip at all: from the second try
    t.no_rtt = true;
    t.link_rtt = 0;
    t.tries = 1;
    assert_eq!(pick(&c, &t, false, 1).len(), 3);
    t.tries = 2;
    assert_eq!(pick(&c, &t, false, 1), vec![c[2]]);
    // a single path is never rotated, and a server never rotates
    assert_eq!(pick(&c[..1], &t, false, 1), vec![c[0]]);
    t.dialer = false;
    assert_eq!(pick(&c, &t, false, 1).len(), 3);
}

#[test]
fn rly_once_skips_a_relay_already_holding_the_flight_for_min_30s_max_4s_3_rtt() {
    let c = [udp(1), Cand::Relay(2)];
    let mut t = base();
    t.link_rtt = TG_SLOW; // 3 x 250 ms = 750 ms: the wait is the 4 s floor
    t.tries = 2; // rotation would pick index 0; isolate RLY_ONCE with a single relay
    let only_relay = [Cand::Relay(2)];
    t.last_relay = Some((2, 7, t.now - 4 * S + 1));
    assert_eq!(
        pick(&only_relay, &t, true, 7),
        vec![],
        "within 4 s on the same stream generation"
    );
    t.last_relay = Some((2, 7, t.now - 4 * S));
    assert_eq!(
        pick(&only_relay, &t, true, 7),
        vec![Cand::Relay(2)],
        "at 4 s it is queued again"
    );
    t.last_relay = Some((2, 6, t.now));
    assert_eq!(
        pick(&only_relay, &t, true, 7),
        vec![Cand::Relay(2)],
        "a reset carrier (new generation) takes it again"
    );
    t.last_relay = Some((2, 7, t.now));
    assert_eq!(
        pick(&only_relay, &t, false, 7),
        vec![Cand::Relay(2)],
        "a carrier that is down takes it again"
    );
    // 3 x link rtt above 4 s: 12 s link rtt gives 30 s cap, 2 s rtt gives 6 s
    t.link_rtt = 2 * S;
    t.last_relay = Some((2, 7, t.now - 6 * S + 1));
    assert_eq!(pick(&only_relay, &t, true, 7), vec![]);
    t.last_relay = Some((2, 7, t.now - 6 * S));
    assert_eq!(pick(&only_relay, &t, true, 7).len(), 1);
    t.link_rtt = 20 * S;
    t.last_relay = Some((2, 7, t.now - 30 * S + 1));
    assert_eq!(pick(&only_relay, &t, true, 7), vec![], "capped at 30 s");
    t.last_relay = Some((2, 7, t.now - 30 * S));
    assert_eq!(pick(&only_relay, &t, true, 7).len(), 1);
    // not slow: never applies
    t.link_rtt = 10 * MS;
    t.last_relay = Some((2, 7, t.now));
    assert_eq!(pick(&c, &t, true, 7).len(), 2);
}

#[test]
fn thin_hs0_sends_only_relay_paths() {
    let c = [udp(1), Cand::Relay(0), udp(2)];
    let mut t = base();
    t.hs0 = true;
    assert_eq!(pick(&c, &t, true, 1), vec![Cand::Relay(0)]);
    t.dialer = false;
    assert_eq!(pick(&c, &t, true, 1).len(), 3);
}

#[test]
fn the_selection_reports_the_relay_that_now_holds_the_flight() {
    let c = [udp(1), Cand::Relay(3)];
    let mut out = [Cand::Relay(0); 16];
    let (n, carried) = select(
        &c,
        &base(),
        |_| {
            Some(RelayView {
                live: true,
                generation: 9,
            })
        },
        &mut out,
    );
    assert_eq!(n, 2);
    assert_eq!(carried, Some((3, 9)));
    let (_, none) = select(&c[..1], &base(), |_| None, &mut out);
    assert_eq!(none, None);
}

#[test]
fn a_hub_initial_goes_by_relay_paths_only_while_nothing_at_all_has_been_heard() {
    assert_eq!(THIN_HS0_WAIT, 4 * S);
    // a resend of a hub session inside the first four seconds, on a node that heard no round trip of any kind
    assert!(hs0(true, 2, 0, true));
    assert!(hs0(true, 5, 4 * S - 1, true));
    // a round trip of any kind (an address-discovery answer, a handshake average or peak, one remembered for the
    // peer) ends it
    assert!(!hs0(true, 2, 0, false));
    // the first send, a later one, another peer, and the first resend after the wait are unchanged
    assert!(!hs0(true, 1, 0, true));
    assert!(!hs0(true, 2, 4 * S, true));
    assert!(!hs0(false, 2, 0, true));
}
