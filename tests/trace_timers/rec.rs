//! The recorder of the timers trace: the microsecond rounding the checkers take, the carrier rule's decision and the
//! ndjson log with its counters.

use std::fmt::Write as _;

use pinc_tests::*;
use pinc_transport::conn::{CarrierView, CloseReason, Event, Lent, TimerView};

/// The largest integer TLC holds.
pub const TOP: i64 = 2_147_483_647;

/// A lifecycle time in whole microseconds, rounded up.
pub fn us(t: u64) -> i64 {
    let v = i64::try_from(t.div_ceil(1000)).unwrap();
    assert!(v < TOP, "a lifecycle time past the checker's integers: {t}");
    v
}

pub fn ous(t: Option<u64>) -> i64 {
    t.map_or(-1, us)
}

/// A component deadline in whole microseconds, rounded up, and held at `TOP`.
pub fn cus(t: Option<u64>) -> i64 {
    t.map_or(-1, |t| i64::try_from(t.div_ceil(1000)).unwrap_or(TOP).min(TOP))
}

/// The recovery timer's reads of a `handle_timeout` call for the carrier rule, as the checkers take them: times in whole
/// microseconds (the carrier's and the peer's are whole already; the smoothed and node round trips are rounded up), and
/// the call's own probe timeout and dead path. A call whose recovery timer did not run reads nothing.
pub fn probe_json(p: Option<&CarrierView>) -> String {
    let Some(p) = p else {
        return r#","pr":{"ping":false,"dead":false,"relay":false,"ch":-1,"pto":0,"lh":0,"smp":true,"sr":1,"nd":0}"#
            .into();
    };
    assert!(
        p.carrier.is_none_or(|c| c % 1000 == 0) && p.heard % 1000 == 0,
        "a carrier or peer time off the microsecond"
    );
    format!(
        r#","pr":{{"ping":{},"dead":{},"relay":{},"ch":{},"pto":{},"lh":{},"smp":{},"sr":{},"nd":{}}}"#,
        p.ping,
        p.dead,
        p.relay,
        ous(p.carrier),
        p.ptos,
        us(p.heard),
        p.sampled,
        us(p.srtt),
        us(p.node)
    )
}

/// What `dead_behind_live_carrier` decides, from the read times in nanoseconds, and the same from the rounded ones the
/// checkers take: both must agree at the call's time.
pub fn carrier_decision(p: &CarrierView, now: u64) -> bool {
    let rtt = if p.sampled { p.srtt } else { (333 * MS).max(p.node * 2) };
    let exact = p.relay
        && p.carrier.is_some_and(|h| now.saturating_sub(h) < 6 * SEC)
        && p.ptos >= 4
        && now.saturating_sub(p.heard) >= rtt * 4;
    let (nowu, rttu) = (
        now.div_ceil(1000),
        if p.sampled {
            p.srtt
        } else {
            (333 * MS).max(p.node.div_ceil(1000) * 2000)
        }
        .div_ceil(1000),
    );
    let rounded = p.relay
        && p.carrier.is_some_and(|h| nowu.saturating_sub(h / 1000) < 6_000_000)
        && p.ptos >= 4
        && nowu.saturating_sub(p.heard / 1000) >= rttu * 4;
    assert_eq!(
        exact, rounded,
        "rounding to microseconds changed the carrier rule at {now}: {p:?}"
    );
    exact
}

pub fn view_json(v: &TimerView) -> String {
    let ph = ["hs", "conn", "closing", "closed"][usize::from(v.phase)];
    format!(
        r#"{{"ph":"{ph}","close":{},"keys":{},"act":{},"sent":{},"ka":{},"pa":{},"la":{},"stx":{},"wd":{},"ld":{},"idle":{},"conf":{},"hs":{},"rekey":{},"rec":{},"ack":{},"amp":{},"paced":{},"path":{},"mtu":{}}}"#,
        v.close.map_or(-1, |c| i64::try_from(c).unwrap()),
        v.send_keys,
        us(v.last_activity),
        us(v.last_sent),
        ous(v.keepalive),
        ous(v.peer_asleep),
        v.local_asleep,
        v.sleep_tx,
        ous(v.wake_deadline),
        ous(v.link_down),
        us(v.idle),
        v.confirmed,
        cus(v.hs),
        cus(v.rekey),
        cus(v.rec),
        cus(v.ack),
        v.amp_ok,
        cus(v.paced),
        cus(v.path),
        cus(v.mtu)
    )
}

/// The ndjson being written and what the test counts by itself.
pub struct Log {
    pub out: String,
    pub run: u32,
    /// CLOSE packets that left each node of the run (a datagram written while closing).
    pub closes: [u32; 2],
    /// Events of each kind seen over all runs, to show the scenarios reach them.
    pub seen: std::collections::BTreeMap<&'static str, usize>,
}

impl Log {
    /// One event: the call `op` of node `n` at `now`, with `extra` (`,"k":v` pairs), the lifecycle events the
    /// connection reports after it and its timers.
    pub fn line(&mut self, n: usize, node: &mut Node<'_>, now: u64, op: &str, extra: &str) -> Vec<&'static str> {
        let v = node.conn.trace_timers();
        let mut ev = Vec::new();
        while let Some(e) = node.conn.poll_event(Lent {
            spill: &mut node.spill,
            store: &mut node.store,
        }) {
            ev.push(match e {
                Event::Closed(r) => match r {
                    CloseReason::Local { .. } => "local",
                    CloseReason::Peer { .. } => "peer",
                    CloseReason::Violation { .. } => "viol",
                    CloseReason::IdleTimeout => "idle",
                    CloseReason::PathDead => "dead",
                    CloseReason::HandshakeTimeout | CloseReason::Unanswered => "hs",
                    CloseReason::Unconfirmed => "unconf",
                    CloseReason::Handshake(f) => panic!("the handshake failed: {f:?}"),
                },
                Event::PeerAsleep => "asleep",
                Event::PeerAwake => "awake",
                Event::WakeUnanswered => "unanswered",
                Event::Connected { .. } => "connected",
                _ => continue,
            });
        }
        for e in &ev {
            *self.seen.entry(e).or_default() += 1;
        }
        *self.seen.entry(leak(op)).or_default() += 1;
        let evs: Vec<String> = ev.iter().map(|e| format!("\"{e}\"")).collect();
        let name = if n == 0 { "a" } else { "b" };
        let _ = writeln!(
            self.out,
            r#"{{"t":"tmr","run":{},"n":"{name}","op":"{op}","now":{}{extra},"ev":[{}],"v":{}}}"#,
            self.run,
            us(now),
            evs.join(","),
            view_json(&v)
        );
        ev
    }
}

pub fn leak(op: &str) -> &'static str {
    match op {
        "init" => "init",
        "poll" => "poll",
        "timeout" => "timeout",
        "tx" => "tx",
        "recv" => "recv",
        "inject" => "inject",
        "close" => "close",
        "sleep" => "sleep",
        "wake" => "wake",
        "link" => "link",
        "keepalive" => "keepalive",
        "pulse" => "pulse",
        _ => "app",
    }
}
