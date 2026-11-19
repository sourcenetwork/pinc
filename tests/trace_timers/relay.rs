//! The relay runs of the timers trace: the session closed behind a live carrier, and the near misses.

use pinc_tests::*;
use pinc_transport::conn::{PathId, PathInfo};
use pinc_transport::recovery::PathKind;

use crate::duo::{app, simple, with_pair_at};
use crate::rec::Log;

/// How the carrier of the relay path answers in a `relay_run`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Carrier {
    /// Heard 1 ms ago at every timer call.
    Fresh,
    /// Heard exactly 6 s ago: not fresh.
    Stale,
    /// Heard 6 s less a microsecond ago: fresh.
    Edge,
    /// Not open.
    Never,
    /// Fresh, and the peer is heard (a keepalive answer of the carrier) just before every timer call.
    Heard,
    /// Fresh, and the peer last heard exactly 4 fallback round trips (4 x max(333 ms, 2 x the node's)) before every timer
    /// call: silent enough.
    SilentHit,
    /// Fresh, and the peer last heard a microsecond less than 4 fallback round trips before every timer call.
    SilentMiss,
}

/// A session on a path whose probes time out while nothing comes back, with the carrier of a relay path answering as
/// `carrier` says: the probe timeouts grow in a row, and the session is closed behind a live carrier at the 4th when
/// the rule holds. `relay` says whether the active path is a relay path.
pub fn relay_run(
    log: &mut Log,
    seed: u64,
    relay: bool,
    carrier: Carrier,
    node_rtt: Option<u64>,
    side: usize,
    resent: bool,
) {
    with_pair_at(seed, false, resent, |d| {
        d.init(log);
        d.exchange(log);
        let me = side;
        if let Some(r) = node_rtt {
            d.nodes[me].conn.set_node_rtt(r, 0, false);
        }
        let info = PathInfo {
            kind: if relay { PathKind::Relay } else { PathKind::Direct },
            ..PathInfo::default()
        };
        d.nodes[me].conn.set_path_info(PathId(1 + me as u64), info);
        assert_eq!(d.nodes[me].conn.active_is_relay(), relay);
        d.now += 10 * SEC;
        app(log, me, &mut d.nodes[me], d.now, 20_000);
        for _ in 0..40 {
            d.tx(log, me);
            d.tx(log, 1);
            d.lose_all();
            let Some(t) = d.next_deadline() else { break };
            d.now = d.now.max(t.div_ceil(1000) * 1000);
            let now = d.now;
            d.nodes[me].conn.set_carrier_heard(match carrier {
                Carrier::Fresh | Carrier::Heard | Carrier::SilentHit | Carrier::SilentMiss => Some(now - MS),
                Carrier::Stale => Some(now - 6 * SEC),
                Carrier::Edge => Some(now - 6 * SEC + 1000),
                Carrier::Never => None,
            });
            let four = 4 * (333 * MS).max(2 * node_rtt.unwrap_or(0));
            match carrier {
                Carrier::Heard => simple(log, me, &mut d.nodes[me], now, "pulse", 0),
                Carrier::SilentHit => simple(log, me, &mut d.nodes[me], now - four, "pulse", 0),
                Carrier::SilentMiss => simple(log, me, &mut d.nodes[me], now - four + 1000, "pulse", 0),
                _ => {}
            }
            d.fire(log);
            if d.nodes[me].conn.is_closed() || d.nodes[1 - me].conn.is_closed() {
                break;
            }
        }
        if carrier == Carrier::SilentMiss {
            assert!(
                !d.nodes[me].conn.is_closed(),
                "a session silent for less than 4 round trips was closed"
            );
        }
        if relay && matches!(carrier, Carrier::Fresh | Carrier::Edge | Carrier::SilentHit) {
            assert!(
                d.nodes[me].conn.is_closed(),
                "the session behind a live carrier was not closed"
            );
            assert_eq!(log.closes[me], 0);
            // its CLOSE leaves, once
            d.tx(log, me);
            assert_eq!(log.closes[me], 1, "the carrier close sends its CLOSE");
            d.deliver_all(log);
        }
    });
}
