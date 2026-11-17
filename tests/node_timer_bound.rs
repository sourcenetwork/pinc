//! A deadline that a timer call leaves due where the call before had left it is counted against the layer that holds
//! it, recorded in the trace once for that layer, and the node asks for its next call one tick later (vinc#569). A
//! host that serves due timers before anything else (the facade's `run_as`) therefore yields between two calls,
//! whatever a layer does with its deadline. The layer here is the scripted endpoint, whose timer call does nothing.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::{ScriptNode, node_traced};
use vinc_node::{Body, HUB_ALPN, NoApps, NodeTrace, TIMER_TICK, Timed, TimerStats};

const SEC: u64 = 1_000_000_000;

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// The records of a deadline left due that the node traced since the last call.
fn stuck_records(n: &mut ScriptNode<NoApps>) -> Vec<u64> {
    let mut out = Vec::new();
    while let Some(item) = n.poll_trace() {
        if let Body::Node(NodeTrace::TimerStuck { timer }) = item.body {
            out.push(timer);
        }
    }
    out
}

#[test]
fn a_deadline_its_timer_calls_do_not_move_is_counted_and_asked_again_one_tick_later() {
    big(|| {
        let mut n = node_traced(false, &[], HUB_ALPN, NoApps::default()).unwrap();
        let mut now = SEC;
        // The layers' first timers run, so that their deadline lies ahead of the clock.
        for _ in 0..8 {
            if n.poll_timeout().is_none_or(|d| d > now) {
                break;
            }
            n.handle_timeout(now);
        }
        let layers = n.poll_timeout();
        assert!(
            layers.is_none_or(|d| d > now),
            "the layers keep a timer due: {layers:?}"
        );
        assert_eq!(
            n.timer_stats(),
            TimerStats::default(),
            "a node whose timers move counted one"
        );
        assert_eq!(stuck_records(&mut n), Vec::<u64>::new());

        // The endpoint's deadline is due and stays where it is: its timer call does nothing. The first call that
        // leaves it due could be the endpoint asking to be called again at once, so the host is: the deadline stands.
        let stuck = now;
        n.endpoint_mut().due = Some(stuck);
        n.handle_timeout(now);
        assert_eq!(n.poll_timeout(), Some(stuck));
        assert_eq!(n.timer_stats(), TimerStats::default());
        // Every call from then on did not move it.
        let calls = 5;
        for call in 1..=calls {
            n.handle_timeout(now);
            assert_eq!(
                n.poll_timeout(),
                Some(now + TIMER_TICK),
                "call {call}: the host is not asked to come back one tick later"
            );
            assert_eq!(n.timer_stats().stuck(Timed::Endpoint), call);
            // The host yields until the deadline the node named.
            now += TIMER_TICK;
        }
        assert_eq!(n.timer_stats().total(), calls, "only the endpoint is named");
        assert_eq!(
            stuck_records(&mut n),
            vec![0],
            "one record, the first time, naming the endpoint"
        );

        // The endpoint's deadline moves again: the node answers what its layers name and counts nothing more.
        n.endpoint_mut().due = Some(now + 10 * TIMER_TICK);
        n.handle_timeout(now);
        let moved = [layers, Some(now + 10 * TIMER_TICK)].into_iter().flatten().min();
        assert_eq!(n.poll_timeout(), moved);
        assert_eq!(n.timer_stats().total(), calls);
        assert_eq!(stuck_records(&mut n), Vec::<u64>::new());
    });
}
