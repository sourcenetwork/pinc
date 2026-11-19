//! The node works its deadline out once for the calls that cannot move it. Asking for a datagram to send, for a
//! connectivity datagram or for a carrier request when none waits is not an input, so the answer stands. A command that
//! only moves the application's data can move the endpoint's deadline and no layer's: the endpoint's part is read
//! again and the layers' part stands until a call lets them run.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::{ScriptNode, node_with};
use pinc_core::{Command, SessionId};
use pinc_node::{HUB_ALPN, NoApps};

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

/// A node over a script that says exactly what waits (`exact`), or one that cannot tell.
fn node(exact: bool) -> Box<ScriptNode<NoApps>> {
    let mut n = node_with(false, &[], HUB_ALPN, NoApps::default()).unwrap();
    n.endpoint_mut().exact = exact;
    n
}

/// A command that moves the application's data and raises no event.
fn move_data(n: &mut ScriptNode<NoApps>, now: u64) {
    n.data_command(
        now,
        Command::SendDatagram {
            session: SessionId(1),
            data: b"x",
        },
    )
    .unwrap();
}

#[test]
fn asking_for_what_does_not_wait_keeps_the_deadline() {
    big(|| {
        let mut n = node(true);
        let before = n.poll_timeout();
        assert!(n.deadline_cached());
        let mut b = [0u8; 2048];
        assert!(n.poll_transmit(SEC, &mut b).is_none());
        assert!(
            n.deadline_cached(),
            "asking for a datagram to send, with none waiting, cleared the cached deadline"
        );
        assert!(n.poll_udp(&mut b).is_none());
        assert!(n.poll_udp_from(&mut b).is_none());
        assert!(n.poll_io().is_none());
        assert!(
            n.deadline_cached(),
            "asking the connectivity layer, with nothing queued, cleared the cached deadline"
        );
        assert_eq!(n.poll_timeout(), before);
    });
}

#[test]
fn an_endpoint_that_cannot_tell_is_asked_and_the_deadline_is_worked_out_again() {
    big(|| {
        let mut n = node(false);
        let _ = n.poll_timeout();
        assert!(n.deadline_cached());
        let mut b = [0u8; 2048];
        assert!(n.poll_transmit(SEC, &mut b).is_none());
        assert!(
            !n.deadline_cached(),
            "a poll that reached the endpoint kept the cached deadline"
        );
    });
}

#[test]
fn a_command_that_moves_data_keeps_the_layers_deadline_and_reads_the_endpoints_again() {
    big(|| {
        let mut n = node(true);
        // The layers' first timers run, so that their deadline lies ahead of the clock.
        let mut layers = n.poll_timeout();
        for _ in 0..8 {
            if layers.is_none_or(|d| d > SEC) {
                break;
            }
            n.handle_timeout(SEC);
            layers = n.poll_timeout();
        }
        assert!(
            layers.is_none_or(|d| d > SEC),
            "the layers keep a timer due: {layers:?}"
        );
        assert!(n.layers_deadline_cached());
        // The command arms a timer of the endpoint, earlier than any layer's.
        let script = n.endpoint_mut();
        (script.rearm, script.next_due) = (true, Some(SEC));
        let _ = n.poll_timeout();
        move_data(&mut n, SEC);
        assert!(
            n.layers_deadline_cached(),
            "a command that only moved data cleared the layers' deadline"
        );
        assert!(!n.deadline_cached(), "the endpoint's deadline was not asked for again");
        assert_eq!(
            n.poll_timeout(),
            Some(SEC),
            "the endpoint's new deadline is not the node's"
        );
        // The next command disarms it: the layers' deadline is the node's again, without having been worked out anew.
        let script = n.endpoint_mut();
        (script.rearm, script.next_due) = (true, None);
        let _ = n.poll_timeout();
        move_data(&mut n, SEC);
        assert!(n.layers_deadline_cached());
        assert_eq!(n.poll_timeout(), layers);
    });
}

#[test]
fn a_call_that_lets_the_layers_run_clears_their_deadline() {
    big(|| {
        let mut n = node(true);
        let _ = n.poll_timeout();
        move_data(&mut n, SEC);
        assert!(n.layers_deadline_cached());
        // Time passes for the layers.
        n.handle_timeout(2 * SEC);
        assert!(
            !n.layers_deadline_cached(),
            "the layers ran and their deadline stayed cached"
        );
        let _ = n.poll_timeout();
        // A command that raised an event lets them run too.
        n.endpoint_mut()
            .events
            .push_back(pinc_core::Event::DatagramReceived { session: SessionId(1) });
        let _ = n.poll_timeout();
        assert!(n.layers_deadline_cached());
        move_data(&mut n, 3 * SEC);
        assert!(
            !n.layers_deadline_cached(),
            "a command with an event waiting did not let the layers run"
        );
    });
}
