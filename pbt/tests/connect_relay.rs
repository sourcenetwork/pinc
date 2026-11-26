//! `pinc-connect`: the relay role as one state machine, against a reference model, under hostile attached nodes,
//! hostile peers and hostile unattached senders.
//!
//! Where the expected behaviour comes from:
//! - `relay` (module doc): "Authenticated peers only ... forwarded packets and replicated records are accepted only
//!   from a node id in the set of authenticated peer relays ... anything else is [`Reject::Unauthenticated`]", "The
//!   relay never reads relayed content", "Bounded. Every table has a compile-time capacity; per-node byte and time
//!   limits ([`Quota`]) bound what one node can relay", "No loops. A packet that arrived from a peer relay is never
//!   forwarded to another relay", "Nothing ... panics".
//! - `relay::route` (module doc): the five routing rules, in order; the model below implements them as written.
//! - `relay::clients`: "A node has at most one session; a newer one replaces the older, and calls about the older one
//!   are ignored", "a frame over the window is dropped and traced, never queued", "A session older than the quota's
//!   time limit is closed by the sweep", "When a carrier closes the node becomes \"gone\" with the time; if its sleep
//!   notice came within [`super::rule::SLEEP_WIN_NS`] before, the close is a suspension", and `carrier_frame`: "The
//!   [`Reject`] reason; the input is dropped and traced, the session stays up".
//! - `relay::records` and `docs/proofs/properties.md` (the record store row): "a lower number, or an equal one with
//!   different bytes, is refused and changes nothing (equal bytes only renew the receive time, a higher number
//!   replaces)", "a lookup answers only with a stored, unexpired, verified record", "a published or own record goes
//!   once to every peer relay", `restore_record`: "it ends [`super::rule::RECORD_TTL_NS`] after that, not after the
//!   restart"; and `held_packet`: "A host keeps these across a restart and gives them back with
//!   [`Relay::restore_held`]".
//! - `relay::sleep`: "a notice counts only if its clock is within [`SKEW_MS`] of the relay's, its sender holds a
//!   carrier here or just lost one, and its signature verifies".
//! - `carrier::alias`: the receiver "overwrites the slot named by a new-alias frame"; a receiver that learns aliases
//!   from the stream stays in step, so every alias the relay sends resolves at the receiver to the true source.
//! - `pinc_core::ledger` (the amplification gate every outgoing datagram of a node is meant to pass): "for an address
//!   that is not validated the bytes charged never exceed three times the bytes received, so a spoofed source gets at
//!   most three times what it sent". Read here on wire bytes (each datagram plus 28 header bytes, both ways), which is
//!   looser than the ledger itself (it counts the received bytes without headers).
//!
//! The existing tests (`tests/connect_relay.rs`, `tests/connect_hub_held.rs`, the TLA+ and Lean models) check each
//! rule on hand-built inputs. Here one generated run interleaves every entry point: carriers opened, replaced and
//! closed (current and stale), every client frame (valid, forbidden, mangled, batched), peer frames from
//! authenticated and unauthenticated relays, datagrams from members and from unvalidated addresses, sleep notices
//! (for this relay, for another, skewed, tampered, replayed), records (valid, tampered, wrong owner, lower, equal,
//! higher), the clock (with and without the host's deadline), and a restart with the same identity restored from what
//! the relay saved. After every step the model predicts the result, every effect but the release of held mail, every
//! refusal, every quota drop and every stored record, and checks the tables against their limits.


mod connect_relay_model;

use connect_relay_model::world::World;
use connect_relay_model::{C, Op, Setup, case};

fn drive(setup: &Setup, ops: &[Op], gone_cap: Option<usize>) {
    let mut w = World::new(setup, gone_cap);
    for (i, op) in ops.iter().enumerate() {
        w.step = i;
        w.op(op);
    }
}

/// The relay role against the reference model of its rules, with the table of gone nodes as the module doc states
/// it: "When a carrier closes the node becomes \"gone\" with the time".
#[ephyra::test(gen = case(), tests = 1500)]
fn the_relay_role_follows_its_rules_step_by_step(case: (Setup, Vec<Op>)) {
    drive(&case.0, &case.1, None);
}

/// The same run with the table of gone nodes modelled as the code keeps it (capacity `C`, a close it has no room for
/// is not recorded), so a run that reaches that finding goes on to check everything else.
#[ephyra::test(gen = case(), tests = 1500)]
fn the_relay_role_follows_its_rules_past_a_full_table_of_gone_nodes(case: (Setup, Vec<Op>)) {
    drive(&case.0, &case.1, Some(C));
}
