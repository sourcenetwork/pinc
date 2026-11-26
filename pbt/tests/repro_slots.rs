//! Reproducing tests of bugs the `slots` properties found in `pinc-core`. Each fails on the unmodified code.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::{Command, Endpoint, EndpointConfig, Role, Slot, Value};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_transport::conn::{Held, Machines, Resources, Shared, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};

const K: usize = 8;
type Ep<'s> = Endpoint<'s, 'static, Software, NoSource, 8, 17, 128, 4, K, 128, 8, 16, 8>;
type NSlot = Slot<'static, Software, NoSource, 8, 17, 128, 4>;

const SEC: u64 = 1_000_000_000;

fn table() -> Box<[NSlot; K]> {
    let loss = Rc::new(LossEstimate::new());
    let machines = Machines::new();
    let v: Vec<NSlot> = (0..K)
        .map(|_| {
            let pool = BufferPool::new_grown(128);
            let streams = Box::new(Streams::new(&stream::Config::new(false), &pool));
            Slot::new(Resources {
                pool,
                streams: Held::Owned(streams),
                loss: Shared::Counted(Rc::clone(&loss)),
                tables: Tables::sharing(&machines),
            })
        })
        .collect();
    v.into_boxed_slice().try_into().ok().unwrap()
}

fn endpoint(tag: u8, now: u64, slots: &mut [NSlot; K]) -> Box<Ep<'_>> {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let ident = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let mut ep = Box::new(Endpoint::new(now, Software, Drbg::new(&[tag; 32]), ident, EndpointConfig::new(7), slots));
    let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
    let mut env = Env { provider: &Software, now, drbg: &mut drbg };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    ep.set_prekey(prekeys.acquire(&mut env).unwrap());
    assert!(ep.register_alpn(b"pinc/a"));
    assert!(ep.add_iface(([10, 0, 0, tag], 4433).into()).is_some());
    ep
}

/// A dial on `ep` to a fixed peer; whether anything leaves within `span` of timers (the first flight and its resends).
fn dial_sends(ep: &mut Ep<'_>, now: u64, span: u64) -> bool {
    let peer = Keypair::from_seed(IdentityAlg::Ed25519, &[2; 32]).unwrap();
    let peer = LocalIdentity::from_keypair(&peer, KeyHandle(1)).unwrap().node_id();
    let to: SocketAddr = ([10, 0, 0, 2], 4433).into();
    let r = ep.command(now, Command::Connect { node: peer, alpn: b"pinc/a", addrs: &[to], role: Role::Other });
    assert!(matches!(r.map(|r| r.value), Ok(Value::Session(_))), "the dial was refused");
    let mut buf = vec![0u8; 65_536];
    let mut t = now;
    for _ in 0..10_000 {
        while ep.poll_event().is_some() {}
        if ep.poll_transmit(t, &mut buf).is_some() {
            return true;
        }
        match ep.poll_timeout() {
            Some(d) if d <= now + span => {
                t = d.max(t);
                ep.handle_timeout(t);
            },
            _ => return false,
        }
    }
    false
}

/// An endpoint built on a connection table that another endpoint gave back with `into_slots` while one of its sessions
/// waited in the send queue never sends for the session that next takes that slot: a dial's first flight never leaves,
/// nor its resends, until the dial times out.
///
/// Expected (crates/pinc-core/src/endpoint.rs, `into_slots`): "give its connection table back with every session closed
/// and every slot's memory returned, so another endpoint can run in the same memory"; `Endpoint::new` takes such a
/// table. A dial on the new endpoint sends its first flight at once, as on a fresh table (the control below).
///
/// Actual: endpoint X dials (the session's slot 0 is put on the send queue, `Meta::dirty = 1`) and is ended with
/// `into_slots` before its host polls `poll_transmit`. Endpoint Y on the same table dials: `poll_transmit` returns
/// `None` and goes on doing so through 25 s of timers. The property's case:
/// `Case { history: [Dial(0)], drain: false, script: [Pump], loss: 0, seed: 0 }` (`EPHYRA_REPLAY=16898037739589038103:26`
/// of `an_endpoint_on_a_used_table_behaves_as_on_a_fresh_one`).
///
/// Suspected fault: the send-queue mark of a slot survives the hand-over. `free_slot` (endpoint.rs:859-902) leaves
/// `m.dirty` and `m.dirty_next` as they are (right inside one endpoint, whose queue still lists the slot and skips it
/// when served), `with_slots` (endpoint.rs:450-526) resets only `next_free` and starts with empty queues
/// (`dirty_head = [NIL; 2]`), and `Meta::begin` (slot.rs:358-373) keeps `dirty` on purpose. So `mark_dirty`
/// (endpoint.rs:974-979) sees `dirty != 0` and returns without queueing the slot: no session in that slot is ever
/// served by `poll_transmit` (tx.rs:62). `into_slots` or `with_slots` should clear `dirty` and `dirty_next` of every
/// slot.
///
/// Who: the local application through the public API: any host that ends an endpoint with `into_slots` and builds
/// another on the table without first polling `poll_transmit` to `None` (the simulator's `recycle`,
/// crates/pinc-sim/src/suite/node/mem.rs:76-81, ends a node at the end of a run and at a restart, mid-step).
#[test]
fn a_slot_queued_to_send_when_its_table_is_given_back_never_sends_again() {
    let h = std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(|| {
            let now = 10 * SEC;
            let mut fresh = table();
            let mut ep = endpoint(1, now, &mut fresh);
            assert!(dial_sends(&mut ep, now, 25 * SEC), "control: a dial on a fresh table sends nothing");

            let mut t = table();
            let mut x = endpoint(3, now, &mut t);
            let peer = LocalIdentity::from_keypair(&Keypair::from_seed(IdentityAlg::Ed25519, &[4; 32]).unwrap(), KeyHandle(1))
                .unwrap()
                .node_id();
            let to: SocketAddr = ([10, 0, 0, 4], 4433).into();
            let r = x.command(now, Command::Connect { node: peer, alpn: b"pinc/a", addrs: &[to], role: Role::Other });
            assert!(r.is_ok());
            let back = (*x).into_slots().expect("every slot has its memory back");
            let mut y = endpoint(1, now, back);
            assert!(
                dial_sends(&mut y, now, 25 * SEC),
                "a dial on a table given back while a session waited to send sends nothing"
            );
        })
        .unwrap();
    if let Err(e) = h.join() {
        std::panic::resume_unwind(e);
    }
}
