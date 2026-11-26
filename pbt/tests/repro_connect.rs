//! Reproducers of the bugs the properties of `connect_relay.rs` found in the relay role. Each test fails on the
//! unmodified code and passes once the bug is fixed; its doc comment says what is expected and why.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::future::{Future, pending};
use std::net::{Ipv4Addr, SocketAddr};
use std::pin::pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

use pinc::relay::{CarrierFns, Clock, Kept, KeptRecord, Peer, Relay as Host, Store, Udp};
use pinc::{CarrierKind, Error, ErrorKind, Identity};
use pinc_connect::carrier::{Frame, MAX_FRAME_LEN};
use pinc_connect::record::{self, Reach, RecordFields};
use pinc_connect::relay::datagram::Datagram;
use pinc_connect::relay::{Config, Effect, NodeState, Relay, Sink, Trace, sleep};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_700_000_000 * SEC;

fn keypair(seed: u8) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &[seed; 32]).expect("a seed makes a key")
}

fn signed_record(kp: &Keypair, home: NodeId) -> Vec<u8> {
    let mut out = vec![0u8; record::MAX_RECORD_LEN];
    let fields = RecordFields { home, seq: 1, reach: Reach::UdpBlocked, addrs: &[], hints: &[] };
    let n = record::sign(kp, &fields, &mut out).expect("a record signs");
    out.truncate(n);
    out
}

/// A store that kept one record before the start, as a relay restarted with the same identity finds it.
struct OneRecord(Vec<u8>);

impl Store for OneRecord {
    async fn load(&self) -> pinc::Result<Kept> {
        Ok(Kept { records: vec![KeptRecord { bytes: self.0.clone(), received: T0 }], mailboxes: Vec::new() })
    }
    async fn put(&self, _: &NodeId, _: &[u8], _: u64) -> pinc::Result<()> {
        Ok(())
    }
    async fn remove(&self, _: &NodeId) -> pinc::Result<()> {
        Ok(())
    }
    async fn put_mailbox(&self, _: &NodeId, _: &[u8]) -> pinc::Result<()> {
        Ok(())
    }
}

/// Expected: a node deployed from the relay binary answers a datagram from an address that proved nothing with at
/// most three times what it received. `pinc_core::ledger` (the amplification gate of a node's outgoing datagrams):
/// "for an address that is not validated the bytes charged never exceed three times the bytes received, so a spoofed
/// source gets at most three times what it sent"; `docs/proofs/properties.md` lists "reflection and amplification by
/// spoofed sources" among the attacks the design rules out, with each datagram "charged its size plus 28".
///
/// Actual: one 34-byte DNSQ datagram for a node whose record the relay holds is answered with a DNSR of 216
/// bytes, 244 charged against a bound of 186 (3 x 62). The record can be a few hundred bytes larger (addresses and
/// hints), so the factor grows to the size of the largest answer, about 1424 bytes.
///
/// Suspected fault: the relay role's UDP answers never pass the endpoint's ledger. In the relay binary's host
/// `crates/pinc/src/relay/run.rs:139` sends what `take_udp` gives directly (and `state.rs` `queue_udp` has no gate); on
/// an ordinary node that carries the relay role, `crates/pinc/src/drive/role_io.rs:156` (`role_outgoing`) does the
/// same.
///
/// Who can trigger it: an unauthenticated remote with a spoofed source address, against any node that carries the
/// relay role and holds at least one record (every hub does), in all three shapes of network.
#[test]
fn a_dns_answer_to_a_spoofed_source_is_more_than_three_times_the_query() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(amplification)
        .expect("a thread starts")
        .join()
        .expect("the check ran");
}

fn amplification() {
    let me = Identity::from_seed(&[1; 32]).expect("an identity");
    let member = keypair(3);
    let relay_id = keypair(1).node_id();
    let store = OneRecord(signed_record(&member, relay_id));

    let spoofed = SocketAddr::from((Ipv4Addr::new(198, 51, 100, 7), 40_000));
    let mut q = vec![0u8; MAX_FRAME_LEN];
    let n = Datagram::DnsQuery { peer: member.node_id() }.encode(&mut q).expect("a query encodes");
    q.truncate(n);
    let received = q.len() + 28;

    let inbox = Rc::new(RefCell::new(VecDeque::from([(q, spoofed)])));
    let sent: Rc<RefCell<Vec<(SocketAddr, usize)>>> = Rc::default();
    let (inq, out) = (Rc::clone(&inbox), Rc::clone(&sent));
    let relay = Host::builder()
        .identity(me)
        .store(store)
        .build(
            Udp::new(
                async move |buf: &mut [u8]| {
                    let next = inq.borrow_mut().pop_front();
                    match next {
                        Some((b, from)) => {
                            buf[..b.len()].copy_from_slice(&b);
                            Ok((b.len(), from))
                        },
                        None => pending().await,
                    }
                },
                async move |pkt: &[u8], to: SocketAddr| {
                    out.borrow_mut().push((to, pkt.len()));
                    Ok(pkt.len())
                },
            ),
            CarrierFns::new(
                async || pending::<pinc::Result<((), CarrierKind)>>().await,
                async |_: &Peer, _: CarrierKind| Err::<(), _>(Error::new(ErrorKind::Unreachable, "no carriers")),
                async |_: &(), b: Vec<u8>| {
                    pending::<()>().await;
                    (Ok(0), b)
                },
                async |_: &(), b: Vec<u8>, _: usize| {
                    pending::<()>().await;
                    (Ok(0), b)
                },
                async |_: ()| {},
            ),
            Clock::new(|| T0, async |_: u64| pending::<()>().await),
        )
        .expect("the relay builds");

    // A bounded number of polls with a no-op waker: the host's I/O is all in memory and ready at once.
    let mut run = pin!(relay.run());
    let mut cx = Context::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(r) = run.as_mut().poll(&mut cx) {
            panic!("the run ended: {r:?}");
        }
        if inbox.borrow().is_empty() && !sent.borrow().is_empty() {
            break;
        }
    }
    let to_spoofed: usize = sent.borrow().iter().filter(|(to, _)| *to == spoofed).map(|(_, n)| n + 28).sum();
    assert!(to_spoofed > 0, "the relay answered the query: {:?}", sent.borrow());
    assert!(
        to_spoofed <= 3 * received,
        "{to_spoofed} bytes charged to {spoofed}, which proved nothing, for one datagram of {received} (at most {})",
        3 * received
    );
}

#[derive(Default)]
struct Closes(Vec<(NodeId, bool)>);

impl Sink for Closes {
    fn emit(&mut self, effect: Effect<'_>) {
        if let Effect::Trace(Trace::CarrierClosed { node, asleep }) = effect {
            self.0.push((node, asleep));
        }
    }
}

/// Expected: a node that sends its sleep notice and then loses its carrier is suspended, whatever other nodes did
/// before. `relay::clients` (module doc): "When a carrier closes the node becomes \"gone\" with the time; if its sleep
/// notice came within [`super::rule::SLEEP_WIN_NS`] before, the close is a suspension, not a crash"; `pinc-node`'s
/// `relay_trace` acts on it: "a sleep notice before a close means a suspension, not a failure".
///
/// Actual: once `C` other nodes closed within `GONE_TTL` (600 s), the table of gone nodes is full; the next close is
/// not recorded, `node_state` says `Unknown` and the close is traced with `asleep: false`, so the hub's membership
/// takes the suspension for a failure. A notice sent just after the close is refused as from an unknown node.
///
/// Suspected fault: `crates/pinc-connect/src/relay/clients.rs:116` (`let _ = self.gone.insert(*node, now)`) drops the
/// close when the table is full, and the sweep (`clients.rs:338`) does the same for an expired session.
///
/// Who can trigger it: any node that can open a carrier (an identity costs nothing), by opening and closing `C`
/// carriers under fresh identities within 600 s (1024 on the relay binary), or ordinary churn on a busy node that
/// carries the relay role. Every honest suspension after that, for 600 s, is reported as a crash.
#[test]
fn a_suspension_after_a_full_table_of_gone_nodes_is_taken_for_a_crash() {
    let me = keypair(10);
    let mut relay: Box<Relay<2, 3, 2, 1600>> = Box::new(Relay::new(Config::new(me.node_id(), 7)));
    let mut sink = Closes::default();
    let mut now = T0;
    for seed in [1, 2] {
        let node = keypair(seed).node_id();
        let sid = relay.carrier_opened(now, node, &mut sink).expect("a carrier opens");
        relay.carrier_closed(now, &node, sid, &mut sink);
        now += SEC;
    }

    let sleeper = keypair(3);
    let node = sleeper.node_id();
    let sid = relay.carrier_opened(now, node, &mut sink).expect("a carrier opens");
    let mut notice = vec![0u8; sleep::MAX_LEN];
    let n = sleep::sign(&sleeper, &me.node_id(), now / 1_000_000, &mut notice).expect("a notice signs");
    relay
        .carrier_frame(now, &node, sid, &Frame::Sleep { notice: &notice[..n] }, &mut sink)
        .expect("the notice is taken");
    now += SEC;
    relay.carrier_closed(now, &node, sid, &mut sink);

    assert_eq!(sink.0.last(), Some(&(node, true)), "the close of the node that sent its notice is a suspension");
    assert_eq!(relay.node_state(&node), NodeState::Gone { since: now, asleep: true });
}
