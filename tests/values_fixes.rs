//! Regression tests of four corrections to the value fetch: the HEAD_HOLD tail threshold, a granule announced once
//! when two streams race on it, the stall timer armed by the first request, and a wrong out-of-band proof frame that
//! evicts its provider. (The fifth, supersession, is in `values_server`.) Each fails with its correction reverted.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use std::collections::HashMap;

use pinc_transport::frame::ext;
use pinc_transport::stream::{StreamId, StreamSource};
use pinc_values::fetch::{Fetch, FetchSpec, In, Io};
use pinc_values::plan::Plan;
use pinc_values::session::{OpenError, Outbound, PeerInfo, Provider, Session};
use pinc_values::source::ValueSource;
use pinc_values::span::Span;
use pinc_values::trace::{Event, LiarWhy, Release, Trace};
use pinc_values::wire::ProofFrame;
use values_support::*;

const G: u64 = GROUP;

fn releases(sim: &Sim) -> Vec<(u64, Release)> {
    sim.rec
        .traces_of(|t| {
            if let Trace::Released { off, why } = t {
                Some((*off, *why))
            } else {
                None
            }
        })
        .into_iter()
        .map(|(_, r)| r)
        .collect()
}

/// The wanted ranges end at the end of the last range, not at the first offset plus the bytes wanted: with the group
/// between the two ranges already stored, the first granule is not released as the tail while the second is missing.
#[test]
fn head_hold_tail_is_the_end_of_the_wanted_ranges() {
    let store = PStore::random(61, 4 * G as usize);
    let seeded = ClientStore::seeded(store.content(), &[G..2 * G]);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 2000)], seeded);
    let ps = sim.all_providers();
    sim.start_with(&[Span { off: 0, len: G }, Span { off: 2 * G, len: G }], &ps, None);
    sim.run(30);
    let offs: Vec<u64> = sim.rec.readable().iter().map(|e| e.1).collect();
    assert_eq!(offs, vec![2 * G, 0], "the first granule waits for the last wanted one");
    assert_eq!(releases(&sim), vec![(0, Release::Tail)]);
    assert!(sim.rec.complete());
}

/// A session of canned responses: each stream shows `avail` bytes of its response.
#[derive(Default)]
struct Canned {
    resp: HashMap<StreamId, Vec<u8>>,
    avail: HashMap<StreamId, u64>,
    next: StreamId,
}

impl Session for Canned {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        let (Some(b), Some(&a)) = (self.resp.get(&stream), self.avail.get(&stream)) else {
            return;
        };
        if from < a {
            f(&b[from as usize..a as usize]);
        }
    }
    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        self.avail.get(&stream).is_some_and(|&a| from + len <= a)
    }
    fn consume(&mut self, _: StreamId, _: u64) {}
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        true
    }
    fn reset(&mut self, _: StreamId, _: u64) {}
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Outbound for Canned {
    fn is_connected(&self, _: Provider) -> bool {
        true
    }
    fn dial(&mut self, _: Provider) {}
    fn hangup(&mut self, _: Provider) {}
    fn open_stream(&mut self, _: Provider, _: u8) -> Result<StreamId, OpenError> {
        self.next += 1;
        Ok(self.next)
    }
    fn peer_info(&self, _: Provider) -> Option<PeerInfo> {
        None
    }
}

/// Two streams of one provider carry the same group; one finishes it while the other is still inside it. The group
/// is announced once.
#[test]
fn a_granule_two_streams_race_on_is_announced_once() {
    let len = 3 * G;
    let store = PStore::random(62, len as usize);
    let plan = Plan::new(len, &[Span { off: 0, len }]).unwrap();
    let mut src = ValueSource::new(store.clone(), store.root(), plan.clone());
    let mut resp = vec![0u8; plan.total() as usize];
    assert_eq!(src.read_at(0, &mut resp), resp.len());
    let f1 = plan.frame(0, 1).unwrap();

    let mut net = Canned::default();
    let mut cst = ClientStore::new();
    let mut rec = Rec::default();
    let mut fetch = Fetch::new();
    let p = Provider(0);
    macro_rules! io {
        () => {
            Io {
                session: &mut net,
                store: &mut cst,
                out: &mut rec,
            }
        };
    }
    let spec = FetchSpec {
        root: store.root(),
        length: len,
        ranges: &[],
        providers: &[p],
        deadline: None,
    };
    fetch.start(&mut io!(), 0, &spec).unwrap();
    // The session comes up twice (a redial racing the first): two streams ask for the same bytes.
    fetch.on_event(&mut io!(), 1, &In::Connected(p));
    fetch.on_event(&mut io!(), 2, &In::Connected(p));
    net.resp.insert(1, resp.clone());
    net.resp.insert(2, resp);
    for (stream, upto) in [(2, f1.data_start() + 100), (1, f1.end()), (2, f1.end())] {
        net.avail.insert(stream, upto);
        fetch.on_event(&mut io!(), 3, &In::Readable { stream, bytes: 1 });
    }
    let again = rec.readable().iter().filter(|e| e.1 == G).count();
    assert_eq!(again, 1, "the raced granule was announced {again} times");
    assert!(!rec.events.iter().any(|(_, e)| matches!(e, Event::Failed(_))));
    cst.assert_verified_is_true(store.content());
}

/// The stall rule starts at the first verified granule: a fetch that has not received one is not redialled by it,
/// however long the provider stays silent (a slow link may still be sending the first granule).
#[test]
fn a_fetch_with_no_verified_granule_yet_is_not_redialled_by_the_stall_rule() {
    let store = PStore::random(63, 2 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000).stall_after(0)], ClientStore::new());
    sim.start();
    sim.run_until(60 * SEC, |_| false);
    assert!(
        !sim.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::StallRedial { .. })),
        "a fetch that never received a granule was redialled"
    );
}

/// A PROOF frame that does not fit the value evicts the provider whose stream it names.
#[test]
fn a_wrong_proof_frame_evicts_its_provider() {
    let store = PStore::random(64, 8 << 20);
    let mut sim = Sim::new(
        vec![ProvCfg::new(store.clone(), 400), ProvCfg::new(store.clone(), 400)],
        ClientStore::new(),
    );
    sim.start();
    sim.run_until(SEC, |s| {
        s.rec
            .traces
            .iter()
            .filter(|(_, t)| matches!(t, Trace::Requested { .. }))
            .count()
            >= 2
    });
    let (victim, stream) = sim.rec.traces_of(|t| {
        if let Trace::Requested { provider, stream, .. } = t {
            Some((*provider, *stream))
        } else {
            None
        }
    })[0]
        .1;
    // A well-formed head for a value one byte longer than the one fetched.
    let mut body = [0u8; 64];
    let n = ProofFrame::write_head(stream, 4, 0, 4 * G as u32, store.len() + 1, &mut body).unwrap();
    let mut io = Io {
        session: &mut sim.sess,
        store: &mut sim.store,
        out: &mut sim.rec,
    };
    sim.fetch.on_event(
        &mut io,
        sim.now,
        &In::Ext {
            ty: ext::PROOF,
            body: &body[..n],
        },
    );
    let liars = sim.rec.traces_of(|t| {
        if let Trace::Liar { provider, why } = t {
            Some((*provider, *why))
        } else {
            None
        }
    });
    assert_eq!(
        liars.iter().map(|l| l.1).collect::<Vec<_>>(),
        vec![(victim, LiarWhy::Protocol)]
    );
    // The other provider finishes the fetch.
    sim.run(120);
    assert!(sim.rec.complete());
    sim.store.assert_verified_is_true(store.content());
}
