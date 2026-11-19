//! The server: requests, refusals, supersession, the serve batch and the range proofs of write-through.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    clippy::unreadable_literal,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use values_support::*;
use pinc_dag::tree::{Layout, PARENT_LEN};
use pinc_transport::frame::ext;
use pinc_values::knobs::{GROUP_LOG, code};
use pinc_values::plan::Plan;
use pinc_values::server::{Server, ServerIn};
use pinc_values::session::Provider;
use pinc_values::span::Span;
use pinc_values::trace::Trace;
use pinc_values::wire::{ProofFrame, ProofReq, Req};

const PEER: Provider = Provider(7);

struct Rig {
    server: Server<PStore, 4>,
    sess: ServerSession,
    rec: Rec,
    store: PStore,
}

impl Rig {
    fn new(len: usize) -> Self {
        let store = PStore::random(5, len);
        Self {
            server: Server::new(store.clone()),
            sess: ServerSession::default(),
            rec: Rec::default(),
            store,
        }
    }

    fn ev(&mut self, ev: &ServerIn<'_>) {
        self.server.on_event(&mut self.sess, &mut self.rec, 0, ev);
    }

    fn open(&mut self, stream: u64, peer: Provider, bytes: &[u8]) {
        self.sess.reqs.insert(stream, bytes.to_vec());
        self.ev(&ServerIn::Opened { stream, peer });
        self.ev(&ServerIn::Readable(stream));
    }

    fn req(root: [u8; 32], spans: &[Span]) -> Vec<u8> {
        let mut b = [0u8; 600];
        let n = Req::encode(&root, spans, &mut b).unwrap();
        b[..n].to_vec()
    }

    fn resets(&self) -> Vec<(u64, u64)> {
        self.sess
            .out
            .iter()
            .filter_map(|m| {
                if let ToClient::Reset(s, c) = m {
                    Some((*s, *c))
                } else {
                    None
                }
            })
            .collect()
    }
}

#[test]
fn a_valid_request_is_served_through_a_source_and_consumed() {
    let mut r = Rig::new(100_000);
    let spans = [Span { off: 10, len: 50_000 }];
    let req = Rig::req(r.store.root(), &spans);
    r.open(1, PEER, &req);
    assert_eq!(r.sess.installs.len(), 1);
    let (stream, _, len) = &r.sess.installs[0];
    assert_eq!(*stream, 1);
    assert_eq!(*len, Plan::new(100_000, &spans).unwrap().total());
    assert_eq!(r.sess.consumed.get(&1), Some(&(req.len() as u64)));
    assert!(r.resets().is_empty());
    assert!(r.rec.traces.iter().any(|(_, t)| matches!(
        t,
        Trace::Serving {
            stream: 1,
            ranges: 1,
            ..
        }
    )));
    assert_eq!(r.server.held(), 1);
}

#[test]
fn a_request_in_single_bytes_is_collected_and_served_once() {
    let mut r = Rig::new(40_000);
    let req = Rig::req(r.store.root(), &[Span { off: 0, len: 40_000 }, Span { off: 5, len: 5 }]);
    r.sess.reqs.insert(1, Vec::new());
    r.ev(&ServerIn::Opened { stream: 1, peer: PEER });
    for b in &req {
        r.sess.reqs.get_mut(&1).unwrap().push(*b);
        assert!(r.sess.installs.is_empty());
        r.ev(&ServerIn::Readable(1));
        if r.sess.reqs[&1].len() < req.len() {
            assert!(r.resets().is_empty());
        }
    }
    assert_eq!(r.sess.installs.len(), 1);
}

#[test]
fn refusals_carry_the_reason() {
    // An unknown value, a range past the end, a malformed request, bytes after the request.
    let mut r = Rig::new(10_000);
    let root = r.store.root();
    r.open(1, PEER, &Rig::req([9; 32], &[Span { off: 0, len: 1 }]));
    r.open(2, PEER, &Rig::req(root, &[Span { off: 9_999, len: 2 }]));
    let mut bad = Rig::req(root, &[]);
    bad[0] = 9;
    r.open(3, PEER, &bad);
    let mut extra = Rig::req(root, &[Span { off: 0, len: 5 }]);
    extra.push(0);
    r.open(4, PEER, &extra);
    assert_eq!(
        r.resets(),
        vec![
            (1, code::UNAVAILABLE),
            (2, code::UNAVAILABLE),
            (3, code::PROTOCOL),
            (4, code::PROTOCOL)
        ]
    );
    assert!(r.sess.installs.is_empty());
    assert_eq!(r.server.held(), 0, "refused requests free their slots");
}

#[test]
fn an_empty_request_gets_an_empty_response() {
    let mut r = Rig::new(10_000);
    r.open(1, PEER, &Rig::req(r.store.root(), &[]));
    assert_eq!(r.sess.installs[0].2, 0);
    let mut r2 = Rig::new(10_000);
    r2.open(1, PEER, &Rig::req(r2.store.root(), &[Span { off: 3, len: 0 }]));
    assert_eq!(r2.sess.installs[0].2, 0);
}

#[test]
fn the_server_holds_at_most_its_slots_and_says_busy() {
    let mut r = Rig::new(10_000);
    let req = Rig::req(r.store.root(), &[Span { off: 0, len: 10 }]);
    for s in 1..=4 {
        r.open(s, Provider(s as u32), &req);
    }
    r.open(5, Provider(9), &req);
    assert_eq!(r.resets(), vec![(5, code::BUSY)]);
    assert_eq!(r.server.held(), 4);
    r.ev(&ServerIn::Reset(2));
    assert_eq!(r.server.held(), 3);
    r.open(6, Provider(9), &req);
    assert_eq!(r.resets().len(), 1, "a freed slot takes the next request");
    r.ev(&ServerIn::Closed(Provider(1)));
    assert_eq!(r.server.held(), 3);
}

#[test]
fn a_newer_overlapping_request_supersedes_the_older_one_of_the_same_peer_only() {
    let mut r = Rig::new(200_000);
    let root = r.store.root();
    r.open(1, PEER, &Rig::req(root, &[Span { off: 0, len: 100_000 }]));
    r.open(2, Provider(8), &Rig::req(root, &[Span { off: 0, len: 100_000 }]));
    assert!(r.resets().is_empty());
    // The same peer asks again for bytes overlapping its first request: the first is reset.
    r.open(
        3,
        PEER,
        &Rig::req(
            root,
            &[Span {
                off: 90_000,
                len: 50_000,
            }],
        ),
    );
    assert_eq!(r.resets(), vec![(1, code::SUPERSEDED)]);
    // A request for other bytes of the same peer leaves the others alone.
    r.open(4, PEER, &Rig::req(root, &[Span { off: 190_000, len: 10 }]));
    assert_eq!(r.resets().len(), 1);
    assert_eq!(r.server.held(), 3);
}

#[test]
fn a_refused_newer_request_leaves_the_older_response_alone() {
    let mut r = Rig::new(200_000);
    let root = r.store.root();
    r.open(1, PEER, &Rig::req(root, &[Span { off: 0, len: 100_000 }]));
    // The session has no room for the newer response: the request is refused and the older response keeps running.
    r.sess.refuse_serve = true;
    r.open(
        2,
        PEER,
        &Rig::req(
            root,
            &[Span {
                off: 90_000,
                len: 50_000,
            }],
        ),
    );
    assert_eq!(r.resets(), vec![(2, code::UNAVAILABLE)]);
    assert_eq!(r.server.held(), 1);
    // Once it can be accepted, the newer request supersedes the older one.
    r.sess.refuse_serve = false;
    r.open(
        3,
        PEER,
        &Rig::req(
            root,
            &[Span {
                off: 90_000,
                len: 50_000,
            }],
        ),
    );
    assert_eq!(r.resets(), vec![(2, code::UNAVAILABLE), (1, code::SUPERSEDED)]);
    assert_eq!(r.server.held(), 1);
}

fn proofs(r: &Rig) -> Vec<(u64, Vec<u8>)> {
    r.sess
        .out
        .iter()
        .filter_map(|m| {
            if let ToClient::Ext(s, ty, b) = m {
                (*ty == ext::PROOF).then(|| (*s, b.clone()))
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn a_proof_request_is_answered_with_the_outboard_pairs_of_each_range() {
    let len = 64 * 16384;
    let mut r = Rig::new(len);
    r.open(
        1,
        PEER,
        &Rig::req(
            r.store.root(),
            &[Span {
                off: 0,
                len: len as u64,
            }],
        ),
    );
    let mut body = [0u8; 32];
    let n = ProofReq {
        sid: 1,
        from: 3 * 16384,
        upto: 30 * 16384,
    }
    .encode(&mut body)
    .unwrap();
    r.ev(&ServerIn::Ext {
        ty: ext::PROOF_REQ,
        body: &body[..n],
    });
    let frames = proofs(&r);
    assert!(!frames.is_empty());
    let layout = Layout::new(len as u64, GROUP_LOG).unwrap();
    // Frames are cut at multiples of 16 groups so each is a subtree; the first covers the group asked for.
    let mut next = 0;
    for (sid, b) in &frames {
        let pf = ProofFrame::parse(b).unwrap();
        assert_eq!((*sid, pf.sid, u32::from(pf.glog), pf.ln), (1, 1, GROUP_LOG, len as u64));
        assert_eq!(pf.start, next, "frames tile from the block of the request");
        assert!(pf.wn <= 16 * 16384 && pf.start.is_multiple_of(16384));
        let a = pf.start / 16384;
        let pairs = pinc_values::plan::range_pairs(layout.groups(), a, (pf.start + u64::from(pf.wn)).div_ceil(16384));
        assert_eq!(pf.proof.len() as u64, pairs * PARENT_LEN as u64);
        next = pf.start + u64::from(pf.wn);
        // The pairs are the outboard's, in pre-order: the first is the root's when the range starts the tree path.
        for (i, pair) in pf.proof.chunks(PARENT_LEN).enumerate() {
            assert!(
                r.store
                    .0
                    .outboard
                    .windows(PARENT_LEN)
                    .step_by(PARENT_LEN)
                    .any(|p| p == pair),
                "pair {i} is not in the outboard"
            );
        }
    }
    assert!(next >= 30 * 16384);
    assert!(
        r.rec
            .traces
            .iter()
            .any(|(_, t)| matches!(t, Trace::ProofSent { stream: 1, .. }))
    );
    // Asking again for the same region sends nothing new.
    let before = r.sess.out.len();
    r.ev(&ServerIn::Ext {
        ty: ext::PROOF_REQ,
        body: &body[..n],
    });
    assert_eq!(r.sess.out.len(), before);
}

#[test]
fn a_proof_request_near_the_top_of_the_offset_range_is_bounded_not_wrapped() {
    // `upto` is peer-controlled: the end of the proofs must saturate, never overflow (a debug-build panic, a wrap in release).
    let len = 64 * 16384;
    let mut r = Rig::new(len);
    r.open(
        1,
        PEER,
        &Rig::req(
            r.store.root(),
            &[Span {
                off: 0,
                len: len as u64,
            }],
        ),
    );
    for upto in [u64::MAX, u64::MAX - 16383, u64::MAX - 16384] {
        let mut body = [0u8; 32];
        let n = ProofReq { sid: 1, from: 0, upto }.encode(&mut body).unwrap();
        r.ev(&ServerIn::Ext {
            ty: ext::PROOF_REQ,
            body: &body[..n],
        });
    }
    let frames = proofs(&r);
    assert!(!frames.is_empty(), "the request is served as far as the value goes");
    let mut next = 0;
    for (_, b) in &frames {
        let pf = ProofFrame::parse(b).unwrap();
        assert_eq!(pf.start, next);
        next = pf.start + u64::from(pf.wn);
    }
    assert_eq!(next, len as u64, "proofs stop at the end of the value");
}

#[test]
fn a_loss_arms_proofs_from_the_lost_group_to_a_window_past_the_frontier() {
    let len = 64 * 16384;
    let mut r = Rig::new(len);
    let spans = [Span {
        off: 0,
        len: len as u64,
    }];
    r.open(1, PEER, &Rig::req(r.store.root(), &spans));
    let plan = Plan::new(len as u64, &spans).unwrap();
    let lost = plan.frame(0, 10).unwrap();
    let sent = plan.frame(0, 20).unwrap().start;
    r.ev(&ServerIn::Loss {
        stream: 1,
        offset: lost.data_start() + 5,
        sent,
        window: 8 * 16384,
    });
    let frames = proofs(&r);
    assert!(!frames.is_empty());
    let first = ProofFrame::parse(&frames[0].1).unwrap();
    assert_eq!(first.start, 0, "the block of 16 groups holding the lost group");
    let last = ProofFrame::parse(&frames.last().unwrap().1).unwrap();
    assert!(
        last.start + u64::from(last.wn) >= 20 * 16384 + 8 * 16384,
        "proofs reach a window beyond the sent frontier"
    );
    // Once armed, progress of the stream sends proofs ahead of the data.
    let before = frames.len();
    let beyond = plan.frame(0, 45).unwrap().start;
    r.ev(&ServerIn::Sent {
        stream: 1,
        sent: beyond,
        window: 64 * 1024,
    });
    assert!(proofs(&r).len() > before);
}

#[test]
fn proofs_are_not_sent_for_a_stream_that_never_lost_or_asked() {
    let len = 64 * 16384;
    let mut r = Rig::new(len);
    r.open(
        1,
        PEER,
        &Rig::req(
            r.store.root(),
            &[Span {
                off: 0,
                len: len as u64,
            }],
        ),
    );
    r.ev(&ServerIn::Sent {
        stream: 1,
        sent: 30_000,
        window: 64 * 1024,
    });
    assert!(proofs(&r).is_empty());
}

#[test]
fn junk_extension_frames_and_unknown_streams_are_ignored() {
    let mut r = Rig::new(100_000);
    r.ev(&ServerIn::Ext {
        ty: ext::PROOF_REQ,
        body: &[1, 2, 3],
    });
    r.ev(&ServerIn::Ext {
        ty: 0x99,
        body: &[0; 20],
    });
    let mut body = [0u8; 32];
    let n = ProofReq {
        sid: 77,
        from: 0,
        upto: 100,
    }
    .encode(&mut body)
    .unwrap();
    r.ev(&ServerIn::Ext {
        ty: ext::PROOF_REQ,
        body: &body[..n],
    });
    r.ev(&ServerIn::Loss {
        stream: 5,
        offset: 0,
        sent: 1,
        window: 1,
    });
    r.ev(&ServerIn::Sent {
        stream: 5,
        sent: 1,
        window: 1,
    });
    r.ev(&ServerIn::Readable(5));
    assert!(r.sess.out.is_empty() && r.resets().is_empty());
}

#[test]
fn a_finished_response_frees_its_slot() {
    let mut r = Rig::new(10_000);
    let req = Rig::req(r.store.root(), &[Span { off: 0, len: 10 }]);
    for round in 0..20u64 {
        r.open(round + 1, Provider(round as u32), &req);
        assert_eq!(r.server.held(), 1);
        r.ev(&ServerIn::Done(round + 1));
        assert_eq!(r.server.held(), 0);
    }
    assert!(
        r.resets().is_empty(),
        "a server that frees finished responses is never busy"
    );
}
