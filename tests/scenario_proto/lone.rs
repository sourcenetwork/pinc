//! One stack on a bare host, driven event by event: the checks that need a hand-made byte stream (a forged creator,
//! a corrupted body, a malformed frame) and the timers that need an exact clock.

use std::cell::RefCell;
use std::rc::Rc;

use pinc_core::SessionId;
use pinc_sim::suite::crypto::{MsgId, PayloadKind, Registry};
use pinc_sim::suite::proto::body::{self, Verdict, render};
use pinc_sim::suite::proto::frame::{Frame, Framer, T_ACK, T_ECHO, T_PUSH, T_REQ, T_RESP, hdr};
use pinc_sim::suite::proto::host::{LayerEvent, Layers};
use pinc_sim::suite::proto::{ALPN_DOCSYNC, ALPN_ECHO, ALPN_MANAGE, ALPN_PUSHLOG, Durable, MsgIntents, Stack};
use pinc_sim::suite::rec::{IntentMeta, MustArg, NS, Rec};
use pinc_sim::suite::world::model::{IntentKind, World};

use crate::net::{TestHost, allow, base_intent, new_world};

pub struct Env {
    pub world: Rc<World>,
    pub rec: Rc<RefCell<Rec>>,
    pub reg: &'static Registry,
    pub shared: MsgIntents,
}

pub struct Lone {
    pub stack: Stack,
    pub host: TestHost,
    pub now: u64,
    pub durable: Rc<RefCell<Durable>>,
}

impl Env {
    pub fn new(world: World) -> Self {
        let world = Rc::new(world);
        let rec = Rc::new(RefCell::new(Rec::new(world.clone())));
        Self {
            world,
            rec,
            reg: Registry::leak(11),
            shared: MsgIntents::default(),
        }
    }

    pub fn node(&self, idx: usize, build: impl FnOnce(Stack) -> Stack) -> Lone {
        let durable = Rc::new(RefCell::new(Durable::sharing(self.shared.clone())));
        self.node_on(idx, durable, build)
    }

    pub fn node_on(&self, idx: usize, durable: Rc<RefCell<Durable>>, build: impl FnOnce(Stack) -> Stack) -> Lone {
        let stack = build(Stack::new(idx, self.world.clone(), self.rec.clone(), durable.clone()));
        Lone {
            stack,
            host: TestHost::new(idx, self.reg, usize::MAX),
            now: 5 * NS,
            durable,
        }
    }

    pub fn violations(&self) -> Vec<(String, String)> {
        self.rec
            .borrow()
            .violations
            .iter()
            .map(|v| (v.gate.clone(), v.msg.clone()))
            .collect()
    }

    /// A message by `creator` of `len` bytes, and its bytes.
    pub fn message(&self, creator: usize, len: u64) -> (MsgId, Vec<u8>) {
        let m = self.reg.new_msg(creator, PayloadKind::Msg, len);
        (m, render(self.reg, m, len))
    }
}

pub const S: SessionId = SessionId(1);

impl Lone {
    pub fn boot(&mut self) {
        self.stack.boot(self.now, &mut self.host);
    }

    pub fn ev(&mut self, e: LayerEvent<'_>) {
        self.stack.event(self.now, &mut self.host, e);
    }

    pub fn incoming(&mut self, peer: usize, alpn: &'static [u8]) {
        self.ev(LayerEvent::Incoming { session: S, peer, alpn });
        self.ev(LayerEvent::StreamOpened { session: S, stream: 1 });
    }

    pub fn data(&mut self, bytes: &[u8], fin: bool) {
        self.ev(LayerEvent::StreamData {
            session: S,
            stream: 1,
            data: bytes,
            fin,
        });
    }

    /// Everything the stack has written, parsed into frames.
    pub fn written(&self) -> Vec<Frame> {
        let mut out = Vec::new();
        Framer::new().feed(&self.host.pending_bytes(), &mut out).unwrap();
        out
    }

    pub fn clear_written(&mut self) {
        self.host.pipes.clear();
    }
}

pub fn frame(ty: u8, id: u64, body: &[u8]) -> Vec<u8> {
    let mut f = hdr(ty, body.len(), id).to_vec();
    f.extend_from_slice(body);
    f
}

fn gate(env: &Env) -> Vec<(String, String)> {
    env.violations()
}

fn sec(alpn: &str) -> (String, String) {
    (
        "G-SEC".into(),
        format!("{alpn} message accepted from a principal other than the session peer"),
    )
}

/// A push intent of node `origin` for `rep` whose message is delivered to the intent on arrival.
fn registered_push(env: &Env, origin: usize, rep: usize, len: u64) -> (MsgId, Vec<u8>, u32) {
    let (m, bytes) = env.message(origin, len);
    let iid = env.rec.borrow_mut().intent(
        IntentKind::Push,
        origin,
        0,
        Some(100 * NS),
        &[rep],
        len,
        MustArg::Flag(true),
        IntentMeta::default(),
    );
    env.shared.borrow_mut().insert(m.0, iid);
    (m, bytes, iid)
}

#[test]
fn a_push_from_the_wrong_creator_is_a_security_violation_and_is_not_delivered() {
    let env = Env::new(new_world(3));
    allow(&env.rec, 0, 1);
    let mut r = env.node(0, |s| s);
    r.boot();
    r.incoming(1, ALPN_PUSHLOG);
    // node 2 wrote it, node 1 sends it
    let (_, bytes, _) = registered_push(&env, 2, 0, 200);
    r.data(&frame(T_PUSH, 1, &bytes), false);
    assert_eq!(gate(&env), [sec("/defra/pushlog/1")]);
    assert!(env.rec.borrow().pushlog_order.is_empty());
    assert!(env.rec.borrow().intents[&1].delivered.is_empty());
    assert!(r.host.pending_bytes().is_empty(), "a refused push is not acknowledged");
    assert_eq!(r.durable.borrow().pl_in.get(&1), None);
}

#[test]
fn a_push_from_the_right_creator_is_delivered_acknowledged_and_checked_for_access() {
    let env = Env::new(new_world(3));
    let mut r = env.node(0, |s| s);
    r.boot();
    r.incoming(1, ALPN_PUSHLOG);
    let (_, bytes, iid) = registered_push(&env, 1, 0, 200);
    r.data(&frame(T_PUSH, 1, &bytes), false);
    // no oracle answer was given: the delivery is recorded, and so is the missing allow
    let v = env.violations();
    assert_eq!(v.len(), 1);
    assert_eq!(v[0].0, "G-ACP");
    {
        let rec = env.rec.borrow();
        assert_eq!(rec.intents[&iid].delivered.keys().copied().collect::<Vec<_>>(), [0]);
        assert_eq!(rec.pushlog_order[&(1, 0)], [1]);
        assert_eq!(rec.app_bytes, 200);
    }
    let w = r.written();
    assert_eq!(
        w,
        [Frame {
            ty: T_ACK,
            id: 1,
            body: None
        }]
    );
}

#[test]
fn push_gap_delivers_and_records_an_order_violation_and_old_sequences_are_only_acknowledged() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let mut r = env.node(0, |s| s);
    r.boot();
    r.incoming(1, ALPN_PUSHLOG);
    let (_, b3, _) = registered_push(&env, 1, 0, 100);
    r.data(&frame(T_PUSH, 3, &b3), false);
    assert_eq!(
        gate(&env),
        [("G-ORDER".into(), "PUSHLOG gap: expected seq 1, got 3".into())]
    );
    assert_eq!(env.rec.borrow().pushlog_order[&(1, 0)], [3]);
    // sequence 2 is now old: acknowledged with the high-water mark, never delivered
    let (_, b2, _) = registered_push(&env, 1, 0, 100);
    r.data(&frame(T_PUSH, 2, &b2), false);
    assert_eq!(env.rec.borrow().pushlog_order[&(1, 0)], [3]);
    let ids: Vec<u64> = r.written().iter().map(|f| f.id).collect();
    assert_eq!(ids, [3, 3]);
    assert_eq!(gate(&env).len(), 1);
}

#[test]
fn a_corrupted_or_cut_push_body_is_an_integrity_violation() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let mut r = env.node(0, |s| s);
    r.boot();
    r.incoming(1, ALPN_PUSHLOG);
    let (_, mut bytes, iid) = registered_push(&env, 1, 0, 300);
    let last = bytes.len() - 1;
    bytes[last] ^= 1;
    r.data(&frame(T_PUSH, 1, &bytes), false);
    assert_eq!(
        gate(&env),
        [(
            "G-INT".into(),
            "PUSHLOG push delivered corrupted or foreign bytes".into()
        )]
    );
    let (_, bytes, _) = registered_push(&env, 1, 0, 300);
    r.data(&frame(T_PUSH, 2, &bytes[..100]), false);
    assert_eq!(
        gate(&env)[1],
        ("G-INT".into(), "PUSHLOG push delivered a partial message".into())
    );
    assert!(env.rec.borrow().pushlog_order.is_empty());
    assert!(env.rec.borrow().intents[&iid].delivered.is_empty());
}

#[test]
fn a_request_from_the_wrong_creator_is_refused_and_a_right_one_is_answered() {
    for (alpn, name) in [(ALPN_DOCSYNC, "/defra/docsync/1"), (ALPN_MANAGE, "/defra/manage/1")] {
        let env = Env::new(new_world(3));
        let mut s = env.node(0, |s| s);
        s.boot();
        s.incoming(1, alpn);
        let (_, forged) = env.message(2, 120);
        s.data(&frame(T_REQ, (7 << 24) | 500, &forged), true);
        assert_eq!(gate(&env), [sec(name)], "{name}");
        assert!(s.host.pending_bytes().is_empty(), "no answer to a forged request");

        let (_, honest) = env.message(1, 120);
        s.data(&frame(T_REQ, (7 << 24) | 500, &honest), true);
        assert_eq!(gate(&env).len(), 1);
        let w = s.written();
        assert_eq!(w.len(), 1);
        assert_eq!((w[0].ty, w[0].id), (T_RESP, 7));
        let b = w[0].body.as_deref().unwrap();
        assert_eq!(b.len(), 500);
        let m = body::message_id(b).unwrap();
        assert_eq!(env.reg.creator_of(m), Some(0), "the server wrote the answer");
        assert_eq!(body::verify(env.reg, m, b), Verdict::Whole);
        assert!(s.host.pipes.values().all(|p| p.fin), "the answer ends the stream");
    }
}

#[test]
fn a_response_from_the_wrong_creator_is_refused_and_the_request_stays_open() {
    let env = Env::new(new_world(3));
    allow(&env.rec, 0, 1);
    let mut c = env.node(0, |s| s);
    c.boot();
    let mut d = base_intent(0, IntentKind::Docsync);
    d.to = Some(1);
    c.stack.intent(c.now, &mut c.host, &d);
    c.ev(LayerEvent::Connected {
        session: S,
        peer: 1,
        alpn: ALPN_DOCSYNC,
    });
    let stream = *c.host.pipes.keys().next().map(|(_, s)| s).unwrap();
    let (_, forged) = env.message(2, 2048);
    c.ev(LayerEvent::StreamData {
        session: S,
        stream,
        data: &frame(T_RESP, 1, &forged),
        fin: false,
    });
    assert_eq!(gate(&env), [sec("/defra/docsync/1")]);
    assert!(env.rec.borrow().intents[&1].delivered.is_empty());
    // still in flight: when the connection closes it is asked again
    c.ev(LayerEvent::Closed { session: S });
    assert!(
        c.host.connects.len() >= 2,
        "a closed connection with a request in flight dials again"
    );
}

fn manage_client(env: &Env) -> (Lone, u64) {
    let mut c = env.node(0, |s| s);
    c.boot();
    let mut d = base_intent(0, IntentKind::Manage);
    d.to = Some(1);
    d.resp = Some(300);
    c.stack.intent(c.now, &mut c.host, &d);
    c.ev(LayerEvent::Connected {
        session: S,
        peer: 1,
        alpn: ALPN_MANAGE,
    });
    let stream = *c.host.pipes.keys().next().map(|(_, s)| s).unwrap();
    (c, stream)
}

#[test]
fn a_response_from_the_session_peer_completes_the_request() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let (mut c, stream) = manage_client(&env);
    let (_, ok) = env.message(1, 300);
    c.ev(LayerEvent::StreamData {
        session: S,
        stream,
        data: &frame(T_RESP, 1, &ok),
        fin: true,
    });
    let rec = env.rec.borrow();
    assert_eq!(rec.intents[&1].delivered.keys().copied().collect::<Vec<_>>(), [1]);
    assert_eq!(rec.app_bytes, 300 + 120);
    drop(rec);
    assert_eq!(gate(&env), []);
}

#[test]
fn a_response_for_another_request_does_not_complete_this_one() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let (mut c, stream) = manage_client(&env);
    let (_, other) = env.message(1, 300);
    c.ev(LayerEvent::StreamData {
        session: S,
        stream,
        data: &frame(T_RESP, 99, &other),
        fin: true,
    });
    assert!(env.rec.borrow().intents[&1].delivered.is_empty());
    assert_eq!(env.rec.borrow().app_bytes, 0);
}

#[test]
fn malformed_streams_are_reset_with_an_integrity_violation() {
    let long = {
        let mut h = hdr(T_PUSH, 0, 1);
        h[1..5].copy_from_slice(&u32::MAX.to_be_bytes());
        h.to_vec()
    };
    let not_payload = frame(T_PUSH, 1, &[0x42; 64]);
    let cases: Vec<(&[u8], Vec<u8>, &str)> = vec![
        (
            ALPN_PUSHLOG,
            frame(9, 0, b""),
            "unknown frame type (stream corrupted or reordered)",
        ),
        (
            ALPN_DOCSYNC,
            long.clone(),
            "frame body is too large (stream corrupted or reordered)",
        ),
        (
            ALPN_PUSHLOG,
            frame(T_ACK, 1, b"xx"),
            "acknowledgement with a body (stream corrupted or reordered)",
        ),
        (
            ALPN_PUSHLOG,
            not_payload.clone(),
            "body is not payload (stream corrupted or reordered)",
        ),
        (
            ALPN_MANAGE,
            frame(T_REQ, 1, &[0u8; 30]),
            "body is not payload (stream corrupted or reordered)",
        ),
        (
            ALPN_DOCSYNC,
            frame(T_RESP, 1, b"short"),
            "body is not payload (stream corrupted or reordered)",
        ),
    ];
    for (alpn, bytes, text) in cases {
        let env = Env::new(new_world(2));
        let mut r = env.node(0, |s| s);
        r.boot();
        r.incoming(1, alpn);
        r.data(&bytes, false);
        let name = String::from_utf8_lossy(alpn).into_owned();
        assert_eq!(gate(&env), [("G-INT".into(), format!("{name}: {text}"))]);
        assert_eq!(r.host.resets, [(S, 1, 1)], "{name}: the stream is reset with code 1");
        assert!(r.host.pending_bytes().is_empty());
    }
}

#[test]
fn a_request_with_a_body_that_is_not_the_whole_message_is_reset() {
    let env = Env::new(new_world(2));
    let mut r = env.node(0, |s| s);
    r.boot();
    r.incoming(1, ALPN_DOCSYNC);
    let (_, bytes) = env.message(1, 200);
    r.data(&frame(T_REQ, 5, &bytes[..100]), true);
    assert_eq!(r.host.resets.len(), 1);
    assert_eq!(gate(&env).len(), 1);
}

#[test]
fn the_echo_server_answers_with_the_same_body_and_records_that_it_served() {
    let env = Env::new(new_world(2));
    let mut s = env.node(0, |s| s);
    s.boot();
    // the intent exists on the client's side of the recorder
    let iid = env.rec.borrow_mut().intent(
        IntentKind::Echo,
        1,
        0,
        Some(30 * NS),
        &[],
        32,
        MustArg::Flag(true),
        IntentMeta::default(),
    );
    s.incoming(1, ALPN_ECHO);
    let (_, bytes) = env.message(1, 32);
    s.data(&frame(T_ECHO, u64::from(iid), &bytes), true);
    let w = s.written();
    assert_eq!(
        w,
        [Frame {
            ty: T_ECHO,
            id: u64::from(iid),
            body: Some(bytes)
        }]
    );
    assert_eq!(env.rec.borrow().echo[&iid].served, Some(s.now));
    // an echo of an unknown intent is answered but leaves no timeline behind
    let (_, b2) = env.message(1, 32);
    s.data(&frame(T_ECHO, 777, &b2), false);
    assert!(!env.rec.borrow().echo.contains_key(&777));
}

#[test]
fn open_stream_that_gives_nothing_is_retried_after_100_ms_and_a_reset_after_200_ms() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let mut c = env.node(0, |s| s);
    c.boot();
    let mut d = base_intent(0, IntentKind::Docsync);
    d.to = Some(1);
    c.stack.intent(c.now, &mut c.host, &d);
    c.host.open_ok = false;
    c.ev(LayerEvent::Connected {
        session: S,
        peer: 1,
        alpn: ALPN_DOCSYNC,
    });
    assert_eq!(c.stack.poll_timeout(), Some(c.now + 100_000_000));
    assert!(c.host.pipes.is_empty());
    c.host.open_ok = true;
    c.now += 100_000_000;
    c.stack.timeout(c.now, &mut c.host);
    let stream = *c.host.pipes.keys().next().map(|(_, s)| s).unwrap();
    assert!(c.stack.poll_timeout().is_none());
    // the stream is reset by the peer before an answer: asked again after 200 ms, on a new stream
    c.ev(LayerEvent::StreamReset { session: S, stream });
    assert_eq!(c.stack.poll_timeout(), Some(c.now + 200_000_000));
    c.now += 200_000_000;
    c.stack.timeout(c.now, &mut c.host);
    assert_eq!(c.host.pipes.len(), 2, "the request was written again");
}

#[test]
fn a_reset_after_the_deadline_does_not_ask_again() {
    let env = Env::new(new_world(2));
    allow(&env.rec, 0, 1);
    let mut c = env.node(0, |s| s);
    c.boot();
    let mut d = base_intent(0, IntentKind::Docsync);
    d.to = Some(1);
    d.deadline_ns = NS;
    c.stack.intent(c.now, &mut c.host, &d);
    c.ev(LayerEvent::Connected {
        session: S,
        peer: 1,
        alpn: ALPN_DOCSYNC,
    });
    let stream = *c.host.pipes.keys().next().map(|(_, s)| s).unwrap();
    c.now += 2 * NS;
    c.ev(LayerEvent::StreamReset { session: S, stream });
    assert!(c.stack.poll_timeout().is_none());
}

#[test]
fn a_second_connection_to_a_cached_peer_is_closed() {
    let env = Env::new(new_world(2));
    let mut c = env.node(0, |s| s);
    c.boot();
    let mut d = base_intent(0, IntentKind::Docsync);
    d.to = Some(1);
    c.stack.intent(c.now, &mut c.host, &d);
    c.ev(LayerEvent::Connected {
        session: S,
        peer: 1,
        alpn: ALPN_DOCSYNC,
    });
    c.host.actions.clear();
    c.ev(LayerEvent::Connected {
        session: SessionId(2),
        peer: 1,
        alpn: ALPN_DOCSYNC,
    });
    assert!(matches!(
        c.host.actions[..],
        [crate::net::Action::Close { session: SessionId(2) }]
    ));
    // and a connection nobody asked for (PUSHLOG with no push waiting) is closed the same way
    c.host.actions.clear();
    c.ev(LayerEvent::Connected {
        session: SessionId(3),
        peer: 1,
        alpn: ALPN_PUSHLOG,
    });
    assert!(matches!(
        c.host.actions[..],
        [crate::net::Action::Close { session: SessionId(3) }]
    ));
}
