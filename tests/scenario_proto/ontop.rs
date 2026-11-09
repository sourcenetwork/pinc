//! The application's accounting through a fake on-top layer: publish, fetch and reconcile with the layer present,
//! every check that guards a delivery, and the durable fetch across a restart.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

use vinc_sim::suite::crypto::MsgId;
use vinc_sim::suite::proto::body::{self, Verdict};
use vinc_sim::suite::proto::host::{Host, LayerEvent, Layers};
use vinc_sim::suite::proto::{Command, OnTop, OnTopEvent, ValueIds, stall_fraction};
use vinc_sim::suite::rec::{MemberEvent, MemberKind, NS};
use vinc_sim::suite::world::model::IntentKind;

use crate::lone::{Env, Lone, S};
use crate::net::{allow, base_intent, new_world};

#[derive(Default)]
pub struct FakeState {
    pub cmds: Vec<Command>,
    pub events: VecDeque<OnTopEvent>,
    /// `(value, offset, length)` of the bytes the store holds.
    pub held: Vec<(u64, u64, u64)>,
    pub seen: Vec<String>,
    pub booted: u32,
    pub stopped: u32,
}

pub type Shared = Rc<RefCell<FakeState>>;

pub struct Fake(pub Shared);

pub fn fake() -> (Shared, Box<dyn OnTop>) {
    let s: Shared = Rc::default();
    (s.clone(), Box::new(Fake(s)))
}

impl OnTop for Fake {
    fn alpns(&self) -> Vec<&'static [u8]> {
        vec![b"/fake/1"]
    }
    fn boot(&mut self, _now: u64, _host: &mut dyn Host) {
        self.0.borrow_mut().booted += 1;
    }
    fn command(&mut self, _now: u64, _host: &mut dyn Host, cmd: Command) {
        self.0.borrow_mut().cmds.push(cmd);
    }
    fn event(&mut self, _now: u64, _host: &mut dyn Host, ev: LayerEvent<'_>) {
        self.0.borrow_mut().seen.push(format!("{ev:?}"));
    }
    fn timeout(&mut self, _now: u64, _host: &mut dyn Host) {}
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn poll_event(&mut self) -> Option<OnTopEvent> {
        self.0.borrow_mut().events.pop_front()
    }
    fn holds(&self, value: MsgId, offset: u64, len: u64) -> bool {
        self.0
            .borrow()
            .held
            .iter()
            .any(|&(v, o, l)| v == value.0 && o <= offset && offset + len <= o + l)
    }
    fn contiguous_from(&self, value: MsgId, offset: u64) -> u64 {
        self.0
            .borrow()
            .held
            .iter()
            .filter(|&&(v, o, l)| v == value.0 && o <= offset && offset < o + l)
            .map(|&(_, o, l)| o + l - offset)
            .max()
            .unwrap_or(0)
    }
    fn stop(&mut self) {
        self.0.borrow_mut().stopped += 1;
    }
}

impl Lone {
    /// Lets the stack drain its layers (any call into it does).
    pub fn poll(&mut self) {
        self.stack.timeout(self.now, &mut self.host);
    }
}

fn publish_intent(size: u64) -> vinc_sim::suite::world::model::Intent {
    let mut d = base_intent(0, IntentKind::Publish);
    d.topic = Some(b"/col/0".to_vec());
    d.size = Some(size);
    d.receivers = vec![1, 2];
    d.deadline_ns = 30 * NS;
    d
}

#[test]
fn publish_goes_to_the_layer_and_is_recorded() {
    let env = Env::new(new_world(3));
    let (st, layer) = fake();
    let mut p = env.node(0, |s| s.with_broadcast(layer));
    p.boot();
    assert_eq!(st.borrow().booted, 1);
    p.stack.intent(p.now, &mut p.host, &publish_intent(150));
    assert!(p.stack.waiting.is_empty());
    let rec = env.rec.borrow();
    let it = &rec.intents[&1];
    assert_eq!(it.kind, IntentKind::Publish);
    assert_eq!((it.node, it.size, it.t), (0, 150, p.now));
    assert_eq!(it.deadline, Some(p.now + 30 * NS));
    assert_eq!(it.receivers, [1, 2].into_iter().collect());
    assert!(it.must);
    let cmds = &st.borrow().cmds;
    let [Command::Publish { topic, msg }] = &cmds[..] else {
        panic!("{cmds:?}")
    };
    assert_eq!(topic, b"/col/0");
    assert_eq!(msg.len(), 150);
    let m = body::message_id(msg).unwrap();
    assert_eq!(m.0, it.meta.vid.unwrap());
    assert_eq!(env.reg.creator_of(m), Some(0));
    assert_eq!(body::verify(env.reg, m, msg), Verdict::Whole);
}

fn published(env: &Env, size: u64) -> (u32, Vec<u8>) {
    let (st, layer) = fake();
    let mut p = env.node(0, |s| s.with_broadcast(layer));
    p.boot();
    p.stack.intent(p.now, &mut p.host, &publish_intent(size));
    let iid = env.rec.borrow().next_iid - 1;
    let Command::Publish { msg, .. } = st.borrow().cmds[0].clone() else {
        panic!()
    };
    (iid, msg)
}

#[test]
fn a_message_is_delivered_once_and_every_check_guards_it() {
    let env = Env::new(new_world(3));
    allow(&env.rec, 1, 0);
    let (iid, msg) = published(&env, 150);
    let (st, layer) = fake();
    let mut r = env.node(1, |s| s.with_broadcast(layer));
    r.boot();
    let push =
        |st: &Shared, origin, msg: Vec<u8>| st.borrow_mut().events.push_back(OnTopEvent::Message { origin, msg });

    push(&st, Some(0), msg.clone());
    r.poll();
    {
        let rec = env.rec.borrow();
        assert_eq!(rec.intents[&iid].delivered.keys().copied().collect::<Vec<_>>(), [1]);
        assert_eq!(rec.app_bytes, 150);
        assert!(rec.delivered_msgs.contains(&(1, body::message_id(&msg).unwrap().0)));
    }
    assert_eq!(env.violations(), []);

    // the same message again
    push(&st, Some(0), msg.clone());
    r.poll();
    assert_eq!(
        env.violations(),
        [(
            "G-INT".into(),
            "duplicate delivery of a broadcast message to the application".into()
        )]
    );
    assert_eq!(env.rec.borrow().app_bytes, 150);

    // a message by 0 claimed to come from 2, one with a changed byte, one cut short
    let (_, fresh) = env.message(0, 150);
    push(&st, Some(2), fresh.clone());
    let mut bad = fresh.clone();
    bad[149] ^= 0x80;
    push(&st, Some(0), bad);
    push(&st, Some(0), fresh[..64].to_vec());
    push(&st, Some(0), vec![1, 2, 3]);
    r.poll();
    let v = env.violations();
    assert_eq!(
        v[1..],
        [
            (
                "G-SEC".into(),
                "BROADCAST message attributed to a principal that did not write it".into()
            ),
            (
                "G-INT".into(),
                "BROADCAST message delivered corrupted or foreign bytes".into()
            ),
            ("G-INT".into(), "BROADCAST message delivered a partial message".into()),
            (
                "G-INT".into(),
                "BROADCAST message delivered corrupted or foreign bytes".into()
            ),
        ]
    );
    // the bytes that name no message and the changed byte are the same text, counted twice
    assert_eq!(
        env.rec.borrow().vcount[&(
            "G-INT".to_owned(),
            "BROADCAST message delivered corrupted or foreign bytes".to_owned()
        )],
        2
    );
}

#[test]
fn a_message_without_an_allow_answer_is_an_access_violation() {
    let env = Env::new(new_world(2));
    let (_, msg) = published(&env, 120);
    let (st, layer) = fake();
    let mut r = env.node(1, |s| s.with_broadcast(layer));
    r.boot();
    st.borrow_mut()
        .events
        .push_back(OnTopEvent::Message { origin: Some(0), msg });
    r.poll();
    let v = env.violations();
    assert_eq!(v.len(), 1);
    assert_eq!(v[0].0, "G-ACP");
}

#[test]
fn topics_are_subscribed_at_every_boot_and_the_layer_is_stopped_with_the_node() {
    let mut w = new_world(2);
    w.nodes[0].topics = vec![b"/a".to_vec(), b"/b".to_vec()];
    let env = Env::new(w);
    let (st, layer) = fake();
    let mut n = env.node(0, |s| s.with_broadcast(layer));
    n.boot();
    n.stack.stop();
    n.boot();
    let cmds = st.borrow().cmds.clone();
    let subs: Vec<&[u8]> = cmds
        .iter()
        .map(|c| match c {
            Command::Subscribe { topic } => topic.as_slice(),
            c => panic!("{c:?}"),
        })
        .collect();
    assert_eq!(subs, [&b"/a"[..], b"/b", b"/a", b"/b"]);
    assert_eq!((st.borrow().booted, st.borrow().stopped), (2, 1));
}

#[test]
fn sessions_of_a_layer_are_routed_to_it() {
    let env = Env::new(new_world(2));
    let (st, layer) = fake();
    let mut n = env.node(0, |s| s.with_broadcast(layer));
    assert!(n.stack.alpns().contains(&&b"/fake/1"[..]));
    n.boot();
    n.ev(LayerEvent::Incoming {
        session: S,
        peer: 1,
        alpn: b"/fake/1",
    });
    n.ev(LayerEvent::StreamData {
        session: S,
        stream: 1,
        data: b"x",
        fin: false,
    });
    n.ev(LayerEvent::Closed { session: S });
    n.ev(LayerEvent::StreamData {
        session: S,
        stream: 1,
        data: b"y",
        fin: false,
    });
    let seen = st.borrow().seen.clone();
    assert_eq!(seen.len(), 3, "{seen:?}");
    assert!(seen[0].starts_with("Incoming") && seen[2].starts_with("Closed"));
    assert!(n.host.pending_bytes().is_empty());
}

// ---------------------------------------------------------------------------------------------- fetch

fn fetch_env() -> (Env, ValueIds, MsgId) {
    let mut w = new_world(2);
    w.values.insert("v".to_owned(), 1000);
    w.provides.insert(1, vec!["v".to_owned()]);
    let env = Env::new(w);
    let v = env.reg.new_msg(1, vinc_sim::suite::crypto::PayloadKind::Value, 1000);
    let mut ids = ValueIds::new();
    ids.insert("v".to_owned(), v);
    (env, ids, v)
}

fn fetch_intent() -> vinc_sim::suite::world::model::Intent {
    let mut d = base_intent(0, IntentKind::Fetch);
    d.value = Some("v".to_owned());
    d.providers = vec![1];
    d.ranges = vec![(0, 100), (500, 100)];
    d.stream_rate = Some(8_000_000_000);
    d.deadline_ns = 120 * NS;
    d
}

#[test]
fn a_fetch_is_asked_checked_and_delivered_from_the_store() {
    let (env, ids, v) = fetch_env();
    let (st, layer) = fake();
    let mut f = env.node(0, |s| s.with_values(layer, Rc::new(ids)));
    f.boot();
    f.now = 1000;
    f.stack.intent(f.now, &mut f.host, &fetch_intent());
    {
        let rec = env.rec.borrow();
        let it = &rec.intents[&1];
        assert_eq!((it.size, it.receivers.clone()), (1000, [0].into_iter().collect()));
        assert_eq!(it.meta.req_bytes, Some(200));
        assert_eq!(it.meta.providers, [1]);
        assert_eq!(it.meta.ranges, Some(vec![(0, 100), (500, 100)]));
        assert_eq!(it.deadline, Some(1000 + 120 * NS));
    }
    assert_eq!(f.durable.borrow().open_fetches, [1]);
    let cmd = st.borrow().cmds[0].clone();
    let Command::Fetch {
        fetch_id,
        value,
        len,
        providers,
        ranges,
        priority,
        deadline,
    } = cmd
    else {
        panic!("{cmd:?}")
    };
    assert_eq!(
        (value, len, providers, priority, deadline),
        (v, 1000, vec![1], 3, 1000 + 120 * NS)
    );
    assert_eq!(ranges, Some(vec![(0, 100), (500, 100)]));

    // events: unknown id, complete before the store holds the ranges, readable bytes that are not held
    let ev = |st: &Shared, e| st.borrow_mut().events.push_back(e);
    ev(&st, OnTopEvent::FetchProgress { fetch_id: 99 });
    ev(&st, OnTopEvent::FetchComplete { fetch_id });
    ev(
        &st,
        OnTopEvent::ValueReadable {
            fetch_id,
            offset: 0,
            length: 50,
        },
    );
    ev(&st, OnTopEvent::FetchProgress { fetch_id });
    f.poll();
    assert_eq!(
        env.violations(),
        [
            ("G-SPEC".into(), "FetchProgress for an unknown fetch id".into()),
            (
                "G-INT".into(),
                "FetchComplete before every byte was verified and stored".into()
            ),
            ("G-INT".into(), "ValueReadable for bytes that are not verified".into()),
        ]
    );

    // the first range arrives: progress is noted, the intent is not delivered yet
    st.borrow_mut().held.push((v.0, 0, 100));
    f.now = 1000;
    f.stack.value_progress(1000, v);
    st.borrow_mut().held.push((v.0, 500, 100));
    f.stack.value_progress(1500, v);
    {
        let rec = env.rec.borrow();
        let it = &rec.intents[&1];
        assert_eq!(it.meta.first_byte, Some(1000));
        assert_eq!(it.meta.progress, [(1000, 100), (1500, 100)]);
        assert_eq!(
            it.delivered.keys().copied().collect::<Vec<_>>(),
            [0],
            "delivered when both ranges are held"
        );
        assert_eq!(it.delivered[&0], 1500);
        // 100 B available at 1000 and nothing more until 1500: stalled 400 of 600
        let sf = it.meta.stall_frac.unwrap();
        assert!((sf - 400.0 / 600.0).abs() < f64::EPSILON * 4.0, "{sf}");
        assert_eq!(rec.app_bytes, 0, "a fetch counts the store writes, not the delivery");
    }
    assert!(f.durable.borrow().open_fetches.is_empty());
    // a later write does not deliver twice
    f.stack.value_progress(2000, v);
    assert_eq!(env.rec.borrow().intents[&1].meta.progress.len(), 2);
    // now complete is fine
    ev(&st, OnTopEvent::FetchComplete { fetch_id });
    ev(
        &st,
        OnTopEvent::ValueReadable {
            fetch_id,
            offset: 500,
            length: 100,
        },
    );
    f.poll();
    assert_eq!(env.violations().len(), 3);
}

#[test]
fn a_fetch_is_not_delivered_while_a_range_is_missing() {
    let (env, ids, v) = fetch_env();
    let (st, layer) = fake();
    let mut f = env.node(0, |s| s.with_values(layer, Rc::new(ids)));
    f.boot();
    f.stack.intent(f.now, &mut f.host, &fetch_intent());
    st.borrow_mut().held.push((v.0, 0, 100));
    f.stack.value_progress(10, v);
    let rec = env.rec.borrow();
    assert!(rec.intents[&1].delivered.is_empty());
    assert_eq!(rec.intents[&1].meta.stall_frac, None);
    assert_eq!(f.durable.borrow().open_fetches, [1]);
}

#[test]
fn an_open_fetch_is_asked_again_with_a_new_id_after_a_restart_until_it_is_delivered() {
    let (env, ids, v) = fetch_env();
    let ids = Rc::new(ids);
    let (st, layer) = fake();
    let mut f = env.node(0, |s| s.with_values(layer, ids.clone()));
    f.boot();
    f.stack.intent(f.now, &mut f.host, &fetch_intent());
    f.stack.stop();
    // a new stack on the same durable state
    let (st2, layer2) = fake();
    let mut g = env.node_on(0, f.durable.clone(), |s| s.with_values(layer2, ids.clone()));
    g.boot();
    let ids_of = |st: &Shared| -> Vec<u64> {
        st.borrow()
            .cmds
            .iter()
            .filter_map(|c| {
                if let Command::Fetch { fetch_id, .. } = c {
                    Some(*fetch_id)
                } else {
                    None
                }
            })
            .collect()
    };
    let (a, b) = (ids_of(&st), ids_of(&st2));
    assert_eq!((a.len(), b.len()), (1, 1));
    assert_ne!(a[0], b[0]);
    // the old id is unknown to the new stack; the new one maps to the same intent
    st2.borrow_mut()
        .events
        .push_back(OnTopEvent::FetchProgress { fetch_id: a[0] });
    g.poll();
    assert_eq!(env.violations().len(), 1);
    // once delivered, the next restart does not ask again
    st2.borrow_mut().held.extend([(v.0, 0, 100), (v.0, 500, 100)]);
    g.stack.value_progress(g.now, v);
    g.stack.stop();
    let (st3, layer3) = fake();
    let mut h = env.node_on(0, g.durable.clone(), |s| s.with_values(layer3, ids));
    h.boot();
    assert!(ids_of(&st3).is_empty());
    // provided values are offered at boot
    let (st4, layer4) = fake();
    let (env2, ids2, v2) = fetch_env();
    let mut p = env2.node(1, |s| s.with_values(layer4, Rc::new(ids2)));
    p.boot();
    assert_eq!(st4.borrow().cmds, [Command::Provide { value: v2, len: 1000 }]);
}

#[test]
fn stall_fraction_matches_the_reference_arithmetic() {
    // one byte per ns
    let rate = 8_000_000_000;
    assert_eq!(stall_fraction(&[], Some(0), rate, 100), 1.0);
    assert_eq!(stall_fraction(&[(0, 50)], None, rate, 100), 1.0);
    assert_eq!(stall_fraction(&[(0, 200)], Some(0), rate, 200), 0.0);
    let f = stall_fraction(&[(0, 50), (100, 100)], Some(0), rate, 100);
    assert!((f - 50.0 / 150.0).abs() < f64::EPSILON * 4.0, "{f}");
    // slower than the rate it never stalls: 1 byte per 2 ns and the consumer plays 1 byte per 4 ns
    let f = stall_fraction(&[(0, 0), (8, 4), (16, 8), (24, 12)], Some(0), 2_000_000_000, 12);
    assert!(f >= 0.0 && f < 1.0);
}

// ---------------------------------------------------------------------------------------------- reconcile

fn item(n: u8) -> [u8; 40] {
    [n; 40]
}

fn reconcile_env() -> Env {
    let mut w = new_world(2);
    w.sets.insert((0, b"/col/0".to_vec()), vec![item(1), item(2), item(3)]);
    w.sets
        .insert((1, b"/col/0".to_vec()), vec![item(2), item(3), item(4), item(5)]);
    Env::new(w)
}

fn reconcile_intent() -> vinc_sim::suite::world::model::Intent {
    let mut d = base_intent(0, IntentKind::Reconcile);
    d.to = Some(1);
    d.set_ref = Some(b"/col/0".to_vec());
    d
}

#[test]
fn a_reconcile_result_must_be_the_exact_difference() {
    let env = reconcile_env();
    allow(&env.rec, 0, 1);
    env.rec.borrow_mut().node_tx_bytes.insert(0, 100);
    env.rec.borrow_mut().node_tx_bytes.insert(1, 50);
    let (st, layer) = fake();
    let mut r = env.node(0, |s| s.with_reconcile(layer));
    r.boot();
    r.stack.intent(r.now, &mut r.host, &reconcile_intent());
    assert_eq!(
        st.borrow().cmds,
        [Command::Reconcile {
            set_ref: b"/col/0".to_vec(),
            peer: 1
        }]
    );
    {
        let rec = env.rec.borrow();
        let it = &rec.intents[&1];
        assert_eq!((it.size, it.meta.tx0, it.meta.to), (0, Some(150), Some(1)));
        assert_eq!(it.receivers, [1].into_iter().collect());
    }
    // a wrong difference
    let wrong = OnTopEvent::ReconcileResult {
        set_ref: b"/col/0".to_vec(),
        missing_here: vec![item(4)],
        missing_there: vec![item(1)],
    };
    st.borrow_mut().events.push_back(wrong);
    r.poll();
    assert_eq!(
        env.violations(),
        [(
            "G-INT".into(),
            "reconciliation reported a difference that is not exact".into()
        )]
    );
    assert!(env.rec.borrow().intents[&1].delivered.is_empty());
    // the session was consumed by the wrong answer: a right one now has nothing to answer
    let right = OnTopEvent::ReconcileResult {
        set_ref: b"/col/0".to_vec(),
        missing_here: vec![item(5), item(4)],
        missing_there: vec![item(1)],
    };
    st.borrow_mut().events.push_back(right.clone());
    r.poll();
    assert_eq!(
        env.violations()[1],
        (
            "G-SPEC".into(),
            "ReconcileResult without an open Reconcile for that set".into()
        )
    );

    // a second session, answered exactly
    env.rec.borrow_mut().node_tx_bytes.insert(0, 400);
    env.rec.borrow_mut().node_tx_bytes.insert(1, 350);
    let before = env.rec.borrow().next_iid;
    r.stack.intent(r.now, &mut r.host, &reconcile_intent());
    env.rec.borrow_mut().node_tx_bytes.insert(0, 1000);
    env.rec.borrow_mut().node_tx_bytes.insert(1, 750);
    st.borrow_mut().events.push_back(right);
    r.now += NS;
    r.poll();
    let rec = env.rec.borrow();
    assert_eq!(rec.intents[&before].delivered.keys().copied().collect::<Vec<_>>(), [1]);
    assert_eq!(rec.intents[&before].delivered[&1], r.now);
    assert_eq!(rec.app_bytes, 3 * 40);
    assert_eq!(rec.reconcile_cost, [(1000, 3)]);
    assert_eq!(env.violations().len(), 2);
}

#[test]
fn an_empty_difference_costs_one_item_in_the_cost_figure() {
    let mut w = new_world(2);
    w.sets.insert((0, b"/col/0".to_vec()), vec![item(1)]);
    w.sets.insert((1, b"/col/0".to_vec()), vec![item(1)]);
    let env = Env::new(w);
    allow(&env.rec, 0, 1);
    let (st, layer) = fake();
    let mut r = env.node(0, |s| s.with_reconcile(layer));
    r.boot();
    r.stack.intent(r.now, &mut r.host, &reconcile_intent());
    env.rec.borrow_mut().node_tx_bytes.insert(0, 70);
    st.borrow_mut().events.push_back(OnTopEvent::ReconcileResult {
        set_ref: b"/col/0".to_vec(),
        missing_here: vec![],
        missing_there: vec![],
    });
    r.poll();
    assert_eq!(env.rec.borrow().reconcile_cost, [(70, 1)]);
    assert_eq!(env.violations(), []);
}

// ---------------------------------------------------------------------------------------------- membership

#[test]
fn member_events_reach_the_recorder_with_the_incarnation_of_the_start() {
    let env = Env::new(new_world(3));
    let (st, layer) = fake();
    let mut n = env.node(0, |s| s.with_broadcast(layer));
    n.boot();
    for e in [
        MemberEvent::Joined(Some(1)),
        MemberEvent::Suspected(Some(2)),
        MemberEvent::ViewChanged { epoch: 5 },
    ] {
        st.borrow_mut().events.push_back(OnTopEvent::Member(e));
    }
    n.poll();
    {
        let rec = env.rec.borrow();
        assert_eq!(rec.membership.len(), 2);
        assert_eq!(
            (rec.membership[0].kind, rec.membership[0].member),
            (MemberKind::Joined, Some(1))
        );
        assert_eq!(rec.membership[1].kind, MemberKind::Suspected);
    }
    // the same epoch in the same incarnation is a violation; after a restart it is not
    st.borrow_mut()
        .events
        .push_back(OnTopEvent::Member(MemberEvent::ViewChanged { epoch: 5 }));
    n.poll();
    assert_eq!(
        env.violations(),
        [("G-AWARE".into(), "view epoch not strictly increasing".into())]
    );
    n.stack.stop();
    n.boot();
    st.borrow_mut()
        .events
        .push_back(OnTopEvent::Member(MemberEvent::ViewChanged { epoch: 5 }));
    n.poll();
    assert_eq!(env.violations().len(), 1);
}
