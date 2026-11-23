//! Model-based test of the facade's open queue: a real session whose peer lets it hold two streams, four `open_bi`
//! futures polled by hand with counting wakers, driven along every edge of the state graph of
//! `proofs/tla/MbtFacadeOpen.tla` (`FacadeOpen.tla`, the code as built).
//!
//! `scripts/mbt.py` turns the graph into paths from the empty queue; `scripts/proofs.sh` writes them to
//! `$PINC_MBT_DIR/facade_open.ndjson`. Each case runs in a fresh world (two endpoints over an in-memory wire and a
//! virtual clock): a call of the case asks, polls, releases or cancels one of the four opens, and after it each open's
//! state (idle, waiting, holding a stream, gone) and the set of opens whose waker ran and that were not polled since
//! must be the model's, and the opens the call woke each ran their waker once more. Without `PINC_MBT_DIR` it checks
//! nothing.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::type_complexity,
    clippy::many_single_char_names,
    clippy::similar_names,
    dead_code,
    unreachable_pub,
    missing_docs
)]

mod facade_world;

use std::future::{Future, poll_fn};
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Poll, Wake, Waker};

use facade_world::{Exec, PEER, PEER_BASE, SUBJECT, Wire, settle, settle_until};
use pinc::{Connection, Hosted, Limits, RecvStream, SendStream};
use pinc_tests::{Json, MbtCase, SplitMix64, mbt_cases};

const ALPN: &[u8] = b"mbt/open";
/// The opens the model has.
const OPENS: usize = 4;

type Task<H> = Option<Connection<H>>;
type Open<H> = Pin<Box<dyn Future<Output = pinc::Result<(SendStream<H>, RecvStream<H>)>>>>;

/// A waker that counts its wakes.
struct Count(AtomicUsize);

impl Wake for Count {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

enum Slot<H: Hosted> {
    Idle,
    Wait(Open<H>),
    Held(SendStream<H>, RecvStream<H>),
    Gone,
}

impl<H: Hosted> Slot<H> {
    const fn name(&self) -> &'static str {
        match self {
            Self::Idle => "idle",
            Self::Wait(_) => "wait",
            Self::Held(..) => "open",
            Self::Gone => "gone",
        }
    }
}

/// The peer: accept a session, then echo every stream the session's other side opens, many at once.
async fn peer_echo<H: Hosted + 'static>(e: pinc::Endpoint<H>) -> Task<H> {
    let i = e.accept().await?;
    let c = i.into_connection();
    let mut live: Vec<Pin<Box<dyn Future<Output = ()>>>> = Vec::new();
    loop {
        let mut acc = Box::pin(c.accept_bi());
        let got = poll_fn(|cx| {
            live.retain_mut(|f| f.as_mut().poll(cx).is_pending());
            acc.as_mut().poll(cx)
        })
        .await;
        let Ok((mut s, mut r)) = got else { return None };
        live.push(Box::pin(async move {
            let data = r.read_to_end(1024).await.unwrap_or_default();
            let _ = s.write_all(&data).await;
            let _ = s.finish().await;
        }));
    }
}

async fn finish_stream<H: Hosted + 'static>(mut s: SendStream<H>) -> Task<H> {
    let _ = s.finish().await;
    None
}

/// The model's value for open `o` (1-based) in a variable of its state, as an array or a record.
fn at(v: &Json, o: usize) -> &Json {
    match v {
        Json::Arr(a) => &a[o - 1],
        Json::Obj(f) => &f.iter().find(|(k, _)| *k == o.to_string()).unwrap().1,
        other => panic!("a state variable that is not indexed by the opens: {other}"),
    }
}

fn set(v: &Json) -> Vec<usize> {
    let mut s: Vec<usize> = v
        .arr()
        .unwrap()
        .iter()
        .map(|x| usize::try_from(x.u64().unwrap()).unwrap())
        .collect();
    s.sort_unstable();
    s
}

struct World<H: Hosted> {
    w: Wire,
    x: Exec<Task<H>>,
    conn: Connection<H>,
    slots: Vec<Slot<H>>,
    wakers: Vec<Arc<Count>>,
    /// The wake count of each open at its last poll.
    polled_at: Vec<usize>,
}

fn world<H: Hosted + 'static>(case: u64, mk: impl FnOnce(&Wire) -> (pinc::Endpoint<H>, pinc::Endpoint<H>)) -> World<H> {
    let w = Wire::new(SplitMix64::traced(0x6f70_656e + case));
    let (a, p) = mk(&w);
    let mut x = Exec::new();
    x.spawn(1, false, {
        let a = a.clone();
        async move {
            let _ = a.accept().await;
            None
        }
    });
    x.spawn(PEER_BASE, false, peer_echo(p.clone()));
    let id = PEER_BASE + 500;
    x.spawn(id, false, {
        let (a, p) = (a.clone(), p.clone());
        async move { a.connect(p.addr(), ALPN).await.ok() }
    });
    settle_until(&w, &mut x, &mut |_| {}, &mut |x| x.done.contains_key(&id));
    let conn = x.done.remove(&id).unwrap().expect("the dial did not connect");
    let mut me = World {
        w,
        x,
        conn,
        slots: Vec::new(),
        wakers: Vec::new(),
        polled_at: vec![0; OPENS],
    };
    me.slots = (0..OPENS).map(|_| Slot::Idle).collect();
    me.wakers = (0..OPENS).map(|_| Arc::new(Count(AtomicUsize::new(0)))).collect();
    me.settle_timed();
    me
}

impl<H: Hosted + 'static> World<H> {
    fn count(&self, o: usize) -> usize {
        self.wakers[o].0.load(Ordering::SeqCst)
    }

    fn counts(&self) -> Vec<usize> {
        (0..OPENS).map(|o| self.count(o)).collect()
    }

    /// Settle, then let 100 ms of virtual time pass, so that what the transport holds back is sent.
    fn settle_timed(&mut self) {
        settle(&self.w, &mut self.x, &mut |_| {});
        let end = self.w.virt.now.get() + 100_000_000;
        while let Some(wakers) = self.w.advance_to(end) {
            wakers.into_iter().for_each(Waker::wake);
            settle(&self.w, &mut self.x, &mut |_| {});
        }
    }

    fn poll_slot(&mut self, o: usize) -> bool {
        let waker = Waker::from(Arc::clone(&self.wakers[o]));
        self.polled_at[o] = self.count(o);
        let Slot::Wait(f) = &mut self.slots[o] else {
            panic!("slot {} holds no open", o + 1)
        };
        match f.as_mut().poll(&mut Context::from_waker(&waker)) {
            Poll::Ready(r) => {
                let (s, r) = r.expect("the open failed");
                self.slots[o] = Slot::Held(s, r);
                true
            }
            Poll::Pending => false,
        }
    }

    fn ask(&mut self, o: usize) -> bool {
        let c = self.conn.clone();
        self.slots[o] = Slot::Wait(Box::pin(async move { c.open_bi().await }));
        self.poll_slot(o)
    }
}

fn run<H: Hosted + 'static>(
    file: &str,
    case: &MbtCase,
    mk: impl FnOnce(&Wire) -> (pinc::Endpoint<H>, pinc::Endpoint<H>),
) -> u64 {
    let mut t = world(case.id, mk);
    let mut task = PEER_BASE + 1000;
    for (n, step) in case.steps.iter().enumerate() {
        let what = || format!("{file}: case {}, step {n} ({step})", case.id);
        let before = t.counts();
        let arg = |i: usize| &step.args[i];
        let o = usize::try_from(arg(0).u64().unwrap()).unwrap() - 1;
        let woke: Vec<usize> = match step.call.as_str() {
            "CallAsk" => {
                let ready = t.ask(o);
                assert_eq!(
                    arg(1).str().unwrap() == "open",
                    ready,
                    "{}: the answer of the first poll",
                    what()
                );
                t.settle_timed();
                Vec::new()
            }
            "CallPoll" => {
                let ready = t.poll_slot(o);
                assert_eq!(
                    arg(1).str().unwrap() == "open",
                    ready,
                    "{}: the answer of the poll",
                    what()
                );
                t.settle_timed();
                set(arg(2)).into_iter().map(|w| w - 1).collect()
            }
            "CallRelease" => {
                let woke: Vec<usize> = set(arg(1)).into_iter().map(|w| w - 1).collect();
                let Slot::Held(s, r) = std::mem::replace(&mut t.slots[o], Slot::Gone) else {
                    panic!("{}: no stream to release", what())
                };
                t.x.spawn(task, false, finish_stream(s));
                task += 1;
                drop(r);
                if woke.is_empty() {
                    t.settle_timed();
                } else {
                    let before = before.clone();
                    let counts: Vec<_> = t.wakers.iter().map(Arc::clone).collect();
                    let w = woke.clone();
                    settle_until(&t.w, &mut t.x, &mut |_| {}, &mut |_| {
                        w.iter().all(|&k| counts[k].0.load(Ordering::SeqCst) > before[k])
                    });
                }
                woke
            }
            "CallCancel" => {
                let woke: Vec<usize> = set(arg(1)).into_iter().map(|w| w - 1).collect();
                t.slots[o] = Slot::Gone;
                t.settle_timed();
                // The future is dropped: a wake it got means nothing (FacadeOpen.tla Cancel).
                t.polled_at[o] = t.count(o);
                woke
            }
            other => panic!("{}: a call the test does not know: {other}", what()),
        };
        let after = t.counts();
        for k in 0..OPENS {
            let want = before[k] + usize::from(woke.contains(&k));
            assert_eq!(after[k], want, "{}: the wakes of open {}", what(), k + 1);
        }
        let st = step.state.get("st").unwrap();
        for (k, slot) in t.slots.iter().enumerate().take(OPENS) {
            assert_eq!(
                at(st, k + 1).str().unwrap(),
                slot.name(),
                "{}: state of open {}",
                what(),
                k + 1
            );
        }
        let woken: Vec<usize> = (0..OPENS)
            .filter(|&k| after[k] > t.polled_at[k])
            .map(|k| k + 1)
            .collect();
        assert_eq!(
            woken,
            set(step.state.get("woken").unwrap()),
            "{}: the opens woken and not polled",
            what()
        );
    }
    case.steps.len() as u64
}

#[test]
fn mbt_facade_open() {
    let Some(cases) = mbt_cases("facade_open.ndjson") else {
        eprintln!("mbt_facade_open: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
        return;
    };
    let cases = cases.unwrap();
    let head = cases.head.clone();
    let (mut n, mut steps) = (0u64, 0u64);
    for case in cases {
        let case = case.unwrap();
        steps += run("facade_open.ndjson", &case, |w| {
            let a = w.endpoint(SUBJECT.parse().unwrap(), 1, ALPN, Limits::default());
            let p = w.endpoint(
                PEER.parse().unwrap(),
                2,
                ALPN,
                Limits {
                    streams: 2,
                    ..Limits::default()
                },
            );
            (a, p)
        });
        n += 1;
    }
    println!("facade_open: {n} cases, {steps} steps");
    let count = |f: &str| head.get(f).and_then(Json::u64).unwrap();
    assert_eq!(
        (n, steps),
        (count("cases"), count("steps")),
        "facade_open.ndjson ends early"
    );
}
