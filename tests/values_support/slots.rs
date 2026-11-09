//! The request slots of the value server as a trace: random runs of a real `Server` over several values, recorded as
//! `vslotnew` / `vslot` events (the whole table before and after, and the resets sent) for the trace checks of
//! `trace_values_plan` (`TraceValuesPlan.tla` and the Lean replay, which hold each event to the model of
//! `ValuesPlanServer`).

use std::collections::HashMap;
use std::rc::Rc;

use super::PStore;
use vinc_tests::SplitMix64;
use vinc_transport::stream::StreamId;
use vinc_values::server::{Server, ServerIn};
use vinc_values::session::{Inbound, Provider, Session};
use vinc_values::source::ValueSource as VSource;
use vinc_values::span::Span;
use vinc_values::store::ValueRead;
use vinc_values::wire::Req;

use vinc_values::knobs::GROUP;

fn arr(items: impl Iterator<Item = String>) -> String {
    format!("[{}]", items.collect::<Vec<_>>().join(","))
}

fn span_json(spans: &[Span]) -> String {
    arr(spans.iter().map(|s| format!("[{},{}]", s.off, s.len)))
}

/// Several values behind one store handle, found by root.
#[derive(Clone)]
struct Multi(Rc<Vec<PStore>>);

impl Multi {
    fn find(&self, root: &[u8; 32]) -> Option<&PStore> {
        self.0.iter().find(|s| s.servable_len(root).is_some())
    }
}

impl ValueRead for Multi {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        self.find(root).and_then(|s| s.servable_len(root))
    }
    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        self.find(root).map_or(0, |s| s.read_at(root, offset, dst))
    }
    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        self.find(root).map_or(0, |s| s.read_outboard(root, offset, dst))
    }
}

/// A session that holds request bytes, records the resets and installs a source unless it is told to refuse.
#[derive(Default)]
struct SlotSess {
    reqs: HashMap<StreamId, Vec<u8>>,
    resets: Vec<(StreamId, u64)>,
    refuse: bool,
}

impl Session for SlotSess {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        if let Some(r) = self.reqs.get(&stream)
            && let Some(rest) = r.get(from as usize..).filter(|r| !r.is_empty())
        {
            f(rest);
        }
    }
    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        self.reqs.get(&stream).is_some_and(|r| (from + len) as usize <= r.len())
    }
    fn consume(&mut self, _: StreamId, _: u64) {}
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        false
    }
    fn reset(&mut self, stream: StreamId, code: u64) {
        self.resets.push((stream, code));
    }
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Inbound<Multi> for SlotSess {
    fn serve(&mut self, _: StreamId, _: VSource<Multi>, _: u64) -> bool {
        !self.refuse
    }
}

/// Whether a slot holds the request on `stream`.
fn holds<const S: usize>(server: &Server<Multi, S>, stream: StreamId) -> bool {
    (0..S).any(|i| server.slot(i).is_some_and(|v| v.stream == stream))
}

/// The table of a server as the trace holds it.
fn slot_table<const S: usize>(server: &Server<Multi, S>, roots: &[PStore]) -> String {
    arr((0..S).map(|i| match server.slot(i) {
        None => "[]".to_string(),
        Some(v) => match v.serving {
            None => format!("[{},{}]", v.stream, v.peer.0),
            Some((root, plan)) => {
                let idx = roots.iter().position(|r| r.root() == *root).unwrap() + 1;
                let ranges = arr((0..plan.ranges()).map(|r| {
                    let sp = plan.range_span(r).unwrap();
                    format!("[{},{}]", sp.off, sp.len)
                }));
                format!("[{},{},{idx},{ranges}]", v.stream, v.peer.0)
            }
        },
    }))
}

/// One run over a server with `S` slots: random opens, requests (known and unknown roots, spans in and out of the
/// value, a session that refuses), finished and reset streams, closed sessions.
fn slot_run<const S: usize>(emit: &mut dyn FnMut(&str, &[u64]), rng: &mut SplitMix64, multi: &Multi, steps: usize) {
    let roots = multi.0.as_ref();
    let mut server: Server<Multi, S> = Server::new(multi.clone());
    let mut sess = SlotSess::default();
    let mut next: StreamId = 1;
    let mut collecting: Vec<StreamId> = Vec::new();
    let mut seen: Vec<StreamId> = Vec::new();
    let mut lines = vec![format!(r#"{{"t":"vslotnew","s":{S}}}"#)];
    let mut nums = vec![S as u64];
    for _ in 0..steps {
        let before = slot_table(&server, roots);
        let mark = sess.resets.len();
        let head = match rng.next_u64() % 14 {
            0..=3 => {
                let (stream, peer) = (next, 1 + rng.next_u64() % 2);
                next += 1;
                server.on_event(
                    &mut sess,
                    &mut (),
                    0,
                    &ServerIn::Opened {
                        stream,
                        peer: Provider(peer as u32),
                    },
                );
                if holds(&server, stream) {
                    collecting.push(stream);
                }
                seen.push(stream);
                format!(r#""ev":"open","stream":{stream},"peer":{peer}"#)
            }
            4..=9 if !collecting.is_empty() => {
                let stream = collecting.swap_remove((rng.next_u64() as usize) % collecting.len());
                let known = !rng.next_u64().is_multiple_of(8);
                let (ridx, root, ln) = if known {
                    let k = (rng.next_u64() as usize) % 2;
                    (k + 1, roots[k].root(), roots[k].len())
                } else {
                    (0, [0xEE; 32], 0)
                };
                let spans: Vec<Span> = (0..=rng.next_u64() % 3)
                    .map(|_| match rng.next_u64() % 8 {
                        0 => Span { off: 0, len: 0 },
                        1 => Span {
                            off: ln.saturating_sub(10),
                            len: 100,
                        },
                        2..=4 => Span {
                            off: 0,
                            len: 1 + rng.next_u64() % ln.max(1),
                        },
                        _ => {
                            let off = rng.next_u64() % ln.max(1);
                            Span {
                                off,
                                len: 1 + rng.next_u64() % (ln - off).max(1),
                            }
                        }
                    })
                    .collect();
                let mut b = [0u8; 600];
                let n = Req::encode(&root, &spans, &mut b).unwrap();
                sess.reqs.insert(stream, b[..n].to_vec());
                sess.refuse = rng.next_u64().is_multiple_of(6);
                server.on_event(&mut sess, &mut (), 0, &ServerIn::Readable(stream));
                nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
                nums.push(ln);
                format!(
                    r#""ev":"req","stream":{stream},"root":{ridx},"len":{ln},"spans":{},"inst":{}"#,
                    span_json(&spans),
                    u8::from(!sess.refuse)
                )
            }
            10..=12 if !seen.is_empty() => {
                let stream = seen[(rng.next_u64() as usize) % seen.len()];
                let done = rng.next_u64().is_multiple_of(2);
                server.on_event(
                    &mut sess,
                    &mut (),
                    0,
                    &if done {
                        ServerIn::Done(stream)
                    } else {
                        ServerIn::Reset(stream)
                    },
                );
                collecting.retain(|&c| c != stream);
                format!(r#""ev":"{}","stream":{stream}"#, if done { "done" } else { "reset" })
            }
            _ => {
                let peer = 1 + rng.next_u64() % 3;
                server.on_event(&mut sess, &mut (), 0, &ServerIn::Closed(Provider(peer as u32)));
                collecting.retain(|&c| holds(&server, c));
                format!(r#""ev":"closed","peer":{peer}"#)
            }
        };
        assert!(server.held() <= S, "a request beyond {S} is refused, never queued");
        let rc = arr(sess.resets[mark..].iter().map(|(s, c)| format!("[{s},{c}]")));
        lines.push(format!(
            r#"{{"t":"vslot",{head},"before":{before},"after":{},"rc":{rc}}}"#,
            slot_table(&server, roots)
        ));
    }
    for l in lines {
        emit(&l, &nums);
    }
}

pub fn slot_runs(emit: &mut dyn FnMut(&str, &[u64]), rng: &mut SplitMix64) {
    let g = GROUP as usize;
    let multi = Multi(Rc::new(vec![
        PStore::random(500, g + 3),
        PStore::random(501, 5 * g + 9),
        PStore::random(502, 12 * g),
    ]));
    for _ in 0..4 {
        slot_run::<2>(emit, rng, &multi, 60);
        slot_run::<3>(emit, rng, &multi, 60);
        slot_run::<4>(emit, rng, &multi, 80);
    }
}
