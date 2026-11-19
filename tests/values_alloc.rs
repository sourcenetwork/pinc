//! Steady state allocates nothing: the verifier, the fetcher draining a response, the server reading the store.
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

use std::ops::Range;

use pinc_dag::ranges::VerifiedRanges;
use pinc_tests::measure;
use pinc_transport::stream::{StreamId, StreamSource};
use pinc_values::fetch::{Fetch, FetchSpec, In, Io};
use pinc_values::plan::Plan;
use pinc_values::server::{Server, ServerIn};
use pinc_values::session::{Inbound, OpenError, Outbound, PeerInfo, Provider, Session};
use pinc_values::source::ValueSource;
use pinc_values::span::Span;
use pinc_values::store::{StoreError, ValueRead, ValueStore};
use pinc_values::trace::{Event, Out, Trace};
use pinc_values::verify::GroupVerifier;
use pinc_values::wire::{GroupHeader, Req};
use values_support::{GROUP, PStore};

pinc_tests::install_counting_allocator!();

const LEN: usize = 4 << 20;

/// A requester session holding one whole response, preallocated; nothing here touches the heap while running.
struct Flat {
    resp: Vec<u8>,
    consumed: u64,
    up: bool,
    req: [u8; 600],
    req_len: usize,
    piece: usize,
}

impl Session for Flat {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, _: StreamId, from: u64, mut f: F) {
        let mut at = from as usize;
        while at < self.resp.len() {
            let end = (at + self.piece).min(self.resp.len());
            let n = f(&self.resp[at..end]);
            at += n;
            if n < end - (at - n) {
                break;
            }
        }
    }
    fn has(&self, _: StreamId, from: u64, len: u64) -> bool {
        (from + len) as usize <= self.resp.len()
    }
    fn consume(&mut self, _: StreamId, upto: u64) {
        self.consumed = upto;
    }
    fn write(&mut self, _: StreamId, data: &[u8], _: bool) -> bool {
        self.req[..data.len()].copy_from_slice(data);
        self.req_len = data.len();
        true
    }
    fn reset(&mut self, _: StreamId, _: u64) {}
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Outbound for Flat {
    fn is_connected(&self, _: Provider) -> bool {
        self.up
    }
    fn dial(&mut self, _: Provider) {}
    fn hangup(&mut self, _: Provider) {}
    fn open_stream(&mut self, _: Provider, _: u8) -> Result<StreamId, OpenError> {
        Ok(1)
    }
    fn peer_info(&self, _: Provider) -> Option<PeerInfo> {
        None
    }
}

struct Mem {
    data: Vec<u8>,
    verified: VerifiedRanges<64>,
}

impl ValueRead for Mem {
    fn servable_len(&self, _: &[u8; 32]) -> Option<u64> {
        None
    }
    fn read_at(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
    fn read_outboard(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
}

impl ValueStore for Mem {
    fn verified_from(&self, _: &[u8; 32], from: u64) -> Option<Range<u64>> {
        pinc_values::store::verified_after(&self.verified, from)
    }
    fn write_at(&mut self, _: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError> {
        self.data[offset as usize..offset as usize + data.len()].copy_from_slice(data);
        Ok(())
    }
    fn commit(&mut self, _: &[u8; 32], range: Range<u64>) -> Result<(), StoreError> {
        self.verified.insert(range).map_err(Into::into)
    }
}

#[derive(Default)]
struct Count {
    readable: u64,
    complete: bool,
    failed: bool,
    traces: u64,
}

impl Out for Count {
    fn event(&mut self, _: u64, ev: Event) {
        match ev {
            Event::Readable { len, .. } => self.readable += len,
            Event::Complete => self.complete = true,
            Event::Failed(_) => self.failed = true,
        }
    }
    fn trace(&mut self, _: u64, _: Trace) {
        self.traces += 1;
    }
}

fn response(store: &PStore) -> Vec<u8> {
    let plan = Plan::new(
        LEN as u64,
        &[Span {
            off: 0,
            len: LEN as u64,
        }],
    )
    .unwrap();
    let mut src = ValueSource::new(store.clone(), store.root(), plan.clone());
    let mut resp = vec![0u8; plan.total() as usize];
    let mut at = 0;
    while at < resp.len() {
        let end = (at + 1452).min(resp.len());
        at += src.read_at(at as u64, &mut resp[at..end]);
    }
    resp
}

#[test]
fn the_fetcher_drains_a_response_without_allocating() {
    let store = PStore::random(1, LEN);
    let resp = response(&store);
    for piece in [1452usize, 65_536] {
        let mut fetch = Box::new(Fetch::new());
        let mut session = Flat {
            resp: resp.clone(),
            consumed: 0,
            up: false,
            req: [0; 600],
            req_len: 0,
            piece,
        };
        let mut mem = Mem {
            data: vec![0; LEN],
            verified: VerifiedRanges::new(),
        };
        let mut out = Count::default();
        let spec = FetchSpec {
            root: store.root(),
            length: LEN as u64,
            ranges: &[],
            providers: &[Provider(0)],
            deadline: None,
        };
        let stats = measure(|| {
            let mut io = Io {
                session: &mut session,
                store: &mut mem,
                out: &mut out,
            };
            fetch.start(&mut io, 0, &spec).unwrap();
            io.session.up = true;
            let total = io.session.resp.len();
            fetch.on_event(&mut io, 1, &In::Connected(Provider(0)));
            fetch.on_event(
                &mut io,
                2,
                &In::Readable {
                    stream: 1,
                    bytes: total,
                },
            );
            fetch.on_event(&mut io, 3, &In::Finished(1));
            fetch.on_timeout(&mut io, 4);
        });
        assert!(out.complete && !out.failed);
        assert_eq!(out.readable, LEN as u64);
        assert_eq!(
            stats.count(),
            0,
            "the fetcher allocated {} times ({} bytes) at pieces of {piece}",
            stats.count(),
            stats.bytes
        );
        assert_eq!(mem.data[..], store.content().bytes(0, LEN as u64)[..]);
        assert_eq!(session.consumed, session.resp.len() as u64);
        assert!(out.traces > 0);
    }
}

#[test]
fn many_providers_stripe_without_allocating() {
    let store = PStore::random(2, LEN);
    let mut fetch = Box::new(Fetch::new());
    let mut session = Flat {
        resp: Vec::new(),
        consumed: 0,
        up: true,
        req: [0; 600],
        req_len: 0,
        piece: 1452,
    };
    let mut mem = Mem {
        data: vec![0; LEN],
        verified: VerifiedRanges::new(),
    };
    let mut out = Count::default();
    let provs = [Provider(0), Provider(1), Provider(2)];
    let spec = FetchSpec {
        root: store.root(),
        length: LEN as u64,
        ranges: &[],
        providers: &provs,
        deadline: Some(1 << 60),
    };
    let stats = measure(|| {
        let mut io = Io {
            session: &mut session,
            store: &mut mem,
            out: &mut out,
        };
        fetch.start(&mut io, 0, &spec).unwrap();
        for (i, p) in provs.iter().enumerate() {
            fetch.on_event(&mut io, 1 + i as u64, &In::Connected(*p));
        }
        fetch.on_timeout(&mut io, 10);
        let _ = fetch.poll_timeout();
        fetch.on_event(&mut io, 11, &In::Closed(Provider(1)));
        fetch.on_event(&mut io, 12, &In::Reset { stream: 1, code: 5 });
    });
    assert_eq!(stats.count(), 0, "scheduling allocated {} times", stats.count());
}

struct ServeSession {
    req: [u8; 600],
    req_len: usize,
    source: Option<ValueSource<PStore>>,
    len: u64,
}

impl Session for ServeSession {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, _: StreamId, from: u64, mut f: F) {
        if let Some(rest) = self.req[..self.req_len].get(from as usize..).filter(|r| !r.is_empty()) {
            f(rest);
        }
    }
    fn has(&self, _: StreamId, from: u64, len: u64) -> bool {
        (from + len) as usize <= self.req_len
    }
    fn consume(&mut self, _: StreamId, _: u64) {}
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        false
    }
    fn reset(&mut self, _: StreamId, _: u64) {}
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Inbound<PStore> for ServeSession {
    fn serve(&mut self, _: StreamId, source: ValueSource<PStore>, len: u64) -> bool {
        self.source = Some(source);
        self.len = len;
        true
    }
}

#[test]
fn the_server_serves_from_the_store_without_allocating_or_buffering() {
    let store = PStore::random(3, LEN);
    let mut server: Server<PStore, 8> = Server::new(store.clone());
    let mut session = ServeSession {
        req: [0; 600],
        req_len: 0,
        source: None,
        len: 0,
    };
    let spans = [Span {
        off: 0,
        len: LEN as u64,
    }];
    session.req_len = Req::encode(&store.root(), &spans, &mut session.req).unwrap();
    let mut out = Count::default();
    let mut buf = vec![0u8; 1452];
    let mut total = 0u64;
    let mut sum = 0u64;
    let stats = measure(|| {
        server.on_event(
            &mut session,
            &mut out,
            0,
            &ServerIn::Opened {
                stream: 1,
                peer: Provider(9),
            },
        );
        server.on_event(&mut session, &mut out, 0, &ServerIn::Readable(1));
        let src = session.source.as_mut().unwrap();
        while total < session.len {
            let n = src.read_at(total, &mut buf);
            sum += u64::from(buf[0]);
            total += n as u64;
        }
        // A retransmission of an early range reads the store again.
        let n = src.read_at(5000, &mut buf);
        sum += n as u64;
    });
    assert!(sum > 0);
    assert_eq!(total, session.len);
    assert_eq!(stats.count(), 0, "the server allocated {} times", stats.count());
}

#[test]
fn the_verifier_and_the_wire_do_not_allocate() {
    let store = PStore::random(4, LEN);
    let resp = response(&store);
    let mut v = GroupVerifier::new(store.root(), LEN as u64, 4, &(0..LEN as u64)).unwrap();
    let mut groups = 0;
    let stats = measure(|| {
        let mut at = 0;
        while at < resp.len() {
            let h = GroupHeader::parse(&resp[at..]).unwrap();
            at += 16;
            let end = at + h.plen as usize + h.len as usize;
            while at < end {
                let f = v.feed(&resp[at..(at + 1452).min(end)]).unwrap();
                at += f.consumed;
                groups += usize::from(f.group.is_some());
            }
        }
        let mut b = [0u8; 600];
        let n = Req::encode(&[1; 32], &[Span { off: 1, len: 2 }; 32], &mut b).unwrap();
        let _ = Req::parse(&b[..n]).unwrap();
    });
    assert!(v.is_complete());
    assert_eq!(groups as u64, LEN as u64 / GROUP);
    assert_eq!(stats.count(), 0, "the verifier allocated {} times", stats.count());
}

#[test]
fn the_machines_have_a_fixed_size() {
    let fetch = std::mem::size_of::<Fetch>();
    let server = std::mem::size_of::<Server<PStore, 32>>();
    eprintln!("Fetch is {fetch} bytes, Server<_, 32> is {server} bytes");
    assert!(fetch < 256 * 1024, "a fetch is {fetch} bytes");
    // 32 request slots of one 4114 byte request buffer or one 255 range plan each.
    assert!(server < 256 * 1024, "a server is {server} bytes");
}
