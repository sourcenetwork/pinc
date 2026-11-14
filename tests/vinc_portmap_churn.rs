//! The `UPnP` HTTP exchange of the facade survives a change of the driving call: the application drives the endpoint
//! with calls that return every few milliseconds, and a gateway whose answer is there 40 ms after the request was
//! written. The host honours the carriers' contract (a read that is dropped loses nothing, a write reports how much it
//! took); a host that does not is not coped with, and the last test shows the limit.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::type_complexity,
    clippy::too_many_lines
)]

use std::cell::{Cell, RefCell};
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::{Duration, Instant};

use smol::channel::{Sender, unbounded};
use vinc::{CarrierKind, Endpoint, Hosted, Vinc};
use vinc_portmap::upnp;

const ALPN: &[u8] = b"portmap/churn";
const SEARCH_ANSWER: &[u8] = b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.1:5000/d.xml\r\n\r\n";
const DESC: &str = "<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";

/// One TCP stream of the gateway: what was written, when, and whether the answer was handed over.
struct Stream {
    req: RefCell<Vec<u8>>,
    wrote_at: Cell<Option<Instant>>,
    taken: Cell<bool>,
}

struct Counts {
    opened: Rc<Cell<usize>>,
    closed: Rc<Cell<usize>>,
    answered: Rc<Cell<usize>>,
}

/// How the host behaves besides answering 40 ms after the write.
#[derive(Clone, Copy)]
struct Opts {
    /// A read that is dropped loses the answer (a host that breaks the carriers' contract).
    loses: bool,
    /// A write takes this long (milliseconds) before it records its bytes.
    write_ms: u64,
    /// A write takes at most this many bytes.
    chunk: usize,
    /// The gateway never answers an `AddPortMapping`.
    stall_add: bool,
}

const KIND: Opts = Opts {
    loses: false,
    write_ms: 0,
    chunk: usize::MAX,
    stall_add: false,
};

/// What the gateway answers to the request in `req`.
fn reply(req: &[u8]) -> Vec<u8> {
    let text = String::from_utf8_lossy(req);
    let body = if text.starts_with("GET") {
        DESC.to_owned()
    } else if text.contains("GetExternalIPAddress") {
        "<NewExternalIPAddress>203.0.113.9</NewExternalIPAddress>".to_owned()
    } else {
        "<u:AddPortMappingResponse/>".to_owned()
    };
    format!("HTTP/1.1 200 OK\r\n\r\n{body}").into_bytes()
}

/// An endpoint on 192.168.1.5 with port mapping on and no gateway whose carriers answer 40 ms after the write. With
/// `loses` the read takes the answer when it starts, so a read that is dropped loses it (a host that breaks the
/// carriers' contract).
fn bind(
    loses: bool,
) -> (
    Endpoint<impl Hosted>,
    Rc<RefCell<Vec<SocketAddr>>>,
    Sender<(Vec<u8>, SocketAddr)>,
    Counts,
) {
    bind_with(Opts { loses, ..KIND })
}

fn bind_with(
    o: Opts,
) -> (
    Endpoint<impl Hosted>,
    Rc<RefCell<Vec<SocketAddr>>>,
    Sender<(Vec<u8>, SocketAddr)>,
    Counts,
) {
    let (tx, rx) = unbounded::<(Vec<u8>, SocketAddr)>();
    let sent: Rc<RefCell<Vec<SocketAddr>>> = Rc::default();
    let log = Rc::clone(&sent);
    let opened = Rc::new(Cell::new(0usize));
    let closed = Rc::new(Cell::new(0usize));
    let answered = Rc::new(Cell::new(0usize));
    let (op, cl, an) = (Rc::clone(&opened), Rc::clone(&closed), Rc::clone(&answered));
    let loses = o.loses;
    let ep = Vinc::builder()
        .alpn(ALPN)
        .local_addr("192.168.1.5:4433".parse().unwrap())
        .port_mapping(true)
        .carriers(
            async move |_relay: &vinc::Relay, _kind: CarrierKind| -> std::io::Result<Stream> {
                op.set(op.get() + 1);
                Ok(Stream {
                    req: RefCell::default(),
                    wrote_at: Cell::new(None),
                    taken: Cell::new(false),
                })
            },
            async move |s: &Stream, mut buf: Vec<u8>| -> (std::io::Result<usize>, Vec<u8>) {
                let due = |s: &Stream| {
                    s.wrote_at
                        .get()
                        .is_some_and(|t| Instant::now() >= t + Duration::from_millis(40))
                };
                let mut taken_here = false;
                if loses && !s.taken.get() && s.wrote_at.get().is_some() {
                    // takes the answer now: dropping this read loses it
                    taken_here = true;
                    s.taken.set(true);
                }
                if o.stall_add && String::from_utf8_lossy(&s.req.borrow()).contains("AddPortMapping") {
                    std::future::pending::<()>().await;
                }
                loop {
                    if (taken_here || (!loses && !s.taken.get())) && due(s) {
                        s.taken.set(true);
                        let a = reply(&s.req.borrow());
                        buf[..a.len()].copy_from_slice(&a);
                        an.set(an.get() + 1);
                        return (Ok(a.len()), buf);
                    }
                    if s.taken.get() && !taken_here {
                        return (Ok(0), buf);
                    }
                    tokio::time::sleep(Duration::from_millis(3)).await;
                }
            },
            async move |s: &Stream, buf: Vec<u8>, from: usize| {
                if o.write_ms > 0 {
                    tokio::time::sleep(Duration::from_millis(o.write_ms)).await;
                }
                let n = (buf.len() - from).min(o.chunk);
                s.req.borrow_mut().extend_from_slice(&buf[from..from + n]);
                s.wrote_at.set(Some(s.wrote_at.get().unwrap_or_else(Instant::now)));
                (Ok(n), buf)
            },
            async move |_s: Stream| cl.set(cl.get() + 1),
        )
        .build(
            async move |buf: &mut [u8]| {
                let (d, from) = rx.recv().await.map_err(|_| std::io::ErrorKind::BrokenPipe)?;
                buf[..d.len()].copy_from_slice(&d);
                Ok((d.len(), from))
            },
            async move |pkt: &[u8], to: SocketAddr| {
                log.borrow_mut().push(to);
                Ok(pkt.len())
            },
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap();
    (
        ep,
        sent,
        tx,
        Counts {
            opened,
            closed,
            answered,
        },
    )
}

/// The application's way of driving: a call that returns every 10 ms.
async fn churn(ep: &Endpoint<impl Hosted>, d: Duration) {
    let start = Instant::now();
    while start.elapsed() < d {
        let _ = tokio::time::timeout(Duration::from_millis(10), ep.accept()).await;
        tokio::time::sleep(Duration::from_millis(2)).await;
    }
}

async fn search_then_answer(
    ep: &Endpoint<impl Hosted>,
    sent: &Rc<RefCell<Vec<SocketAddr>>>,
    tx: &Sender<(Vec<u8>, SocketAddr)>,
) {
    let end = Instant::now() + Duration::from_secs(5);
    while !sent.borrow().contains(&upnp::SSDP) && Instant::now() < end {
        churn(ep, Duration::from_millis(20)).await;
    }
    tx.try_send((SEARCH_ANSWER.to_vec(), "192.168.1.1:1900".parse().unwrap()))
        .unwrap();
}

#[tokio::test(flavor = "current_thread")]
async fn an_exchange_survives_a_driving_call_that_changes_every_12_ms() {
    let (ep, sent, tx, c) = bind(false);
    search_then_answer(&ep, &sent, &tx).await;
    // the description, the external address and AddPortMapping: three exchanges of 40 ms each, under churn
    let end = Instant::now() + Duration::from_secs(8);
    let mut held = None;
    while held.is_none() && Instant::now() < end {
        churn(&ep, Duration::from_millis(50)).await;
        held = ep.port_mapping().await;
    }
    assert_eq!(
        held,
        Some("203.0.113.9:4433".parse().unwrap()),
        "opened {} answered {} stats {:?}",
        c.opened.get(),
        c.answered.get(),
        ep.port_mapping_stats().await
    );
    assert!(c.answered.get() >= 3);
}

/// The limit: a host whose read loses the answer when it is dropped is not coped with. The endpoint does not hang or
/// panic and holds no mapping; the exchange ends with no usable answer.
#[tokio::test(flavor = "current_thread")]
async fn a_host_that_loses_data_when_a_read_is_dropped_gets_no_mapping() {
    let (ep, sent, tx, c) = bind(true);
    search_then_answer(&ep, &sent, &tx).await;
    churn(&ep, Duration::from_millis(1500)).await;
    assert_eq!(
        ep.port_mapping().await,
        None,
        "opened {} answered {}",
        c.opened.get(),
        c.answered.get()
    );
}

/// A write that is dropped by a change of driver ends the exchange and its stream is closed; the client's own retry
/// decides when to ask again, so the streams opened in six seconds are the one the first exchange used.
#[tokio::test(flavor = "current_thread")]
async fn a_dropped_write_ends_the_exchange_and_opens_no_stream_of_its_own() {
    for chunk in [usize::MAX, 200] {
        let (ep, sent, tx, c) = bind_with(Opts {
            write_ms: 20,
            chunk,
            ..KIND
        });
        search_then_answer(&ep, &sent, &tx).await;
        churn(&ep, Duration::from_secs(6)).await;
        assert_eq!(
            (c.opened.get(), c.closed.get()),
            (1, 1),
            "writes of {chunk} bytes: streams opened and closed in 6 s (the client retries after 300 s)"
        );
        assert_eq!(ep.port_mapping().await, None);
    }
}
