//! Trace generation for the relay clock of an endpoint that carries the relay role (`endpoint.rs`, `drive.rs`,
//! `drive/role_io.rs`), recorded as ndjson (`role-clock.ndjson`) for the TLA+ trace check `TraceFacadeRoleClock.tla`.
//!
//! A case builds an endpoint with the relay role on a fake platform whose wall clock is `w` and whose monotonic clock the
//! test moves, over a store that always hands back one record that does not verify and some held packets; the endpoint is
//! run, the restore is waited for (the store's `remove` is called), the run is dropped, the clock moves, and it is run
//! again. The second run loads and restores nothing (the role holds what the store kept), so it is waited for until the
//! role serves, and the store has been told to forget the record once. The packets that survive the restore are the
//! ones that are young by the relay's own clock. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::large_futures,
    clippy::unused_async_trait_impl,
    clippy::too_many_lines,
    dead_code,
    unused_macros,
    unused_imports,
    missing_docs
)]

mod pinc_common;
mod relay_members;

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::net::{SocketAddr, UdpSocket};
use std::rc::Rc;
use std::sync::Arc;
use std::time::{Duration, Instant};

use nuclei::Handle;
use pinc::relay::{CarrierFns, Kept, KeptRecord, Limits, Peer, Relay as RelayHost, Store};
use pinc::{CarrierKind, Endpoint, Error, ErrorKind, Hosted, Pinc, Platform};
use pinc_connect::record::{self, Reach, RecordFields};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};
use pinc_tests::SplitMix64;

/// A platform whose instant is nanoseconds in a `u64`, whose wall clock is fixed and whose clock the test moves.
#[derive(Clone)]
struct Fake {
    now: Rc<Cell<u64>>,
    wall_ns: u64,
}

impl Platform for Fake {
    type Instant = u64;
    type Error = Error;

    fn now(&self) -> u64 {
        self.now.get()
    }

    fn wall_ns(&self) -> u64 {
        self.wall_ns
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Error> {
        pinc_keystore::os_random(out).map_err(|_| Error::new(ErrorKind::Config, "no randomness"))
    }
}

struct Inner {
    kept: Kept,
    removes: Cell<u32>,
    loads: Cell<u32>,
}

/// A store that hands back the same `Kept` every time and counts the records it is told to forget.
#[derive(Clone)]
struct RecStore(Rc<Inner>);

impl Store for RecStore {
    async fn load(&self) -> pinc::Result<Kept> {
        self.0.loads.set(self.0.loads.get() + 1);
        Ok(self.0.kept.clone())
    }

    async fn put(&self, _node: &NodeId, _record: &[u8], _received: u64) -> pinc::Result<()> {
        Ok(())
    }

    async fn remove(&self, _node: &NodeId) -> pinc::Result<()> {
        self.0.removes.set(self.0.removes.get() + 1);
        Ok(())
    }

    async fn put_mailbox(&self, _node: &NodeId, _packets: &[u8]) -> pinc::Result<()> {
        Ok(())
    }
}

/// The arrival times (ms) of the packets kept for a wall clock `w` (ms): ascending, not below 0, without repeats.
fn arrivals(w: u64) -> Vec<u64> {
    let w = i64::try_from(w).unwrap();
    let all = [w - 1500, w - 1000, w - 999, w - 1, w, w + 500, 9000, 9001, 10000, 10001];
    all.into_iter()
        .filter(|a| *a >= 0)
        .map(|a| a as u64)
        .collect::<BTreeSet<u64>>()
        .into_iter()
        .collect()
}

/// What the store keeps: one record that parses and does not verify, and a blob of packets of one member.
fn kept(w: u64) -> Kept {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x21; 32]).unwrap();
    let mut rec = vec![0u8; record::MAX_RECORD_LEN];
    let n = record::sign(
        &kp,
        &RecordFields {
            home: kp.node_id(),
            seq: 1,
            reach: Reach::UdpBlocked,
            addrs: &[],
            hints: &[],
        },
        &mut rec,
    )
    .unwrap();
    rec.truncate(n);
    *rec.last_mut().unwrap() ^= 1;
    let src = Keypair::from_seed(IdentityAlg::Ed25519, &[0x23; 32]).unwrap().node_id();
    let mut blob = Vec::new();
    for a in arrivals(w) {
        blob.push(src.alg.tag());
        blob.extend_from_slice(&src.bytes);
        blob.push(0);
        blob.extend_from_slice(&(a * 1_000_000).to_be_bytes());
        blob.extend_from_slice(&4u16.to_be_bytes());
        blob.extend_from_slice(&[0x5A; 4]);
    }
    let member = Keypair::from_seed(IdentityAlg::Ed25519, &[0x22; 32]).unwrap().node_id();
    Kept {
        records: vec![KeptRecord {
            bytes: rec,
            received: 0,
        }],
        mailboxes: vec![(member, blob)],
    }
}

fn failed(_: std::io::Error) -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

/// An endpoint that carries the relay role, on the fake platform, over a loopback UDP socket.
async fn build(fake: Fake, store: RecStore) -> pinc::Result<Endpoint<impl Hosted>> {
    let sock = Arc::new(Handle::<UdpSocket>::bind(pinc_common::lo()).await.unwrap());
    let at = sock.local_addr().unwrap();
    let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
    let carriers = CarrierFns::new(
        async || -> pinc::Result<((), CarrierKind)> { core::future::pending().await },
        async |_peer: &Peer, _kind: CarrierKind| -> pinc::Result<()> {
            Err(Error::new(ErrorKind::Unreachable, "the relay has no peers"))
        },
        async |_s: &(), buf: Vec<u8>| (Ok::<usize, Error>(0), buf),
        async |_s: &(), buf: Vec<u8>, _from: usize| (Ok::<usize, Error>(0), buf),
        async |_s: ()| {},
    );
    Pinc::builder_on(fake)
        .seed(&[0x70; 32])
        .unwrap()
        .hub()
        .local_addr(at)
        .relay_role(
            RelayHost::builder().store(store).limits(Limits {
                mailbox_max_age_ns: 1_000_000_000,
                ..Limits::default()
            }),
            carriers,
        )
        .build(
            async move |buf: &mut [u8]| -> pinc::Result<(usize, SocketAddr)> { r.recv_from(buf).await.map_err(failed) },
            async move |pkt: &[u8], to: SocketAddr| -> pinc::Result<usize> { s.send_to(pkt, to).await.map_err(failed) },
            async |_at: u64| nuclei::time::sleep(Duration::from_millis(1)).await,
        )
}

/// Wait, within 10 s of real time, until the store has been told to forget `n` records.
async fn wait_removes(store: &RecStore, n: u32) {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut pause = 1;
    while store.0.removes.get() < n {
        assert!(Instant::now() < deadline, "the restore did not run within the deadline");
        nuclei::time::sleep(Duration::from_millis(pause)).await;
        pause = (pause * 2).min(64);
    }
}

/// Wait, within 10 s of real time, until the endpoint's relay role serves.
async fn wait_serving(ep: &Endpoint<impl Hosted>) {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut pause = 1;
    while !ep.trace_role_serving() {
        assert!(Instant::now() < deadline, "the role did not serve within the deadline");
        nuclei::time::sleep(Duration::from_millis(pause)).await;
        pause = (pause * 2).min(64);
    }
}

/// One case: a wall clock `w` (ms) and the step (ms) the clock moves between the two runs.
async fn case(out: &mut String, w: u64, step: u64) {
    let fake = Fake {
        now: Rc::default(),
        wall_ns: w * 1_000_000,
    };
    let store = RecStore(Rc::new(Inner {
        kept: kept(w),
        removes: Cell::new(0),
        loads: Cell::new(0),
    }));
    let kept_list: Vec<String> = arrivals(w).iter().map(u64::to_string).collect();
    let built = build(fake.clone(), store.clone()).await;
    let _ = writeln!(
        out,
        "{{\"op\":\"build\",\"w\":{w},\"ok\":{},\"kept\":[{}]}}",
        built.is_ok(),
        kept_list.join(",")
    );
    let ep = match built {
        Ok(ep) => {
            assert_ne!(w, 0, "a wall clock of zero built a relay role");
            ep
        }
        Err(e) => {
            assert_eq!(w, 0, "a known wall clock was refused: {e}");
            assert_eq!(e.kind(), ErrorKind::Config);
            return;
        }
    };
    let spawn = |ep: &Endpoint<_>| {
        let e = ep.clone();
        nuclei::spawn_local(async move {
            let _ = e.run().await;
        })
    };
    let stored = |ep: &Endpoint<_>| ep.relay_stats().unwrap().mailbox.stored;
    let task = spawn(&ep);
    wait_removes(&store, 1).await;
    let first = stored(&ep);
    let _ = writeln!(
        out,
        "{{\"op\":\"run\",\"el\":0,\"stored\":{first},\"loads\":{}}}",
        store.0.loads.get()
    );
    let want = arrivals(w).iter().filter(|a| w.saturating_sub(**a) < 1000).count() as u64;
    assert_eq!(
        first, want,
        "the packets restored are not the young ones by the wall clock"
    );
    drop(task);
    let _ = writeln!(out, "{{\"op\":\"end\"}}");
    fake.now.set(fake.now.get() + step * 1_000_000);
    let task = spawn(&ep);
    wait_serving(&ep).await;
    assert_eq!(store.0.removes.get(), 1, "a second run restored the store again");
    let _ = writeln!(
        out,
        "{{\"op\":\"run\",\"el\":{step},\"stored\":{},\"loads\":{}}}",
        stored(&ep),
        store.0.loads.get()
    );
    drop(task);
    let _ = writeln!(out, "{{\"op\":\"end\"}}");
}

#[test]
fn facade_role_clock_trace() {
    relay_members::on_big_stack(|| async {
        let mut out = String::new();
        for w in [0, 1, 5000, 9999, 10_000, 10_001, 600_000] {
            case(&mut out, w, 2000).await;
        }
        for seed in 1..=10 {
            let mut rng = SplitMix64::new(seed);
            let w = rng.next_u64() % 1_000_000;
            let step = rng.next_u64() % 3000;
            case(&mut out, w, step).await;
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("role-clock.ndjson"), out).unwrap();
        }
    });
}
