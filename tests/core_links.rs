//! Two endpoints over each class of link the benchmark scenarios emulate (`distributed/scenarios`: `geo`, `leo`,
//! `lte-rural`, `low-bandwidth`, `ble`, `serial`): a new session is set up, a second dial resumes it, a transfer
//! completes intact within a bound derived from the link, and no datagram is larger than the link carries.
//!
//! The link is `CoreNet` with its delay and jitter, a seeded loss, and a [`RateLimit`] per direction with the queue the
//! harness gives its shaper. Jitter is modelled as a uniform extra delay, so a link with delay D and jitter J is run
//! as a base delay of D - J plus a draw from 0 to 2J: the same mean and the same reordering range. Time is virtual, so
//! a result is the same on every run.
//!
//! The transfer bound is `FACTOR` times the bytes at the link's rate, plus `TRIPS` round trips, plus one round trip
//! for every datagram the link is expected to lose: the factor says the sender averages at least a quarter of the
//! link, the fixed round trips pay for the handshake (2), slow start from the initial window up to the path's
//! bandwidth-delay product (up to 7) and the first loss recovery (1), and a lost datagram is known lost and sent
//! again within a round trip. Charging a whole round trip per loss assumes every loss is recovered after the one
//! before it; recoveries overlap in practice, so this is an upper estimate, not a fit to a measurement. The bound says that a transfer ends; how fast each library is on the link is what the
//! benchmark scenario of the same name measures.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::print_stderr
)]

use std::net::SocketAddr;

use vinc_core::{Command, Event, Role, SessionId, Value};
use vinc_tests::*;

/// The bytes at the link's rate are multiplied by this: the sender averages at least a quarter of the link.
const FACTOR: u64 = 4;
/// Round trips added to the transfer bound.
const TRIPS: u64 = 10;
/// The IP and UDP headers a datagram carries beyond its payload.
const HEADERS: usize = 28;

/// One class of link, as its scenario file says it, and the transfer sized for it.
struct Link {
    name: &'static str,
    /// One-way delay in microseconds.
    delay_us: u64,
    /// Jitter in microseconds (see the module comment).
    jitter_us: u64,
    /// Random loss per datagram, in percent.
    loss_pct: u64,
    /// Bits per second from the dialer to the listener.
    rate_bps: u64,
    /// Bits per second from the listener to the dialer when it differs.
    reverse_bps: Option<u64>,
    mtu: u16,
    /// Bytes the dialer sends in the transfer.
    bytes: usize,
}

const GEO: Link = Link {
    name: "geo",
    delay_us: 300_000,
    jitter_us: 0,
    loss_pct: 1,
    rate_bps: 20_000_000,
    reverse_bps: Some(2_000_000),
    mtu: 1500,
    bytes: 2 << 20,
};
const LEO: Link = Link {
    name: "leo",
    delay_us: 22_500,
    jitter_us: 5_000,
    loss_pct: 4,
    rate_bps: 50_000_000,
    reverse_bps: None,
    mtu: 1500,
    bytes: 4 << 20,
};
const LTE_RURAL: Link = Link {
    name: "lte-rural",
    delay_us: 70_000,
    jitter_us: 10_000,
    loss_pct: 0,
    rate_bps: 980_000,
    reverse_bps: None,
    mtu: 1500,
    bytes: 512 << 10,
};
const LOW_BANDWIDTH: Link = Link {
    name: "low-bandwidth",
    delay_us: 500_000,
    jitter_us: 0,
    loss_pct: 2,
    rate_bps: 50_000,
    reverse_bps: None,
    mtu: 1500,
    bytes: 32 << 10,
};
const BLE: Link = Link {
    name: "ble",
    delay_us: 15_000,
    jitter_us: 7_500,
    loss_pct: 0,
    rate_bps: 700_000,
    reverse_bps: None,
    mtu: 1280,
    bytes: 512 << 10,
};
const SERIAL: Link = Link {
    name: "serial",
    delay_us: 100,
    jitter_us: 0,
    loss_pct: 0,
    rate_bps: 92_200,
    reverse_bps: None,
    mtu: 1500,
    bytes: 64 << 10,
};

impl Link {
    fn rtt_ns(&self) -> u64 {
        2 * self.delay_us * 1000
    }

    /// The packets the shaper holds, as the harness computes its `tc` queue limit: what is in flight over the delay and
    /// three jitters at the rate plus 50 ms of buffer, in packets of the interface size, at least 64, plus 16.
    fn queue_packets(&self) -> usize {
        let secs = (self.delay_us + 3 * self.jitter_us) as f64 / 1e6 + 0.05;
        let packets = (self.rate_bps as f64 / 8.0 * secs / f64::from(self.mtu)).ceil() as usize;
        packets.max(64) + 16
    }

    /// The datagrams of the transfer the link is expected to lose: its datagrams of 1,200 bytes times the loss.
    fn expected_losses(&self) -> u64 {
        ((self.bytes as u64).div_ceil(1200) * self.loss_pct).div_ceil(100)
    }

    /// The most a transfer may take: `FACTOR` times its bytes at the rate, plus `TRIPS` round trips, plus a round trip
    /// for each datagram the link is expected to lose.
    fn bound_ns(&self) -> u64 {
        FACTOR * (self.bytes as u64 * 8 * SEC_NS).div_ceil(self.rate_bps)
            + (TRIPS + self.expected_losses()) * self.rtt_ns()
    }

    /// Two endpoints, `a` dialing `b`, on this link.
    fn world(&self) -> (CoreNet, usize, usize) {
        let jitter = self.jitter_us * 1000;
        let mut net = CoreNet::new(self.delay_us * 1000 - jitter);
        net.jitter = 2 * jitter;
        let a = net.add_with_mtu(1, self.mtu);
        let b = net.add_with_mtu(2, self.mtu);
        let mut rate = RateLimit::new(self.rate_bps, self.queue_packets());
        if let Some(bps) = self.reverse_bps {
            rate = rate.with_rate_from(net.nodes[b].addr, bps);
        }
        net.rate = Some(rate);
        if self.loss_pct > 0 {
            let (mut drop, pct) = (SplitMix64::new(0x11_7e), self.loss_pct);
            net.loss = Some(Box::new(move |_, _, _| drop.next_u64() % 100 < pct));
        }
        (net, a, b)
    }
}

fn clear(net: &mut CoreNet) {
    for n in &mut net.nodes {
        n.events.clear();
        n.read.clear();
        n.fin.clear();
    }
}

/// Dial from `a` to `b` and run until `a` reports Connected and `b` Incoming; returns `a`'s session and the time it took.
fn dial(net: &mut CoreNet, a: usize, b: usize, limit: u64) -> (SessionId, u64) {
    clear(net);
    let (peer, to, t0) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
    let s = net.nodes[a].session(&rep);
    let ok = net.run(t0 + limit, |n| {
        n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
            && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
    });
    assert!(ok, "no session within {} ms of virtual time", limit / MS_NS);
    (s, net.now - t0)
}

/// Send `data` from `a` over session `s` and run until `b` has read all of it; returns the time it took.
fn transfer(net: &mut CoreNet, a: usize, b: usize, s: SessionId, data: &[u8], limit: u64) -> u64 {
    clear(net);
    let t0 = net.now;
    let Ok(Value::Stream(id)) = net.nodes[a]
        .cmd(
            t0,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .map(|r| r.value)
    else {
        panic!("no stream")
    };
    let mut sent = 0;
    let done = net.run(t0 + limit, |n| {
        if sent < data.len() {
            let t = n.now;
            let rest = &data[sent..];
            if let Ok(Value::Written(k)) = n.nodes[a]
                .cmd(
                    t,
                    Command::Write {
                        session: s,
                        stream: id,
                        data: rest,
                    },
                )
                .map(|r| r.value)
                && k > 0
            {
                sent += k;
                n.pump(a);
            }
        }
        n.nodes[b].read.values().map(Vec::len).sum::<usize>() >= data.len()
    });
    let got: usize = net.nodes[b].read.values().map(Vec::len).sum();
    assert!(
        done,
        "the transfer did not finish in {} ms of virtual time: {got} of {} bytes arrived ({sent} accepted)",
        limit / MS_NS,
        data.len()
    );
    net.now - t0
}

/// The four checks of one class of link.
fn check(l: &Link) {
    let (mut net, a, b) = l.world();
    let ms = |ns: u64| ns as f64 / 1e6;

    // 1. A session is set up.
    let (sa, setup) = dial(&mut net, a, b, 120 * SEC_NS);

    // 2. After a close a second dial resumes: the dialer reports Connected or Answered with `resumed`, which needs the
    // ticket the first session delivered.
    assert!(
        net.run(net.now + 120 * SEC_NS, |n| !n.nodes[a].ep.tickets().is_empty()),
        "{}: no resumption ticket arrived",
        l.name
    );
    let t = net.now;
    net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(10 * l.rtt_ns() + 2 * SEC_NS);
    let (s2, resumed_in) = dial(&mut net, a, b, 120 * SEC_NS);
    let resumed = |n: &CoreNet| {
        n.nodes[a].saw(|e| {
            matches!(
                e,
                Event::Connected { resumed: true, .. } | Event::Answered { resumed: true, .. }
            )
        })
    };
    assert!(
        resumed(&net) || net.run(net.now + 120 * SEC_NS, |n| resumed(n)),
        "{}: the second dial did not resume",
        l.name
    );

    // 3. The transfer completes, intact, within the bound.
    let mut data = vec![0u8; l.bytes];
    SplitMix64::new(7).fill(&mut data);
    let bound = l.bound_ns();
    let took = transfer(&mut net, a, b, s2, &data, 20 * bound);
    let Some(got) = net.nodes[b].read.values().next() else {
        panic!("{}: nothing was read", l.name)
    };
    assert!(
        got == &data,
        "{}: the bytes that arrived differ from the bytes sent",
        l.name
    );
    assert!(
        took <= bound,
        "{}: {} bytes took {:.0} ms, over the bound of {:.0} ms ({FACTOR} x the bytes at the rate plus {TRIPS} round trips and one for each of {} expected losses)",
        l.name,
        l.bytes,
        ms(took),
        ms(bound),
        l.expected_losses()
    );

    // 4. Nothing larger than the link carries was sent.
    let sizes: Vec<usize> = net.tapped.iter().map(|t| t.3).collect();
    let largest = sizes.iter().copied().max().unwrap_or(0);
    assert!(
        largest <= usize::from(l.mtu) - HEADERS,
        "{}: a datagram of {largest} bytes does not fit a link of {}",
        l.name,
        l.mtu
    );
    assert!(
        largest >= 1200,
        "{}: no full-size datagram was sent ({largest})",
        l.name
    );

    eprintln!(
        "{}: set-up {:.0} ms, resumed {:.0} ms, {} bytes in {:.0} ms (bound {:.0} ms, link alone {:.0} ms), largest datagram {largest} of {}",
        l.name,
        ms(setup),
        ms(resumed_in),
        l.bytes,
        ms(took),
        ms(bound),
        ms((l.bytes as u64 * 8 * SEC_NS).div_ceil(l.rate_bps)),
        usize::from(l.mtu) - HEADERS
    );
}

#[test]
fn a_geostationary_link_sets_up_resumes_and_carries_a_transfer_within_its_bound() {
    big_stack(|| check(&GEO));
}

#[test]
fn a_low_orbit_link_sets_up_resumes_and_carries_a_transfer_within_its_bound() {
    big_stack(|| check(&LEO));
}

#[test]
fn a_rural_lte_link_sets_up_resumes_and_carries_a_transfer_within_its_bound() {
    big_stack(|| check(&LTE_RURAL));
}

#[test]
fn a_50_kbit_lossy_link_sets_up_resumes_and_carries_a_transfer_within_its_bound() {
    big_stack(|| check(&LOW_BANDWIDTH));
}

#[test]
fn a_ble_link_of_1280_bytes_sets_up_resumes_and_sends_nothing_over_1252() {
    big_stack(|| check(&BLE));
}

#[test]
fn a_serial_line_sets_up_resumes_and_carries_a_transfer_within_its_bound() {
    big_stack(|| check(&SERIAL));
}

fn addr(tag: u8) -> SocketAddr {
    ([10, 0, 0, tag], 4433).into()
}

#[test]
fn the_rate_spreads_a_burst_at_the_rate_and_drops_what_the_queue_cannot_hold() {
    // 1250 bytes at 1 Mbit/s leave the link in 10 ms each.
    let mut r = RateLimit::new(1_000_000, 3);
    let ms = |n: u64| n * MS_NS;
    assert_eq!(r.depart(addr(1), 0, 1250), Some(ms(10)));
    assert_eq!(r.depart(addr(1), 0, 1250), Some(ms(20)));
    assert_eq!(r.depart(addr(1), 0, 1250), Some(ms(30)));
    assert_eq!(r.depart(addr(1), 0, 1250), None, "a fourth finds three still leaving");
    // The first has left by 10 ms: there is room again, and the new one waits behind the others.
    assert_eq!(r.depart(addr(1), ms(10), 1250), Some(ms(40)));
    // An idle link starts at once; a smaller datagram takes proportionally less.
    assert_eq!(r.depart(addr(1), ms(100), 125), Some(ms(101)));
    // The other sender has a queue of its own.
    assert_eq!(r.depart(addr(2), 0, 1250), Some(ms(10)));
}

#[test]
fn a_sender_can_have_its_own_rate() {
    let mut r = RateLimit::new(1_000_000, 8).with_rate_from(addr(2), 100_000);
    assert_eq!(r.depart(addr(1), 0, 1250), Some(10 * MS_NS));
    assert_eq!(r.depart(addr(2), 0, 1250), Some(100 * MS_NS));
}
