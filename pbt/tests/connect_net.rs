//! `pinc-connect` client: address discovery and the home relay ([`Netcheck`], [`classify`]), the first-flight
//! selection and the pending dials ([`select`], [`Pending`]) and the tunnel rule ([`decide`]), each against a model
//! written from its module doc, with hostile answers (a wrong nonce, a replayed one, a late one).
//!
//! Where the expected behaviour comes from:
//! - `client::netcheck`: "The home relay is the one with the lowest last-measured round trip among the relays that
//!   ever answered, re-chosen at every answer (a tie goes to the relay that answered first); a node whose probes all
//!   went unanswered takes the relay with the lowest id after three tries ... and the first answer that comes later
//!   moves it to the measured relay"; "**Failover.** A relay that failed [`MISS_LIMIT`] times in a row ... is
//!   unhealthy. When the home relay is unhealthy the home moves only to a relay known to work: the one with the
//!   lowest round trip among those that answered a probe since they last failed, else the next one by table position
//!   whose carrier is open. A relay that merely has not failed yet is no target, and with none the home stays. Any
//!   answer or opened carrier makes a relay healthy again"; "**Pinned home.** ... once the pinned relay has answered
//!   a probe and is healthy, an answer makes it the home whatever its round trip"; "Invariants: the nonce of an answer
//!   must match the probe sent to that relay, and a probe is answered at most once; the round trip of a relay is the
//!   last measured one"; `restart`: "Forget every answer since the link changed ... The home stays"; `answered`:
//!   "Returns the relay's round trip when the nonce matched an outstanding probe"; `reflexive_into`: "The distinct
//!   reflexive addresses learned, in relay order".
//! - `classify`, the five classes in their order: "UDP blocked: no UDP datagram was ever heard and every probe went
//!   unanswered for `watchdog` since the first", "Public: a reflexive address equals a local address (IPv4 or IPv6)",
//!   "Port-mapped: a port mapping the host holds has the external IP a relay saw the node at", "Carrier-grade NAT: a
//!   reflexive IPv4 address in the shared range 100.64.0.0/10, or two relays saw different addresses", "Behind NAT: a
//!   reflexive address that differs from every local address and is the same at every relay that answered".
//! - `client::dial`: "Invariants: [`select`] returns a non-empty subset of the candidates whenever there are
//!   candidates, in candidate order"; `Pending::add`: "Returns false if the table or the peer's list is full";
//!   `take`: "the sessions that waited"; `prune` (DIAL_PRUNE): "keep only the sessions for which `in_handshake`
//!   holds. A peer left with none is dropped and passed to `dropped`".
//! - `client::tunnel`, `decide`: "the carrier is not open: the packet goes by the tunnel ...; the carrier has been
//!   silent for 15 s: the packet goes by the carrier and by the tunnel; the session is in loss recovery (one probe
//!   timeout in a row, two on a thin node) or still handshaking (from the second try, or at once on a node that is not
//!   thin): the packet goes by both", and "The tunnel is usable only over a validated direct UDP hub session that was
//!   heard within 20 s".

use std::collections::BTreeMap;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use ephyra::prelude::*;
use pinc_connect::client::dial::{Cand, Pending, RLY_ONCE, RLY_ONCE_MIN, RelayView, TG_SLOW, Try, select};
use pinc_connect::client::netcheck::{HOME_TRIES, HomeStep, MISS_LIMIT, Netcheck, Observed, classify};
use pinc_connect::client::tunnel::{HUB_TUNNEL_FRESH, HubSession, Rides, TUNNEL_STALE, Via, decide, hub_ok};
use pinc_connect::record::Reach;
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_000 * SEC;

// ---------------------------------------------------------------------------------------------------------------
// Addresses

/// A small pool of addresses, so equal and different ones both come up: public, private, the shared range of
/// carrier-grade NAT, IPv6, and the IPv4-mapped IPv6 form of the first public one.
fn addr(i: u8, port: u8) -> SocketAddr {
    let port = 4000 + u16::from(port % 3);
    let ip = match i % 8 {
        0 => IpAddr::V4(Ipv4Addr::new(198, 51, 100, 7)),
        1 => IpAddr::V4(Ipv4Addr::new(203, 0, 113, 9)),
        2 => IpAddr::V4(Ipv4Addr::new(192, 168, 1, 2)),
        3 => IpAddr::V4(Ipv4Addr::new(100, 64, 0, 1)),
        4 => IpAddr::V4(Ipv4Addr::new(100, 127, 255, 254)),
        5 => IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1)),
        6 => IpAddr::V6(Ipv4Addr::new(198, 51, 100, 7).to_ipv6_mapped()),
        _ => IpAddr::V6(Ipv4Addr::new(100, 64, 0, 1).to_ipv6_mapped()),
    };
    SocketAddr::new(ip, port)
}

/// The same address whatever form it was written in (an IPv4 address seen by a dual-stack socket is IPv4-mapped).
fn canon(a: &SocketAddr) -> SocketAddr {
    SocketAddr::new(a.ip().to_canonical(), a.port())
}

// ---------------------------------------------------------------------------------------------------------------
// Netcheck

const R: usize = 3;

#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
enum Nonce {
    /// The nonce of the relay's outstanding probe.
    Current,
    /// The nonce of the probe before it (a late or replayed answer).
    Previous,
    /// A nonce never sent.
    Wrong,
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum NOp {
    Time(#[ephyra(gen = gens::pick_from(vec![0, 1, 5 * MS, 20 * MS, 80 * MS, SEC, 2 * SEC]))] u64),
    Probe {
        #[ephyra(gen = gens::int(0usize..=R))]
        relay: usize,
        #[ephyra(gen = gens::bool_with(0.8))]
        udp_works: bool,
    },
    Answer {
        #[ephyra(gen = gens::int(0usize..=R))]
        relay: usize,
        nonce: Nonce,
        #[ephyra(gen = gens::int(0u8..=7))]
        ip: u8,
        #[ephyra(gen = gens::int(0u8..=2))]
        port: u8,
    },
    Failed(#[ephyra(gen = gens::int(0usize..=R))] usize),
    Healthy(#[ephyra(gen = gens::int(0usize..=R))] usize),
    Failover {
        #[ephyra(gen = gens::int(0u8..=7))]
        usable: u8,
        #[ephyra(gen = gens::int(0u8..=7))]
        open: u8,
    },
    Restart,
    HomeMissing(#[ephyra(gen = gens::option(gens::int(0usize..R)))] Option<usize>),
    Pin(#[ephyra(gen = gens::int(0usize..=R))] usize),
}

/// The doc's netcheck, kept as plain fields.
#[derive(Debug, Default)]
struct NModel {
    probe: [Option<([u8; 8], u64)>; R],
    rtt: [Option<u64>; R],
    /// The place in the order of first answers.
    order: [Option<u32>; R],
    refl: [Option<SocketAddr>; R],
    missed: [u8; R],
    /// Answered a probe since it last failed and since the link last changed.
    answered_since_fail: [bool; R],
    home: Option<usize>,
    tries: u8,
    pin: Option<usize>,
    answers: u32,
}

impl NModel {
    fn unhealthy(&self, i: usize) -> bool {
        self.missed[i] >= MISS_LIMIT
    }

    fn fail(&mut self, i: usize) {
        self.missed[i] = self.missed[i].saturating_add(1);
        self.answered_since_fail[i] = false;
    }

    /// The best relay at an answer: the healthy pinned relay once it answered, else the lowest round trip among the
    /// healthy relays that ever answered, a tie to the one that answered first.
    fn best(&self) -> Option<usize> {
        let measured = |i: usize| self.order[i].is_some() && !self.unhealthy(i);
        if let Some(p) = self.pin.filter(|p| measured(*p)) {
            return Some(p);
        }
        (0..R)
            .filter(|i| measured(*i))
            .min_by_key(|i| (self.rtt[*i], self.order[*i]))
    }
}

/// The nonce of the probe in flight to a relay, and of the one before it.
type Sent = (Option<[u8; 8]>, Option<[u8; 8]>);

/// `Netcheck` against the model of its doc, after every call: the home, each answer's round trip (and the refusal
/// of a wrong, replayed or second answer), health, failover, the fallback home and the reflexive addresses.
#[ephyra::test(gen = gens::vec(ephyra::any::<NOp>()).len(1..=60), tests = 4000)]
fn netcheck_follows_its_doc(ops: Vec<NOp>) {
    let mut n: Netcheck<R> = Netcheck::new();
    let mut m = NModel::default();
    let mut now = T0;
    let mut seq = 0u64;
    // The nonce of each relay's last two probes.
    let mut sent: [Sent; R] = [(None, None); R];
    for (step, op) in ops.iter().enumerate() {
        match *op {
            NOp::Time(d) => now += d,
            NOp::Probe { relay, udp_works } => {
                seq += 1;
                let nonce = seq.to_be_bytes();
                n.probe_sent(now, relay, nonce, udp_works);
                if relay < R {
                    if udp_works && m.probe[relay].is_some() {
                        m.fail(relay);
                    }
                    m.probe[relay] = Some((nonce, now));
                    sent[relay] = (Some(nonce), sent[relay].0);
                }
            }
            NOp::Answer { relay, nonce, ip, port } => {
                let a = addr(ip, port);
                let given = match (nonce, sent.get(relay)) {
                    (Nonce::Current, Some((Some(c), _))) => *c,
                    (Nonce::Previous, Some((_, Some(p)))) => *p,
                    _ => [0xee; 8],
                };
                let got = n.answered(now, relay, given, a);
                let want = match m.probe.get(relay).copied().flatten() {
                    Some((nc, at)) if nc == given => {
                        m.probe[relay] = None;
                        m.missed[relay] = 0;
                        m.answered_since_fail[relay] = true;
                        m.rtt[relay] = Some(now - at);
                        // the table keeps an IPv4 address in its IPv4 form, whatever form the relay reported it in
                        m.refl[relay] = Some(canon(&a));
                        if m.order[relay].is_none() {
                            m.answers += 1;
                            m.order[relay] = Some(m.answers);
                        }
                        if let Some(b) = m.best() {
                            m.home = Some(b);
                        }
                        Some(now - at)
                    }
                    _ => None,
                };
                assert_eq!(
                    got, want,
                    "step {step}: the answer of relay {relay} with nonce {nonce:?}"
                );
            }
            NOp::Failed(i) => {
                n.failed(i);
                if i < R {
                    m.fail(i);
                }
            }
            NOp::Healthy(i) => {
                n.healthy(i);
                if i < R {
                    m.missed[i] = 0;
                }
            }
            NOp::Failover { usable, open } => {
                let us = |i: usize| usable >> i & 1 == 1;
                let op = |i: usize| open >> i & 1 == 1;
                let got = n.failover(us, op);
                let want = match m.home {
                    Some(h) if m.unhealthy(h) => {
                        let known = (0..R)
                            .filter(|i| *i != h && us(*i) && m.answered_since_fail[*i])
                            .min_by_key(|i| m.rtt[*i]);
                        let next = known.or_else(|| {
                            (1..R)
                                .map(|k| (h + k) % R)
                                .find(|i| us(*i) && op(*i) && !m.unhealthy(*i))
                        });
                        if next.is_some() {
                            m.home = next;
                        }
                        next
                    }
                    _ => None,
                };
                assert_eq!(
                    got, want,
                    "step {step}: failover with usable {usable:03b}, open {open:03b}"
                );
            }
            NOp::Restart => {
                n.restart();
                m.probe = [None; R];
                m.refl = [None; R];
                m.answered_since_fail = [false; R];
                sent = [(None, None); R];
            }
            NOp::HomeMissing(first) => {
                let got = n.home_missing(first);
                let want = if m.home.is_some() {
                    HomeStep::Done
                } else {
                    m.tries = m.tries.saturating_add(1);
                    match first {
                        Some(f) if m.tries >= HOME_TRIES => {
                            m.home = Some(f);
                            HomeStep::Fallback(f)
                        }
                        _ => HomeStep::Again,
                    }
                };
                assert_eq!(got, want, "step {step}: a round without a home");
            }
            NOp::Pin(i) => {
                n.pin(i);
                if i < R {
                    m.pin = Some(i);
                }
            }
        }
        assert_eq!(n.home(), m.home, "step {step}: the home after {op:?}");
        assert_eq!(n.pinned(), m.pin, "step {step}: the pin");
        for i in 0..R {
            assert_eq!(n.unhealthy(i), m.unhealthy(i), "step {step}: the health of relay {i}");
            assert_eq!(
                n.reflexive_of(i),
                m.refl[i],
                "step {step}: the reflexive address of relay {i}"
            );
            assert_eq!(
                n.rtt(i),
                m.refl[i].and(m.rtt[i]),
                "step {step}: the round trip of relay {i}"
            );
        }
        let mut out = [addr(0, 0); R];
        let k = n.reflexive_into(&mut out);
        let mut want: Vec<SocketAddr> = Vec::new();
        for a in m.refl.iter().flatten() {
            if !want.contains(a) {
                want.push(*a);
            }
        }
        assert_eq!(
            &out[..k],
            want.as_slice(),
            "step {step}: the distinct reflexive addresses in relay order"
        );
    }
}

// ---------------------------------------------------------------------------------------------------------------
// classify

#[derive(Clone, Debug)]
struct Obs {
    local: Vec<SocketAddr>,
    reflexive: Vec<SocketAddr>,
    mapped: Vec<SocketAddr>,
    udp_heard: bool,
    since_probe: u64,
    watchdog: u64,
}

fn addrs(max: usize) -> impl Gen<Value = Vec<SocketAddr>> {
    gens::vec((gens::int(0u8..=7), gens::int(0u8..=2)))
        .len(0..=max)
        .map(|v| v.into_iter().map(|(i, p)| addr(i, p)).collect())
}

fn observations() -> impl Gen<Value = Obs> {
    (
        addrs(3),
        addrs(3),
        addrs(2),
        gens::bool(),
        gens::pick_from(vec![0, 8 * SEC - 1, 8 * SEC, 30 * SEC]),
    )
        .map(|(local, reflexive, mapped, udp_heard, since_probe)| Obs {
            local,
            reflexive,
            mapped,
            udp_heard,
            since_probe,
            watchdog: 8 * SEC,
        })
}

/// The class of the doc's five rules, in their order. Two forms of one address are one address: the relays and the
/// host may see an IPv4 address through a dual-stack socket, and `mapped_seen` (the rule `classify` shares with the
/// published addresses) already compares the canonical forms.
fn class_of(o: &Obs) -> Option<Reach> {
    let refl: Vec<SocketAddr> = o.reflexive.iter().map(canon).collect();
    let local: Vec<SocketAddr> = o.local.iter().map(canon).collect();
    if refl.is_empty() {
        return (!o.udp_heard && o.since_probe >= o.watchdog).then_some(Reach::UdpBlocked);
    }
    if refl.iter().any(|r| local.contains(r)) {
        return Some(Reach::Public);
    }
    if o.mapped
        .iter()
        .any(|m| refl.iter().any(|r| r.ip() == m.ip().to_canonical()))
    {
        return Some(Reach::PortMapped);
    }
    let shared = |ip: &IpAddr| matches!(ip, IpAddr::V4(v) if v.octets()[0] == 100 && v.octets()[1] & 0xc0 == 64);
    if refl.iter().any(|r| shared(&r.ip())) || refl.iter().any(|r| *r != refl[0]) {
        return Some(Reach::Cgnat);
    }
    Some(Reach::Nat)
}

/// `classify` against the doc's five rules.
#[ephyra::test(gen = observations(), tests = 20_000)]
fn classify_follows_the_five_rules(o: Obs) {
    let got = classify(&Observed {
        local: &o.local,
        reflexive: &o.reflexive,
        mapped: &o.mapped,
        udp_heard: o.udp_heard,
        since_probe: o.since_probe,
        watchdog: o.watchdog,
    });
    let mixed = o.reflexive.iter().chain(&o.local).any(|a| canon(a) != *a);
    if got != class_of(&o) {
        ephyra::signature(format!("class differs, IPv4-mapped form present: {mixed}"));
    }
    assert_eq!(got, class_of(&o), "the class of {o:?}");
}

// ---------------------------------------------------------------------------------------------------------------
// select and Pending

#[derive(Clone, Debug)]
struct Sel {
    cands: Vec<Cand>,
    t: Try,
    /// The carrier of each relay: open or dialing, and its generation.
    relays: [Option<(bool, u64)>; 3],
}

fn cand() -> impl Gen<Value = Cand> {
    gens::one_of(vec![
        (gens::int(0u8..=7), gens::int(0u8..=2))
            .map(|(i, p)| Cand::Udp(addr(i, p)))
            .boxed(),
        gens::int(0u8..=3).map(Cand::Relay).boxed(),
    ])
}

fn selections() -> impl Gen<Value = Sel> {
    let t = (
        gens::pick_from(vec![0, 1, 100 * MS, 4 * SEC, 30 * SEC]),
        gens::bool_with(0.8),
        gens::int(1u32..=6),
        gens::pick_from(vec![0, 20 * MS, 249 * MS, 250 * MS, 2 * SEC, 20 * SEC]),
        gens::bool(),
        gens::bool_with(0.3),
        gens::option((
            gens::int(0u8..=3),
            gens::int(0u64..=2),
            gens::pick_from(vec![0, 1, 3 * SEC, 30 * SEC]),
        )),
    );
    let relays = gens::vec(gens::option((gens::bool(), gens::int(0u64..=2)))).len(3..=3);
    (gens::vec(cand()).len(0..=6), t, relays).map(|(cands, (now, dialer, tries, link_rtt, no_rtt, hs0, last), rv)| {
        let base = T0;
        Sel {
            cands,
            t: Try {
                now: base + now,
                dialer,
                tries,
                link_rtt,
                no_rtt,
                hs0,
                last_relay: last.map(|(r, g, at)| (r, g, base + at)),
            },
            relays: [rv[0], rv[1], rv[2]],
        }
    })
}

/// `select` returns a non-empty subset of the candidates whenever there are some, in candidate order. The one
/// exception is RLY_ONCE: a try whose every candidate THIN_HS0 leaves is a relay that RLY_ONCE drops (the relay of the
/// last flight, same generation, its carrier live, inside the window, on a slow link) sends nothing. A `select` that
/// returns nothing for candidates `[Relay(3)]` with no view of relay 3 fails it.
#[ephyra::test(gen = selections(), tests = 20_000)]
fn select_returns_a_nonempty_ordered_subset(s: Sel) {
    let mut out = [Cand::Relay(0); 16];
    let (k, carried) = select(
        &s.cands,
        &s.t,
        |r| {
            s.relays
                .get(usize::from(r))
                .copied()
                .flatten()
                .map(|(live, generation)| RelayView { live, generation })
        },
        &mut out,
    );
    let picked = &out[..k];
    // in candidate order: a subsequence of the candidates
    let mut it = s.cands.iter();
    assert!(
        picked.iter().all(|p| it.any(|c| c == p)),
        "{picked:?} is not a subsequence of {:?}",
        s.cands
    );
    if let Some((r, _)) = carried {
        assert!(
            picked.contains(&Cand::Relay(r)),
            "the relay said to carry the flight was picked"
        );
    }
    // the candidates THIN_HS0 leaves (it is not applied when it would drop them all), and which of those RLY_ONCE drops:
    // a relay of the try's last flight, same generation, its carrier live, inside the window
    let window = &s.cands[..s.cands.len().min(16)];
    let hs0_drop = |c: &Cand| matches!(c, Cand::Udp(_)) && s.t.hs0 && s.t.dialer;
    let use_hs0 = !window.iter().all(hs0_drop);
    let once_drop = |c: &Cand| match c {
        Cand::Relay(r) => {
            s.t.dialer
                && s.t.link_rtt >= TG_SLOW
                && s.relays.get(usize::from(*r)).copied().flatten().is_some_and(|(live, generation)| {
                    live && s.t.last_relay.is_some_and(|(lr, g, at)| {
                        lr == *r
                            && g == generation
                            && s.t.now.saturating_sub(at) < RLY_ONCE.min(RLY_ONCE_MIN.max(s.t.link_rtt.saturating_mul(3)))
                    })
                })
        }
        Cand::Udp(_) => false,
    };
    let once_only = window.iter().filter(|c| !(use_hs0 && hs0_drop(c))).all(once_drop);
    if k == 0 && !s.cands.is_empty() && !once_only {
        let udp_only = s.cands.iter().all(|c| matches!(c, Cand::Udp(_)));
        ephyra::signature(format!(
            "empty selection, hs0 {}, only UDP candidates {udp_only}",
            s.t.hs0
        ));
    }
    assert!(
        s.cands.is_empty() || k > 0 || once_only,
        "no path for a try with candidates {:?} under {:?}",
        s.cands,
        s.t
    );
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum POp {
    Add(
        #[ephyra(gen = gens::int(0u8..=4))] u8,
        #[ephyra(gen = gens::int(0u8..=5))] u8,
    ),
    Take(#[ephyra(gen = gens::int(0u8..=4))] u8),
    /// Keep the sessions whose bit is set.
    Prune(#[ephyra(gen = gens::int(0u8..=63))] u8),
}

fn node(i: u8) -> NodeId {
    static IDS: std::sync::OnceLock<Vec<NodeId>> = std::sync::OnceLock::new();
    IDS.get_or_init(|| {
        (1u8..=5)
            .map(|s| {
                Keypair::from_seed(IdentityAlg::Ed25519, &[s; 32])
                    .expect("a seed makes a key")
                    .node_id()
            })
            .collect()
    })[usize::from(i)]
}

/// The pending dials against a map of peers to session lists: bounded at 3 peers of 2 sessions, `add` true exactly
/// when the session is held, `take` the sessions that waited, `prune` drops exactly the peers left with none.
#[ephyra::test(gen = gens::vec(ephyra::any::<POp>()).len(1..=40), tests = 4000)]
fn pending_dials_follow_their_doc(ops: Vec<POp>) {
    const N: usize = 3;
    const H: usize = 2;
    let mut p: Pending<u8, N, H> = Pending::new();
    let mut m: BTreeMap<u8, Vec<u8>> = BTreeMap::new();
    for (step, op) in ops.iter().enumerate() {
        match *op {
            POp::Add(peer, s) => {
                let got = p.add(node(peer), s);
                let room = m.len() < N;
                let want = match m.get_mut(&peer) {
                    Some(v) if v.contains(&s) => true,
                    Some(v) if v.len() < H => {
                        v.push(s);
                        true
                    }
                    Some(_) => false,
                    None if room => {
                        m.insert(peer, vec![s]);
                        true
                    }
                    None => false,
                };
                assert_eq!(got, want, "step {step}: add session {s} for peer {peer}");
            }
            POp::Take(peer) => {
                let mut got: Vec<u8> = p.take(&node(peer)).into_iter().flatten().collect();
                got.sort_unstable();
                let mut want = m.remove(&peer).unwrap_or_default();
                want.sort_unstable();
                assert_eq!(got, want, "step {step}: the sessions that waited for peer {peer}");
            }
            POp::Prune(mask) => {
                let mut dropped = Vec::new();
                p.prune(|s| mask >> s & 1 == 1, |peer| dropped.push(*peer));
                let mut want_dropped = Vec::new();
                m.retain(|peer, v| {
                    v.retain(|s| mask >> s & 1 == 1);
                    if v.is_empty() {
                        want_dropped.push(node(*peer));
                    }
                    !v.is_empty()
                });
                dropped.sort_by_key(|n| n.bytes);
                want_dropped.sort_by_key(|n| n.bytes);
                assert_eq!(dropped, want_dropped, "step {step}: the peers pruned");
            }
        }
        for i in 0..5u8 {
            assert_eq!(p.contains(&node(i)), m.contains_key(&i), "step {step}: peer {i} waits");
        }
        for s in 0..6u8 {
            assert_eq!(
                p.holds(s),
                m.values().any(|v| v.contains(&s)),
                "step {step}: session {s} is held"
            );
        }
        assert_eq!(p.peers().count(), m.len(), "step {step}: the peers waited for");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The tunnel rule

#[derive(Clone, Debug)]
struct Tun {
    open: bool,
    silent: u64,
    session: Option<Rides>,
    hub: HubSession,
    now: u64,
}

fn tunnels() -> impl Gen<Value = Tun> {
    let silent = gens::pick_from(vec![0, TUNNEL_STALE - 1, TUNNEL_STALE, TUNNEL_STALE + 1, 60 * SEC]);
    let rides = gens::option((gens::int(0u32..=3), gens::bool(), gens::int(0u32..=3), gens::bool()));
    let heard = gens::pick_from(vec![0, 1, HUB_TUNNEL_FRESH - 1, HUB_TUNNEL_FRESH, HUB_TUNNEL_FRESH + 1]);
    (gens::bool(), silent, rides, gens::bool(), heard).map(|(open, silent, rides, validated, ago)| Tun {
        open,
        silent,
        session: rides.map(|(pto_count, handshaking, hs_tries, thin)| Rides {
            pto_count,
            handshaking,
            hs_tries,
            thin,
        }),
        hub: HubSession {
            validated_direct: validated,
            heard: T0,
            remote: addr(0, 0),
        },
        now: T0 + ago,
    })
}

/// `decide` and `hub_ok` against the rules of the tunnel doc.
#[ephyra::test(gen = tunnels(), tests = 5000)]
fn the_tunnel_rule_follows_its_doc(t: Tun) {
    let usable = t.hub.validated_direct && t.now - t.hub.heard < HUB_TUNNEL_FRESH;
    assert_eq!(
        hub_ok(&t.hub, t.now),
        usable,
        "the tunnel is usable over a validated session heard within 20 s"
    );
    let both = |s: &Rides| {
        let loss = s.pto_count >= if s.thin { 2 } else { 1 };
        let hs = s.handshaking && (s.hs_tries >= 2 || !s.thin);
        loss || hs
    };
    let want = if !usable {
        Via::Carrier
    } else if !t.open {
        Via::Tunnel
    } else if t.silent > TUNNEL_STALE || t.session.as_ref().is_some_and(both) {
        Via::Both
    } else {
        Via::Carrier
    };
    assert_eq!(decide(t.open, t.silent, t.session, usable), want, "{t:?}");
}
