//! The credit record: its exact six-byte encoding, the record carried in the handshake, mismatched configurations, and
//! 0-RTT within the limits a ticket remembered.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::manual_assert_eq
)]

use proptest::prelude::*;
use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, CreditRecord, credit_for_streams, peer_limits};
use vinc_transport::stream::{self, StreamError};

#[test]
fn the_record_is_six_bytes_and_exact() {
    // window (16 KiB units), streams, datagram: three big-endian u16.
    let c = CreditRecord::new(1_310_720, 100, 65_535);
    assert_eq!(c.encode(), [0, 80, 0, 100, 0xff, 0xff]);
    assert_eq!(CreditRecord::decode(&c.encode()), c);
    assert_eq!(c.window_bytes(), 1_310_720);
    assert_eq!(CreditRecord::NONE.encode(), [0; 6]);
    assert_eq!(CreditRecord::default(), CreditRecord::NONE);
    // The window rounds down to whole units and saturates at the field's width.
    assert_eq!(CreditRecord::new(16 * 1024 - 1, 1, 1).window_units, 0);
    assert_eq!(CreditRecord::new(3 * 16 * 1024 + 5, 1, 1).window_units, 3);
    assert_eq!(CreditRecord::new(u64::MAX, 1, 1).window_units, u16::MAX);
    // A record covers another when every limit is at least as large.
    let small = CreditRecord::new(64 * 1024, 10, 1200);
    assert!(c.covers(&small) && !small.covers(&c));
    assert!(c.covers(&c) && small.covers(&CreditRecord::NONE));
}

#[test]
fn the_record_maps_onto_the_stream_layers_limits() {
    let sc = stream::Config::new(false);
    let c = credit_for_streams(&sc);
    assert_eq!(c.window_bytes(), sc.initial_stream_window);
    assert_eq!(u64::from(c.max_streams), sc.max_streams);
    assert_eq!(c.max_datagram, u16::MAX);
    let l = peer_limits(&CreditRecord::new(96 * 1024, 7, 0));
    assert_eq!((l.window, l.max_streams), (96 * 1024, 7));
    assert_eq!(peer_limits(&CreditRecord::NONE), stream::PeerLimits::default());
}

proptest! {
    #[test]
    fn every_six_bytes_decode_to_one_record_that_encodes_back(bytes in any::<[u8; 6]>()) {
        let c = CreditRecord::decode(&bytes);
        prop_assert_eq!(c.encode(), bytes);
        prop_assert_eq!(CreditRecord::decode(&c.encode()), c);
    }

    #[test]
    fn new_never_exceeds_the_window_asked_for(w in any::<u64>(), s in any::<u16>(), d in any::<u16>()) {
        let c = CreditRecord::new(w, s, d);
        prop_assert!(c.window_bytes() <= w);
        prop_assert!(c.window_units == u16::MAX || w - c.window_bytes() < 16 * 1024);
        prop_assert_eq!((c.max_streams, c.max_datagram), (s, d));
    }
}

/// A small MCU-like peer: tiny windows, three streams, no datagrams.
fn mcu() -> (stream::Config, vinc_transport::conn::Config) {
    let mut sc = stream::Config::new(true);
    sc.initial_stream_window = 32 * 1024;
    sc.max_stream_window = 32 * 1024;
    sc.max_streams = 3;
    let mut cfg = vinc_transport::conn::Config::new();
    cfg.credit = credit_for_streams(&sc);
    cfg.credit.max_datagram = 0;
    (sc, cfg)
}

#[test]
fn mismatched_configurations_work_both_ways() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (sc, ccfg) = mcu();
        w.client_cfg = Some(ccfg);
        let mut sa = Store::with_stream(40, &sc);
        let mut sb = Store::new(false);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(61, Params::new(5 * MS).loss(0.5)));
        assert!(net.connect(net.now + 10 * SEC));
        // Each side sees the other's limits.
        let seen = net.b.conn.peer_credit();
        assert_eq!(
            (seen.window_bytes(), seen.max_streams, seen.max_datagram),
            (32 * 1024, 3, 0)
        );
        assert_eq!(net.a.conn.peer_credit().window_bytes(), 1_310_720);
        assert!(net.b.conn.send_datagram(b"x").is_err(), "the MCU takes no datagrams");
        assert!(net.a.conn.send_datagram(b"x").is_ok());
        // The server may open three streams, no more.
        let ids: Vec<u64> = (0..3).map(|_| net.b.conn.open_bi().unwrap()).collect();
        assert_eq!(net.b.conn.open_bi(), Err(StreamError::StreamLimit));
        // One megabyte each way through windows of 32 KiB.
        let up = pattern(1 << 20, 62);
        let down = pattern(1 << 20, 63);
        let (ua, db) = (net.a.conn.open_bi().unwrap(), ids[0]);
        let (mut uo, mut dofs, mut u_fin, mut d_fin) = (0, 0, false, false);
        let mut max_pool = 0;
        let ok = net.run(net.now + 600 * SEC, |n| {
            while uo < up.len() {
                let k = n.a.conn.write(ua, &up[uo..]).unwrap();
                if k == 0 {
                    break;
                }
                uo += k;
            }
            while dofs < down.len() {
                let k = n.b.conn.write(db, &down[dofs..]).unwrap();
                if k == 0 {
                    break;
                }
                dofs += k;
            }
            if uo == up.len() && !u_fin {
                n.a.conn.finish(ua).unwrap();
                u_fin = true;
            }
            if dofs == down.len() && !d_fin {
                n.b.conn.finish(db).unwrap();
                d_fin = true;
            }
            max_pool = max_pool.max(n.a.conn.pool().used_bytes());
            n.b.fin.contains(&ua) && n.a.fin.contains(&db)
        });
        assert!(ok, "closed: {:?} {:?}", net.a.closed(), net.b.closed());
        assert!(net.b.read[&ua] == up && net.a.read[&db] == down);
        assert!(max_pool <= net.a.conn.pool().budget_bytes());
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
        // Idle is the same fixed 75 s on every node, whatever a peer's limits: neither side leaves early.
        net.run(net.now + 60 * SEC, |_| false);
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
        net.run(net.now + 30 * SEC, |_| false);
        assert_eq!(net.a.closed(), Some(CloseReason::IdleTimeout));
        assert_eq!(net.b.closed(), Some(CloseReason::IdleTimeout));
    });
}

#[test]
fn zero_rtt_respects_the_limits_the_ticket_remembered() {
    big_stack(|| {
        // The server's table and its advertised limits: 96 KiB per stream and for the connection.
        let mut sc = stream::Config::new(false);
        sc.initial_stream_window = 96 * 1024;
        sc.max_stream_window = 96 * 1024;
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&sc);
        let (mut sa, mut sb) = (Store::new(true), Store::with_stream(CHUNKS, &sc));
        let mut tickets = {
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(64, Params::new(10 * MS)));
            assert!(net.connect(net.now + 10 * SEC));
            assert!(net.run(net.now + 5 * SEC, |n| !n.a.tickets.is_empty()));
            std::mem::take(&mut net.a.tickets)
        };
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        assert_eq!(
            ticket.peer_credit().window_bytes(),
            96 * 1024,
            "the ticket carries the server's record"
        );
        let (mut sa, mut sb) = (Store::new(true), Store::with_stream(CHUNKS, &sc));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(65, Params::new(10 * MS)), &mut w.stores);
        // Before the handshake finishes, early data is limited to what the server advertised last time.
        let id = net.a.conn.open_bi().unwrap();
        let data = pattern(1 << 20, 66);
        let accepted = net.a.conn.write(id, &data).unwrap();
        assert!(accepted > 0 && accepted <= 96 * 1024, "early credit is {accepted}");
        let deadline = net.now + 10 * MS + MS / 2;
        net.run(deadline, |_| false);
        let early = net.b.read.get(&id).map_or(0, Vec::len);
        assert!(early > 0 && early <= 96 * 1024, "{early} early bytes arrived");
        assert!(!net.a.conn.is_connected());
        // The rest follows once the handshake is done.
        let mut off = accepted;
        let mut finished = false;
        let ok = net.run(net.now + 60 * SEC, |n| {
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == data.len() && !finished {
                n.a.conn.finish(id).unwrap();
                finished = true;
            }
            n.b.fin.contains(&id)
        });
        assert!(ok && net.b.read[&id] == data);
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
    });
}

#[test]
fn without_a_ticket_nothing_may_be_sent_before_the_record_arrives() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(67, Params::new(10 * MS)));
        assert_eq!(
            net.a.conn.open_bi(),
            Err(StreamError::StreamLimit),
            "the minimum allows no streams"
        );
        assert_eq!(net.a.conn.peer_credit(), &CreditRecord::NONE);
        assert!(net.connect(net.now + 10 * SEC));
        assert!(net.a.conn.open_bi().is_ok());
    });
}
