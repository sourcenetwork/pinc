//! Transport parameters: the canonical encoding, parameters carried in the handshake, mismatched configurations, and
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
use vinc_transport::conn::{CloseReason, ParamsError, TransportParams};
use vinc_transport::stream::{self, StreamError};

/// An id and a value as varints.
fn pair(id: u64, v: u64) -> Vec<u8> {
    let mut buf = [0u8; 18];
    let a = vinc_wire::varint::encode(id, &mut buf).unwrap();
    let b = vinc_wire::varint::encode(v, &mut buf[a..]).unwrap();
    buf[..a + b].to_vec()
}

fn enc(p: &TransportParams) -> Vec<u8> {
    let mut buf = [0u8; 256];
    let n = p.encode(&mut buf).unwrap();
    buf[..n].to_vec()
}

#[test]
fn the_encoding_is_canonical_and_exact() {
    assert_eq!(enc(&TransportParams::MIN), Vec::<u8>::new());
    let p = TransportParams {
        initial_max_data: 100,
        max_streams_bidi: 4,
        idle_timeout_ms: 75_000,
        disable_active_migration: true,
        ..TransportParams::MIN
    };
    // id 1 -> 100, id 5 -> 4, id 7 -> 75000 (a three-byte varint), id 12 -> 1.
    assert_eq!(enc(&p), [1, 100, 5, 4, 7, 248, 201, 4, 12, 1]);
    assert_eq!(TransportParams::decode(&enc(&p)).unwrap(), p);
    // Unknown ids are skipped, even among known ones; they must still be ordered.
    assert_eq!(
        TransportParams::decode(&[1, 5, 5, 7, 0x20, 9])
            .unwrap()
            .initial_max_data,
        5
    );
    assert_eq!(TransportParams::decode(&[0x40, 0x99, 9]).unwrap(), TransportParams::MIN);
    // Everything else about the form is strict.
    for (bytes, want) in [
        (&[5u8, 4, 1, 5][..], ParamsError::NotCanonical),
        (&[5, 4, 5, 4][..], ParamsError::NotCanonical),
        (&[1, 0][..], ParamsError::NotCanonical),
        (&pair(8, 1200)[..], ParamsError::NotCanonical),
        (&[12, 0][..], ParamsError::NotCanonical),
        (&[12, 2][..], ParamsError::OutOfRange),
        (&pair(8, 1199)[..], ParamsError::OutOfRange),
        (&[10, 1][..], ParamsError::OutOfRange),
        (&[1][..], ParamsError::Malformed),
        (&[1, 0x80][..], ParamsError::Malformed),
        (&[1, 0xff, 0xff][..], ParamsError::Malformed),
    ] {
        assert_eq!(TransportParams::decode(bytes), Err(want), "{bytes:02x?}");
    }
    let mut tiny = [0u8; 2];
    assert_eq!(p.encode(&mut tiny), Err(ParamsError::BufferTooSmall));
    let bad = TransportParams {
        max_udp_payload: 1199,
        ..TransportParams::MIN
    };
    assert_eq!(bad.encode(&mut [0u8; 64]), Err(ParamsError::OutOfRange));
}

fn params() -> impl Strategy<Value = TransportParams> {
    let big = prop_oneof![Just(0u64), 0u64..1 << 20, any::<u64>().prop_map(|v| v >> 2)];
    (
        proptest::collection::vec(big.clone(), 7),
        1200u64..70_000,
        0u64..2_000,
        2u64..16,
        big,
        any::<bool>(),
    )
        .prop_map(|(v, udp, ack, cid, dg, mig)| TransportParams {
            initial_max_data: v[0],
            max_stream_data_bidi_local: v[1],
            max_stream_data_bidi_remote: v[2],
            max_stream_data_uni: v[3],
            max_streams_bidi: v[4],
            max_streams_uni: v[5],
            idle_timeout_ms: v[6],
            max_udp_payload: udp,
            max_ack_delay_ms: ack,
            active_cid_limit: cid,
            max_datagram_frame_size: dg,
            disable_active_migration: mig,
        })
}

proptest! {
    #[test]
    fn encoding_round_trips_and_is_unique(p in params(), junk in proptest::collection::vec(any::<u8>(), 0..40)) {
        let bytes = enc(&p);
        prop_assert_eq!(TransportParams::decode(&bytes).unwrap(), p);
        // Decoding never panics, and what it accepts re-encodes to the same bytes unless it held unknown ids.
        if let Ok(q) = TransportParams::decode(&junk) {
            let again = enc(&q);
            prop_assert_eq!(TransportParams::decode(&again).unwrap(), q);
        }
    }
}

/// A small MCU-like peer: tiny windows, three streams, no datagrams, a short idle timeout.
fn mcu() -> (stream::Config, vinc_transport::conn::Config) {
    let mut sc = stream::Config::new(true);
    sc.initial_stream_window = 32 * 1024;
    sc.max_stream_window = 32 * 1024;
    sc.initial_conn_window = 48 * 1024;
    sc.max_conn_window = 48 * 1024;
    sc.max_streams_bidi = 3;
    sc.max_streams_uni = 3;
    let mut cfg = vinc_transport::conn::Config::new();
    cfg.params = TransportParams::for_streams(&sc);
    cfg.params.max_datagram_frame_size = 0;
    cfg.idle_timeout = 10 * SEC;
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
        let seen = net.b.conn.peer_params();
        assert_eq!(
            (
                seen.initial_max_data,
                seen.max_streams_bidi,
                seen.max_datagram_frame_size
            ),
            (48 * 1024, 3, 0)
        );
        assert_eq!(net.a.conn.peer_params().initial_max_data, 1_310_720);
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
        // The smaller idle timeout rules for both.
        net.run(net.now + 30 * SEC, |_| false);
        assert_eq!(net.b.closed(), Some(CloseReason::IdleTimeout));
        assert_eq!(net.a.closed(), Some(CloseReason::IdleTimeout));
    });
}

#[test]
fn zero_rtt_respects_the_limits_the_ticket_remembered() {
    big_stack(|| {
        // The server's table and its advertised limits: 100 KiB per stream and for the connection.
        let mut sc = stream::Config::new(false);
        sc.initial_stream_window = 100 * 1024;
        sc.max_stream_window = 100 * 1024;
        sc.initial_conn_window = 100 * 1024;
        sc.max_conn_window = 100 * 1024;
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.params = TransportParams::for_streams(&sc);
        let (mut sa, mut sb) = (Store::new(true), Store::with_stream(CHUNKS, &sc));
        let mut tickets = {
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(64, Params::new(10 * MS)));
            assert!(net.connect(net.now + 10 * SEC));
            assert!(net.run(net.now + 5 * SEC, |n| !n.a.tickets.is_empty()));
            std::mem::take(&mut net.a.tickets)
        };
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        assert_eq!(
            TransportParams::decode(ticket.peer_params().as_bytes())
                .unwrap()
                .initial_max_data,
            100 * 1024,
            "the ticket carries the server's parameters"
        );
        let (mut sa, mut sb) = (Store::new(true), Store::with_stream(CHUNKS, &sc));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(65, Params::new(10 * MS)), &mut w.stores);
        // Before the handshake finishes, early data is limited to what the server advertised last time.
        let id = net.a.conn.open_bi().unwrap();
        let data = pattern(1 << 20, 66);
        let accepted = net.a.conn.write(id, &data).unwrap();
        assert!(accepted > 0 && accepted <= 100 * 1024, "early credit is {accepted}");
        let deadline = net.now + 10 * MS + MS / 2;
        net.run(deadline, |_| false);
        let early = net.b.read.get(&id).map_or(0, Vec::len);
        assert!(early > 0 && early <= 100 * 1024, "{early} early bytes arrived");
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
fn without_a_ticket_nothing_may_be_sent_before_the_parameters_arrive() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(67, Params::new(10 * MS)));
        assert_eq!(
            net.a.conn.open_bi(),
            Err(StreamError::StreamLimit),
            "the minimum allows no streams"
        );
        assert_eq!(net.a.conn.peer_params(), &TransportParams::MIN);
        assert!(net.connect(net.now + 10 * SEC));
        assert!(net.a.conn.open_bi().is_ok());
    });
}
