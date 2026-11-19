//! The TCP model behind stream carriers: connection setup, congestion control, loss recovery, delayed ACKs and the
//! WebSocket setup exchanges, ported from the reference harness.
//!
//! Records written by a node are queued whole on the sending end and delivered whole, in order, when the receiving
//! end's cumulative ACK point covers them, so head-of-line blocking under loss is real. Segments carry no payload:
//! only sizes, sequence numbers and the identity of the sending end travel through the network.
//!
//! Invariants: an end is never reused (a stale segment can only reach the end it was sent to, and is ignored once
//! that end is closed); the heap events scheduled here carry a version, and an event whose version is stale does
//! nothing; every push happens in the order the reference makes it, because that order breaks ties between events at
//! the same instant.
#![allow(clippy::many_single_char_names)]

use std::collections::{BTreeMap, VecDeque};
use std::net::SocketAddr;

use crate::Time;
use crate::config::{CostModel, NodeState};
use crate::node::{Node, StreamEvent, StreamId, StreamKind};
use crate::rng::Random;
use crate::sim::{Ev, Sim};
use crate::stream::StreamInput;

/// IPv4 20 + TCP 20 + timestamps 12.
pub(crate) const TCP_HDR: u32 = 52;
/// The maximum segment size.
pub(crate) const MSS: u64 = 1448;
/// TLS 1.3 per-record overhead.
const TLS_RECORD: u64 = 22;
/// WebSocket frame header, client to server and server to client.
const WS_C2S: u64 = 8;
const WS_S2C: u64 = 4;
/// Setup exchange sizes of a WebSocket carrier (TLS 1.3 certificate chain and the HTTP upgrade).
const TLS_SETUP_C2S: u64 = 520;
const TLS_SETUP_S2C: u64 = 2900;
const WS_UPGRADE_C2S: u64 = 260;
const WS_UPGRADE_S2C: u64 = 160;
const MS: Time = 1_000_000;
const SEC: Time = 1_000_000_000;

/// What a segment is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SegKind {
    Syn,
    SynAck,
    Ack,
    Data,
}

/// Up to four selective-acknowledgement blocks `(seq, len)`, lowest first.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Sack {
    n: u8,
    blocks: [(u64, u32); 4],
}

impl Sack {
    fn blocks(&self) -> &[(u64, u32)] {
        &self.blocks[..usize::from(self.n)]
    }
}

/// The TCP header of a segment in flight.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Seg {
    pub(crate) kind: SegKind,
    /// The sending end.
    pub(crate) from: u32,
    pub(crate) seq: u64,
    pub(crate) len: u32,
    pub(crate) ack: Option<u64>,
    pub(crate) sack: Sack,
    /// Bytes on the wire, header included.
    pub(crate) size: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum State {
    Syn,
    SynRcvd,
    Est,
    Open,
    Rejected,
}

struct Rec {
    end_seq: u64,
    data: Vec<u8>,
    setup: bool,
}

#[derive(Clone, Copy)]
struct Inflight {
    len: u32,
    sent: Time,
    retx: bool,
}

/// One end of a modelled TCP connection.
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct TcpEnd {
    pub(crate) node: u32,
    pub(crate) handle: u32,
    pub(crate) peer: Option<u32>,
    pub(crate) state: State,
    pub(crate) ws: bool,
    pub(crate) is_client: bool,
    pub(crate) local: SocketAddr,
    pub(crate) remote: SocketAddr,
    pub(crate) closed: bool,
    pub(crate) simul: bool,
    snd_una: u64,
    snd_nxt: u64,
    snd_end: u64,
    records: VecDeque<Rec>,
    cwnd: u64,
    ssthresh: u64,
    srtt: u64,
    rttvar: u64,
    rto: Time,
    rto_ver: u64,
    rto_count: u32,
    dupacks: u32,
    inflight: BTreeMap<u64, Inflight>,
    recover: u64,
    in_recovery: bool,
    rcv_nxt: u64,
    ooo: BTreeMap<u64, u32>,
    unacked_segs: u32,
    delack_ver: u64,
    setup: u8,
}

impl TcpEnd {
    pub(crate) fn new(
        node: u32,
        handle: u32,
        is_client: bool,
        kind: StreamKind,
        local: SocketAddr,
        remote: SocketAddr,
    ) -> Self {
        Self {
            node,
            handle,
            peer: None,
            state: if is_client { State::Syn } else { State::SynRcvd },
            ws: kind == StreamKind::Ws,
            is_client,
            local,
            remote,
            closed: false,
            simul: false,
            snd_una: 0,
            snd_nxt: 0,
            snd_end: 0,
            records: VecDeque::new(),
            cwnd: 10 * MSS,
            ssthresh: 1 << 30,
            srtt: 0,
            rttvar: 0,
            rto: SEC,
            rto_ver: 0,
            rto_count: 0,
            dupacks: 0,
            inflight: BTreeMap::new(),
            recover: 0,
            in_recovery: false,
            rcv_nxt: 0,
            ooo: BTreeMap::new(),
            unacked_segs: 0,
            delack_ver: 0,
            setup: 0,
        }
    }

    /// Frees the buffers of a closed end that nobody reads; the shell stays so stale segments find a closed end.
    /// The queued records stay until the peer has closed too, because the peer delivers from them.
    pub(crate) fn release(&mut self) {
        self.inflight = BTreeMap::new();
        self.ooo = BTreeMap::new();
    }
}

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    /// Sends the SYN of a client end and arms its retransmission timer.
    pub(crate) fn tcp_syn(&mut self, t: Time, e: u32) {
        self.tcp_pkt(t, e, SegKind::Syn, 0, 0, None, Sack::default(), 8);
        let end = &mut self.ends[e as usize];
        end.rto_ver += 1;
        let (at, ver) = (t + end.rto, end.rto_ver);
        self.push(at, Ev::TcpRto { end: e, ver });
    }

    /// Puts one segment of end `e` on the wire at `t`, counting its bytes before anything can drop it.
    #[allow(clippy::too_many_arguments)]
    fn tcp_pkt(
        &mut self,
        t: Time,
        e: u32,
        kind: SegKind,
        seq: u64,
        len: u32,
        ack: Option<u64>,
        sack: Sack,
        extra: u32,
    ) {
        let end = &self.ends[e as usize];
        let (n, src, dst) = (end.node as usize, end.local, end.remote);
        let size = TCP_HDR + len + extra;
        let m = &mut self.metrics.nodes[n];
        m.stream_packets += 1;
        m.stream_wire_bytes += u64::from(size);
        m.wire_bytes += u64::from(size);
        let Some(from_site) = self.nodes[n]
            .ifaces
            .iter()
            .find(|i| i.up && i.addr == src.ip())
            .map(|i| i.site)
        else {
            self.count_drop(t, crate::metrics::DropReason::NoIface, size as usize);
            return;
        };
        let seg = Seg {
            kind,
            from: e,
            seq,
            len,
            ack,
            sack,
            size,
        };
        let pkt = self.alloc_seg(src, dst, seg, n as u32, t);
        self.route_from(t, from_site, pkt);
    }

    /// A segment reached node `n` (the middlebox and the firewall have let it through).
    pub(crate) fn tcp_input(&mut self, t: Time, n: usize, dst: SocketAddr, src: SocketAddr, seg: Seg) {
        let src_end = seg.from;
        if seg.kind == SegKind::Syn {
            self.tcp_syn_input(t, n, dst, src, src_end);
            return;
        }
        let Some(e) = self.ends[src_end as usize].peer else {
            return;
        };
        let end = &self.ends[e as usize];
        if end.node as usize != n || end.closed {
            return;
        }
        match seg.kind {
            SegKind::SynAck => self.tcp_synack_input(t, e),
            SegKind::Ack => {
                if self.ends[e as usize].state == State::SynRcvd {
                    self.ends[e as usize].state = State::Est;
                    self.tcp_server_est(t, e);
                }
                if let Some(ack) = seg.ack {
                    self.tcp_ack(t, e, ack, seg.sack);
                }
            }
            SegKind::Data => self.tcp_data(t, e, seg.seq, u64::from(seg.len)),
            SegKind::Syn => {}
        }
    }

    fn tcp_syn_input(&mut self, t: Time, n: usize, dst: SocketAddr, src: SocketAddr, src_end: u32) {
        let src_simul = self.ends[src_end as usize].simul;
        if let Some(&(ln, kind)) = self.listeners.get(&(dst.ip(), dst.port()))
            && !src_simul
            && ln as usize == n
        {
            let h = self.nodes[n].next_stream;
            self.nodes[n].next_stream += 1;
            let e = self.ends.len() as u32;
            let mut end = TcpEnd::new(n as u32, h, false, kind, dst, src);
            end.peer = Some(src_end);
            self.ends.push(end);
            self.ends[src_end as usize].peer = Some(e);
            self.nodes[n].streams.insert(h, e);
            self.tcp_pkt(t, e, SegKind::SynAck, 0, 0, None, Sack::default(), 8);
            return;
        }
        let mut found = None;
        for &e in self.nodes[n].streams.values() {
            let x = &self.ends[e as usize];
            if x.simul && x.state == State::Syn && x.remote.ip() == src.ip() && src_simul {
                found = Some(e);
            }
        }
        if let Some(e) = found {
            self.ends[e as usize].peer = Some(src_end);
            self.ends[src_end as usize].peer = Some(e);
            self.ends[e as usize].remote = src;
            self.tcp_pkt(t, e, SegKind::SynAck, 0, 0, None, Sack::default(), 8);
        }
    }

    fn tcp_synack_input(&mut self, t: Time, e: u32) {
        match self.ends[e as usize].state {
            State::Syn => {
                let end = &mut self.ends[e as usize];
                end.state = State::Est;
                end.rto_ver += 1;
                self.tcp_pkt(t, e, SegKind::Ack, 0, 0, Some(0), Sack::default(), 0);
                if self.ends[e as usize].ws {
                    self.ends[e as usize].setup = 1;
                    self.tcp_write(t, e, Vec::new(), TLS_SETUP_C2S, true);
                } else {
                    self.tcp_opened(t, e);
                }
            }
            State::SynRcvd => {
                self.ends[e as usize].state = State::Est;
                self.tcp_pkt(t, e, SegKind::Ack, 0, 0, Some(0), Sack::default(), 0);
                self.tcp_server_est(t, e);
            }
            _ => {}
        }
    }

    fn tcp_server_est(&mut self, t: Time, e: u32) {
        if !self.ends[e as usize].ws {
            self.tcp_opened(t, e);
        }
    }

    fn tcp_opened(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        if end.state == State::Open {
            return;
        }
        end.state = State::Open;
        let (n, h, remote) = (end.node, end.handle, end.remote);
        self.metrics.carriers_opened += 1;
        if self.nodes[n as usize].state == NodeState::Up {
            self.deliver_stream_input(
                t,
                n,
                StreamInput::Event(StreamEvent::Opened {
                    stream: StreamId(h),
                    remote,
                }),
            );
        }
    }

    /// Queues one record (or one setup exchange, which carries no payload) for sending at `t`.
    pub(crate) fn tcp_write(&mut self, t: Time, e: u32, data: Vec<u8>, setup_len: u64, setup: bool) {
        let end = &mut self.ends[e as usize];
        let n = if setup {
            setup_len
        } else {
            let overhead = if end.ws {
                TLS_RECORD + if end.is_client { WS_C2S } else { WS_S2C }
            } else {
                0
            };
            data.len() as u64 + overhead
        };
        end.snd_end += n;
        let end_seq = end.snd_end;
        end.records.push_back(Rec { end_seq, data, setup });
        self.tcp_try_send(t, e);
    }

    fn tcp_try_send(&mut self, t: Time, e: u32) {
        loop {
            let end = &mut self.ends[e as usize];
            // After a timeout the send point can lie below the acknowledged point (late ACKs arrive for data sent before
            // the rollback); the flight is then negative, as in the reference.
            if end.snd_nxt >= end.snd_end
                || end.snd_nxt.cast_signed() - end.snd_una.cast_signed() >= end.cwnd.min(4 << 20).cast_signed()
            {
                break;
            }
            let len = MSS.min(end.snd_end - end.snd_nxt);
            let seq = end.snd_nxt;
            end.inflight.insert(
                seq,
                Inflight {
                    len: len as u32,
                    sent: t,
                    retx: false,
                },
            );
            end.snd_nxt += len;
            self.tcp_pkt(t, e, SegKind::Data, seq, len as u32, None, Sack::default(), 0);
        }
        let end = &mut self.ends[e as usize];
        if end.snd_una < end.snd_nxt && end.rto_count == 0 {
            end.rto_ver += 1;
            let (at, ver) = (t + end.rto, end.rto_ver);
            self.push(at, Ev::TcpRto { end: e, ver });
        }
    }

    fn tcp_data(&mut self, t: Time, e: u32, seq: u64, len: u64) {
        let end = &mut self.ends[e as usize];
        if seq == end.rcv_nxt {
            end.rcv_nxt += len;
            while let Some(l) = end.ooo.remove(&end.rcv_nxt) {
                end.rcv_nxt += u64::from(l);
            }
            end.unacked_segs += 1;
            self.tcp_deliver(t, e);
            let end = &mut self.ends[e as usize];
            if end.unacked_segs >= 2 || !end.ooo.is_empty() {
                self.tcp_send_ack(t, e);
            } else {
                end.delack_ver += 1;
                let ver = end.delack_ver;
                self.push(t + 40 * MS, Ev::TcpDelack { end: e, ver });
            }
        } else {
            if seq > end.rcv_nxt && end.ooo.len() < 4096 {
                end.ooo.insert(seq, len as u32);
            }
            end.unacked_segs += 1;
            self.tcp_send_ack(t, e);
        }
    }

    pub(crate) fn tcp_send_ack(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        end.unacked_segs = 0;
        end.delack_ver += 1;
        let mut sack = Sack::default();
        for (&s, &l) in end.ooo.iter().take(4) {
            sack.blocks[usize::from(sack.n)] = (s, l);
            sack.n += 1;
        }
        let ack = end.rcv_nxt;
        self.tcp_pkt(t, e, SegKind::Ack, 0, 0, Some(ack), sack, 0);
    }

    /// Hands the receiving end every record of its peer that the cumulative ACK point now covers.
    fn tcp_deliver(&mut self, t: Time, e: u32) {
        let Some(p) = self.ends[e as usize].peer else {
            return;
        };
        loop {
            let upto = self.ends[e as usize].rcv_nxt;
            let peer = &mut self.ends[p as usize];
            if peer.records.front().is_none_or(|r| r.end_seq > upto) {
                break;
            }
            let Some(rec) = peer.records.pop_front() else { break };
            if rec.setup {
                self.ws_setup_step(t, e);
            } else if self.ends[e as usize].state == State::Open {
                self.carrier_record(t, e, rec.data);
            }
        }
    }

    /// The WebSocket setup: TLS client hello, TLS server flight, upgrade request, upgrade response.
    fn ws_setup_step(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        end.setup += 1;
        match (end.is_client, end.setup) {
            (false, 1) => self.tcp_write(t, e, Vec::new(), TLS_SETUP_S2C, true),
            (false, 2) => {
                self.tcp_write(t, e, Vec::new(), WS_UPGRADE_S2C, true);
                self.tcp_opened(t, e);
            }
            (true, 2) => self.tcp_write(t, e, Vec::new(), WS_UPGRADE_C2S, true),
            (true, 3) => self.tcp_opened(t, e),
            _ => {}
        }
    }

    fn tcp_ack(&mut self, t: Time, e: u32, ack: u64, sack: Sack) {
        let end = &mut self.ends[e as usize];
        if ack > end.snd_una {
            if let Some(first) = end.inflight.get(&end.snd_una).copied()
                && !first.retx
            {
                let sample = t - first.sent;
                if end.srtt == 0 {
                    end.srtt = sample;
                    end.rttvar = sample / 2;
                } else {
                    end.rttvar = (3 * end.rttvar + end.srtt.abs_diff(sample)) / 4;
                    end.srtt = (7 * end.srtt + sample) / 8;
                }
                end.rto = (200 * MS).max(end.srtt + 4 * end.rttvar);
            }
            let newly = ack - end.snd_una;
            end.inflight = end.inflight.split_off(&ack);
            end.snd_una = ack;
            end.dupacks = 0;
            end.rto_count = 0;
            if end.srtt != 0 {
                // Forward progress resets the exponential backoff.
                end.rto = (200 * MS).max(end.srtt + 4 * end.rttvar);
            }
            if end.in_recovery && ack >= end.recover {
                end.in_recovery = false;
                end.cwnd = end.ssthresh;
            } else if end.cwnd < end.ssthresh {
                end.cwnd += newly;
            } else {
                end.cwnd += (MSS * newly / end.cwnd.max(1)).max(1);
            }
            end.rto_ver += 1;
            if end.snd_una < end.snd_nxt {
                let (at, ver) = (t + end.rto, end.rto_ver);
                self.push(at, Ev::TcpRto { end: e, ver });
            }
        } else if ack == end.snd_una && end.snd_una < end.snd_nxt {
            end.dupacks += 1;
            let flight = end.snd_nxt - end.snd_una;
            if end.dupacks <= 2 && end.snd_nxt < end.snd_end {
                // Limited transmit: one new segment per early duplicate ACK.
                let len = MSS.min(end.snd_end - end.snd_nxt);
                let seq = end.snd_nxt;
                end.inflight.insert(
                    seq,
                    Inflight {
                        len: len as u32,
                        sent: t,
                        retx: false,
                    },
                );
                end.snd_nxt += len;
                self.tcp_pkt(t, e, SegKind::Data, seq, len as u32, None, Sack::default(), 0);
            }
            let end = &mut self.ends[e as usize];
            if end.dupacks >= 2 && flight <= 4 * MSS && !end.in_recovery {
                // Early retransmit for small flights.
                end.in_recovery = true;
                end.recover = end.snd_nxt;
                end.ssthresh = (flight / 2).max(2 * MSS);
                end.cwnd = end.ssthresh;
                self.tcp_retx_holes(t, e, sack);
            } else if end.dupacks == 3 && !end.in_recovery {
                end.in_recovery = true;
                end.recover = end.snd_nxt;
                let flight = end.snd_nxt - end.snd_una;
                end.ssthresh = (flight / 2).max(2 * MSS);
                end.cwnd = end.ssthresh;
                self.tcp_retx_holes(t, e, sack);
            } else if end.in_recovery && end.dupacks.is_multiple_of(3) {
                self.tcp_retx_holes(t, e, sack);
            }
        }
        self.tcp_try_send(t, e);
    }

    /// Retransmits the unacknowledged segments below the highest selectively acknowledged byte (at most 8 with SACK, 1 without).
    fn tcp_retx_holes(&mut self, t: Time, e: u32, sack: Sack) {
        let end = &self.ends[e as usize];
        let has_sack = sack.n > 0;
        let hi = sack
            .blocks()
            .iter()
            .fold(end.snd_una, |h, (s, l)| h.max(s + u64::from(*l)));
        let floor = end.srtt.max(50 * MS);
        let mut todo = Vec::new();
        for (&seq, info) in &end.inflight {
            if seq >= hi && has_sack {
                break;
            }
            if sack.blocks().iter().any(|(s, _)| *s == seq) || (info.retx && t - info.sent < floor) {
                continue;
            }
            todo.push((seq, info.len));
            if todo.len() >= 8 || !has_sack {
                break;
            }
        }
        for (seq, len) in todo {
            if let Some(info) = self.ends[e as usize].inflight.get_mut(&seq) {
                info.sent = t;
                info.retx = true;
            }
            self.tcp_pkt(t, e, SegKind::Data, seq, len, None, Sack::default(), 0);
        }
    }

    /// The retransmission timer fired: retry the SYN, or go back to the first unacknowledged byte.
    pub(crate) fn tcp_rto(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        if end.state == State::Syn {
            end.rto_count += 1;
            if end.rto_count > 5 {
                self.tcp_fail(t, e);
                return;
            }
            end.rto = (end.rto * 2).min(30 * SEC);
            self.tcp_syn(t, e);
            return;
        }
        if end.snd_una >= end.snd_nxt {
            return;
        }
        end.rto_count += 1;
        if end.rto_count > 8 {
            self.tcp_fail(t, e);
            return;
        }
        let flight = end.snd_nxt - end.snd_una;
        end.ssthresh = (flight / 2).max(2 * MSS);
        end.cwnd = MSS;
        end.rto = (end.rto * 2).min(60 * SEC);
        end.in_recovery = false;
        end.inflight.clear();
        end.snd_nxt = end.snd_una;
        end.rto_ver += 1;
        let (at, ver) = (t + end.rto, end.rto_ver);
        self.push(at, Ev::TcpRto { end: e, ver });
        let end = &mut self.ends[e as usize];
        let len = MSS.min(end.snd_end - end.snd_nxt);
        let seq = end.snd_nxt;
        end.inflight.insert(
            seq,
            Inflight {
                len: len as u32,
                sent: t,
                retx: true,
            },
        );
        end.snd_nxt += len;
        self.tcp_pkt(t, e, SegKind::Data, seq, len as u32, None, Sack::default(), 0);
    }

    /// The connection is dead: tell the node unless it is gone.
    pub(crate) fn tcp_fail(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        end.closed = true;
        let (n, h) = (end.node, end.handle);
        end.release();
        self.nodes[n as usize].streams.remove(&h);
        self.free_records(e);
        self.metrics.streams_failed += 1;
        self.notify_stream(t, n, StreamEvent::Failed { stream: StreamId(h) });
    }

    /// Closes end `e`. With `notify_peer` a FIN (52 bytes, counted) tells the peer after the one-way delay, without
    /// loss, partition or NAT check; without it the node itself learns of the close.
    pub(crate) fn tcp_close(&mut self, t: Time, e: u32, notify_peer: bool) {
        let end = &mut self.ends[e as usize];
        if end.closed {
            return;
        }
        end.closed = true;
        let (n, h, peer) = (end.node, end.handle, end.peer);
        end.release();
        self.nodes[n as usize].streams.remove(&h);
        self.free_records(e);
        if notify_peer {
            let Some(p) = peer.filter(|p| !self.ends[*p as usize].closed) else {
                return;
            };
            let d = self.fin_delay(e, p);
            let m = &mut self.metrics.nodes[n as usize];
            m.stream_packets += 1;
            m.stream_wire_bytes += u64::from(TCP_HDR);
            m.wire_bytes += u64::from(TCP_HDR);
            self.push(t + d, Ev::TcpPeerClosed { end: p });
        } else {
            self.notify_stream(t, n, StreamEvent::Closed { stream: StreamId(h) });
        }
    }

    /// The peer's FIN arrived.
    pub(crate) fn tcp_peer_closed(&mut self, t: Time, e: u32) {
        let end = &mut self.ends[e as usize];
        if end.closed {
            return;
        }
        end.closed = true;
        let (n, h) = (end.node, end.handle);
        end.release();
        self.nodes[n as usize].streams.remove(&h);
        self.free_records(e);
        self.notify_stream(t, n, StreamEvent::Closed { stream: StreamId(h) });
    }

    /// Drops the record queues of a connection once both its ends are closed.
    fn free_records(&mut self, e: u32) {
        let Some(p) = self.ends[e as usize].peer else {
            self.ends[e as usize].records = VecDeque::new();
            return;
        };
        if self.ends[p as usize].closed {
            self.ends[e as usize].records = VecDeque::new();
            self.ends[p as usize].records = VecDeque::new();
        }
    }

    /// The delayed-ACK timer fired.
    pub(crate) fn tcp_delack(&mut self, t: Time, e: u32, ver: u64) {
        let end = &self.ends[e as usize];
        if ver == end.delack_ver && !end.closed && end.unacked_segs > 0 {
            self.tcp_send_ack(t, e);
        }
    }

    /// The retransmission timer event: ignored when stale.
    pub(crate) fn on_tcp_rto(&mut self, t: Time, e: u32, ver: u64) {
        let end = &self.ends[e as usize];
        if ver == end.rto_ver && !end.closed {
            self.tcp_rto(t, e);
        }
    }

    /// A SYN refused with a reset: the connect fails.
    pub(crate) fn on_tcp_fail(&mut self, t: Time, e: u32) {
        if !self.ends[e as usize].closed {
            self.tcp_fail(t, e);
        }
    }
}
