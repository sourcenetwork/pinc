//! A simulated VINC node: the real `vinc_node::Node` (endpoint, connectivity client, membership, broadcast) with the
//! host duties around it: carriers over simulated TCP and WebSocket streams, key answers, access checks, and, for a hub,
//! the relay that accepts the carriers of its members.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::large_stack_arrays,
    clippy::too_many_lines,
    clippy::wildcard_imports
)]

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;
use std::rc::Rc;

use vinc_broadcast::Limits;
use vinc_connect::carrier::MAX_FRAME_LEN;
use vinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use vinc_connect::client::{Config as ConnCfg, Io, Kind, RelayCfg};
use vinc_connect::relay::{Config as RelayConfig, Effect, Relay, SessionId as RSession, Sink, Trace, UdpTarget};
use vinc_core::{Command, Endpoint, EndpointConfig, Event, Query, Slot, relay_addr, relay_parts};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use vinc_keystore::{KeyStore, SoftwareStore};
use vinc_membership::session::StoreError;
use vinc_node::{
    Apps, Config as NodeConfig, DtnRestored, HUB_ALPN, MemberNotice, NoApps, Node, NodeEvent, ServeSource, Store,
    TraceItem, is_relay_request,
};
use vinc_security::{ConnId, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys};
use vinc_sim::{Clock, IfaceEvent, StreamEvent, StreamId, StreamKind, StreamOp, Time, WALL_EPOCH};
use vinc_transport::conn::{Machines, Resources, Tables};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, StreamSource, Streams};

use crate::Caps;
use crate::connect_host::{Outbox, answer_parts};
use crate::core_net::{CC, CCT, CF, CN, CNP, CPK, CTK, metered};

mod build;
mod contract;
mod pump;
mod relay;
mod types;
pub use types::*;

pub struct SimNode<A: SimApps = NoApps> {
    pub node: Box<NodeT<A>>,
    apps: A,
    pub spec: NodeSpec,
    pub me: NodeId,
    prov: Caps,
    kp: Keypair,
    prekeys: SoftPrekeys<Caps>,
    hdrbg: Drbg,
    deny: bool,
    bc_allow: bool,
    seal: SealStore,
    clock: Clock,
    // the node as a client of the relays
    streams: [Option<StreamId>; NRL],
    opening: [Option<SocketAddr>; NRL],
    kinds: [Kind; NRL],
    cws: [Option<Decoder>; NRL],
    // the node as a hub
    hub: Option<HubSide>,
    pub out: Outbox,
    pub events: VecDeque<NEv>,
    pub traces: Vec<(Time, TraceItem)>,
    /// How many times the host called `handle_timeout`.
    pub timeouts: u64,
    /// What the last restart found in the delay-tolerant records.
    pub restored: DtnRestored,
    now: Time,
    down: bool,
    pub addr: SocketAddr,
    /// Incarnations the node announced over its lives, for the monotonicity checks.
    pub incarnations: Vec<u64>,
    /// A slow carrier reader: what a relay stream delivers within this span of the first record is read by the node
    /// in one call (0 for each record on its own).
    pub carrier_hold: Time,
    held: Vec<(Time, usize, Vec<u8>)>,
}
