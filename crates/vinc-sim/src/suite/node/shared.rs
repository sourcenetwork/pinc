//! What every node of one run shares: the world, the recorder, the ledger and the directory of nodes.
//!
//! [`Shared`] is built once per run and held in an `Rc` by every [`super::SuiteNode`]. Its directory maps a world
//! index to the node id of its deterministic identity and back, and lists the public addresses a dial can use; a node
//! with no public interface (a home behind a NAT, a browser) has none, so a dial to it cannot start.
//!
//! Invariants: the identity of node `i` depends only on the world seed and `i`, so the directory, the nodes and every
//! rerun agree; the directory never changes during a run; an address is derived from a world host number by
//! [`iface_ip`], the one function the runner must also use to give the simulator's interfaces their addresses.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::rc::Rc;

use vinc_connect::client::RelayCfg;
use vinc_crypto::{CryptoError, IdentityAlg, Keypair, NodeId, Provider, Software};
use vinc_security::{KeyHandle, LocalIdentity};

use crate::suite::crypto::{DeviceCosts, Registry};
use crate::suite::rec::Rec;
use crate::suite::world::model::{Addr, EnvArg, EnvKind, World};

/// Why a run's shared state or a node could not be set up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetupError {
    /// The node index is not in the world.
    NoSuchNode(usize),
    /// A node names a device class the cost table does not know.
    UnknownDevice(usize),
    /// An interface of a node has an address kind this adapter cannot place.
    BadAddress(usize),
    /// The identity key could not be made.
    Identity(CryptoError),
}

impl core::fmt::Display for SetupError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoSuchNode(i) => write!(f, "node {i} is not in the world"),
            Self::UnknownDevice(i) => write!(f, "node {i} has an unknown device class"),
            Self::BadAddress(i) => write!(f, "node {i} has an interface address of an unknown kind"),
            Self::Identity(e) => write!(f, "the node identity could not be made: {e}"),
        }
    }
}

impl core::error::Error for SetupError {}

/// The simulator address of a world host number: `udp4` and `tcp4` hosts map into `10.0.0.0/8`, `udp6` hosts into
/// `fd00::/16`. The runner gives the simulator's interfaces (and NATs) exactly these addresses, and nodes learn which
/// of their interfaces an interface event is about from them. `None` for an address kind this adapter does not carry
/// (every kind except `udp4`, `udp6`, `tcp4`).
pub fn iface_ip(addr: &Addr) -> Option<IpAddr> {
    match addr.kind.as_str() {
        "udp4" | "tcp4" => Some(IpAddr::V4(Ipv4Addr::from(
            0x0A00_0000 | (addr.host as u32 & 0x00FF_FFFF),
        ))),
        "udp6" => Some(IpAddr::V6(Ipv6Addr::new(
            0xfd00,
            0,
            0,
            0,
            0,
            (addr.host >> 32) as u16,
            (addr.host >> 16) as u16,
            addr.host as u16,
        ))),
        _ => None,
    }
}

/// The 32 seed bytes of the identity of node `idx` in the world seeded `world_seed`.
pub fn identity_seed(world_seed: u64, idx: usize) -> [u8; 32] {
    derive(b"suite-identity", world_seed, idx as u64, 0)
}

/// A deterministic 32-byte value from a label and three numbers (not a key schedule: it only spreads seeds).
pub(super) fn derive(label: &[u8], a: u64, b: u64, c: u64) -> [u8; 32] {
    let mut msg = Vec::with_capacity(label.len() + 24);
    msg.extend_from_slice(label);
    for n in [a, b, c] {
        msg.extend_from_slice(&n.to_be_bytes());
    }
    Software.sha256(&msg)
}

/// The shared state of one run; see the module docs.
pub struct Shared {
    /// The world being run.
    pub world: Rc<World>,
    /// The recorder every node reports to.
    pub rec: Rc<RefCell<Rec>>,
    /// The ledger of the instrumented crypto.
    pub registry: &'static Registry,
    ids: Vec<NodeId>,
    by_id: BTreeMap<[u8; 32], usize>,
    public: Vec<Vec<SocketAddr>>,
    costs: Vec<DeviceCosts>,
    stateless: BTreeSet<(usize, u64)>,
    restarts: BTreeSet<(usize, u64)>,
    relays: Vec<RelayCfg>,
}

impl Shared {
    /// The shared state of a run of `world` reporting to `rec` and `registry`.
    ///
    /// # Errors
    /// A [`SetupError`] if a node has an unknown device class or an interface address this adapter cannot place, or an
    /// identity cannot be derived.
    pub fn new(world: Rc<World>, rec: Rc<RefCell<Rec>>, registry: &'static Registry) -> Result<Rc<Self>, SetupError> {
        let mut ids = Vec::with_capacity(world.nodes.len());
        let mut by_id = BTreeMap::new();
        let mut public = Vec::with_capacity(world.nodes.len());
        let mut costs = Vec::with_capacity(world.nodes.len());
        for (i, n) in world.nodes.iter().enumerate() {
            let (_, identity) = make_identity(world.seed, i)?;
            ids.push(identity.node_id());
            by_id.insert(identity.node_id().bytes, i);
            costs.push(DeviceCosts::named(&n.device).ok_or(SetupError::UnknownDevice(i))?);
            let mut addrs = Vec::new();
            for f in n.ifaces.iter().filter(|f| f.kind.starts_with("udp")) {
                let ip = iface_ip(&f.addr).ok_or(SetupError::BadAddress(i))?;
                if f.public {
                    addrs.push(SocketAddr::new(ip, f.addr.port));
                }
            }
            public.push(addrs);
        }
        let stateless = world
            .env
            .iter()
            .filter(|a| a.kind == EnvKind::Restart && a.arg == EnvArg::Flag(false))
            .map(|a| (a.node, a.t))
            .collect();
        let restarts = world
            .env
            .iter()
            .filter(|a| a.kind == EnvKind::Restart)
            .map(|a| (a.node, a.t))
            .collect();
        let relays = relay_cfgs(&world, &ids);
        Ok(Rc::new(Self {
            world,
            rec,
            registry,
            ids,
            by_id,
            public,
            costs,
            stateless,
            restarts,
            relays,
        }))
    }

    /// The node id of world node `idx`.
    pub fn node_id(&self, idx: usize) -> Option<NodeId> {
        self.ids.get(idx).copied()
    }

    /// The world index of a node id, if it is a node of the world.
    pub fn index_of(&self, id: &NodeId) -> Option<usize> {
        self.by_id.get(&id.bytes).copied()
    }

    /// The world index of a node id given as its bytes, if it is a node of the world.
    pub fn index_of_bytes(&self, id: &[u8; 32]) -> Option<usize> {
        self.by_id.get(id).copied()
    }

    /// The relays every node is configured with: the bootstrap nodes, reachable on UDP, TCP and WebSocket.
    pub fn relays(&self) -> &[RelayCfg] {
        &self.relays
    }

    /// Whether node `idx` is a hub (a bootstrap node, which also runs the relay).
    pub fn is_hub(&self, idx: usize) -> bool {
        self.world.bootstrap.contains(&idx)
    }

    /// The stack version node `idx` announces when it starts at `t`: 1, or the version of the last upgrade before `t`.
    pub fn version_at(&self, idx: usize, t: u64) -> u16 {
        self.world
            .env
            .iter()
            .filter(|a| a.node == idx && a.kind == EnvKind::Upgrade && a.t < t)
            .filter_map(|a| match a.arg {
                EnvArg::Num(v) => u16::try_from(v).ok(),
                _ => None,
            })
            .next_back()
            .unwrap_or(1)
    }

    /// The public socket addresses of node `idx` (empty for a node with no public interface), IPv4 first.
    pub fn public_addrs(&self, idx: usize) -> &[SocketAddr] {
        self.public.get(idx).map_or(&[], Vec::as_slice)
    }

    /// The cost table of node `idx`'s device class.
    pub fn costs(&self, idx: usize) -> DeviceCosts {
        self.costs.get(idx).copied().unwrap_or(DeviceCosts::DESKTOP)
    }

    /// Whether the world has a `restart` action for `idx` at exactly `t`. The reference opens a resume record for every
    /// such action, whether or not the state is kept, and for no other start (an upgrade does not).
    pub(super) fn restart_action_at(&self, idx: usize, t: u64) -> bool {
        self.restarts.contains(&(idx, t))
    }

    /// Whether a restart of `idx` at a time in `(after, at]` is one that keeps no state (`restart` with a false
    /// flag). The runner must schedule `Sim::restart` at the action's time for the match to hold.
    pub(super) fn restarts_stateless(&self, idx: usize, after: u64, at: u64) -> bool {
        after < at && self.stateless.range((idx, after + 1)..=(idx, at)).next().is_some()
    }
}

/// The relay entry of each bootstrap node: its public UDP address and the TCP and WebSocket carrier addresses of the
/// same host.
fn relay_cfgs(world: &World, ids: &[NodeId]) -> Vec<RelayCfg> {
    world
        .bootstrap
        .iter()
        .filter_map(|&h| {
            let node = world.nodes.get(h)?;
            let addr = |kind: &str| {
                node.ifaces
                    .iter()
                    .find(|f| f.kind == kind && f.public)
                    .and_then(|f| Some(SocketAddr::new(iface_ip(&f.addr)?, f.addr.port)))
            };
            Some(RelayCfg {
                id: *ids.get(h)?,
                udp: addr("udp4"),
                tcp: addr("tcp"),
                ws: addr("ws"),
            })
        })
        .collect()
}

/// The key pair and the local identity of node `idx`.
pub(super) fn make_identity(world_seed: u64, idx: usize) -> Result<(Keypair, LocalIdentity), SetupError> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &identity_seed(world_seed, idx)).map_err(SetupError::Identity)?;
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).map_err(SetupError::Identity)?;
    Ok((kp, id))
}
