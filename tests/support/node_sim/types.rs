//! The types of the simulated node: the stores and sizes it is built with, the scenario's commands and events, and
//! the relay-side stream state of a hub.

use super::*;

/// The chunks of each session's buffer pool unless a test asks for fewer. A hub session carries a stream in each
/// direction (the hub opens its own as soon as it accepts, to send the replay floor), each with its receive window
/// charged to the pool, beside the send buffers.
const CHUNKS_PER_CONN: usize = 64;

thread_local! {
    static POOL_CHUNKS: std::cell::Cell<usize> = const { std::cell::Cell::new(CHUNKS_PER_CONN) };
}

/// Run `f`, which builds its nodes, with `chunks` chunks in every session's buffer pool.
pub fn with_pool_chunks<T>(chunks: usize, f: impl FnOnce() -> T) -> T {
    let before = POOL_CHUNKS.replace(chunks);
    let out = f();
    POOL_CHUNKS.set(before);
    out
}

pub const NK: usize = 24;
pub const ND: usize = 384;
pub const NRL: usize = 4;
pub const NPEERS: usize = 32;
pub type NEpS<S> = Endpoint<'static, 'static, Caps, S, CN, CC, CF, CNP, NK, ND, CPK, CTK, CCT>;
pub type NEp = NEpS<NoSource>;

/// What a simulated node needs of the host stores of the layers above broadcast: the node's `Apps` and the stream
/// source type its endpoint is built with.
pub trait SimApps: Apps<Caps> + Clone + 'static {
    type Src: StreamSource + ServeSource<<Self as Apps<Caps>>::Values> + 'static;
}

impl SimApps for NoApps {
    type Src = NoSource;
}

/// The relay-path address family and index the hub's own relay uses for its members: an index no client has.
pub(super) const LOCAL_RELAY: u8 = 0xFE;

fn memory_of<S: StreamSource + 'static>(machines: &Machines) -> Resources<'static, S, CN, CC, CF> {
    let pool = BufferPool::new_boxed(POOL_CHUNKS.get());
    let streams: &'static mut Streams<S, CN, CC> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    Resources {
        pool,
        streams: streams.into(),
        loss: loss.into(),
        tables: Tables::sharing(machines),
    }
}

pub(super) fn node_slots<S: StreamSource + 'static>() -> &'static mut [Slot<'static, Caps, S, CN, CC, CF, CNP>; NK] {
    let machines = Machines::new();
    let v: Vec<Slot<'static, Caps, S, CN, CC, CF, CNP>> =
        (0..NK).map(|_| Slot::new(memory_of::<S>(&machines))).collect();
    let b: Box<[Slot<'static, Caps, S, CN, CC, CF, CNP>; NK]> = v.into_boxed_slice().try_into().ok().unwrap();
    Box::leak(b)
}

/// The incarnation epoch kept sealed by a software key store, as a host would keep it.
#[derive(Clone)]
pub struct SealStore {
    pub persist: bool,
    pub ks: Rc<RefCell<SoftwareStore>>,
    pub blob: Rc<RefCell<Vec<u8>>>,
}

impl Store for SealStore {
    fn persistent(&self) -> bool {
        self.persist
    }

    fn load(&mut self) -> Result<Option<u64>, StoreError> {
        let blob = self.blob.borrow().clone();
        if blob.is_empty() {
            return Ok(None);
        }
        let plain = self.ks.borrow_mut().unseal(&blob).map_err(|_| StoreError)?;
        let b: [u8; 8] = plain.as_slice().try_into().map_err(|_| StoreError)?;
        Ok(Some(u64::from_be_bytes(b)))
    }

    fn save(&mut self, epoch: u64) -> Result<(), StoreError> {
        let sealed = self
            .ks
            .borrow_mut()
            .seal(&epoch.to_be_bytes())
            .map_err(|_| StoreError)?;
        *self.blob.borrow_mut() = sealed;
        Ok(())
    }
}

pub type NodeT<A = NoApps> = Node<NEpS<<A as SimApps>::Src>, Caps, SealStore, NRL, NPEERS, A>;
pub type HubRelay = Relay<24, 16, 8, 4096>;

/// How to reach a hub.
#[derive(Debug, Clone, Copy)]
pub struct HubAddr {
    pub id: NodeId,
    pub udp: SocketAddr,
    pub tcp: SocketAddr,
    pub ws: SocketAddr,
}

/// How a simulated node is built.
#[derive(Clone)]
pub struct NodeSpec {
    pub tag: u8,
    pub addr: SocketAddr,
    pub hubs: Vec<HubAddr>,
    pub is_hub: bool,
    pub persist: bool,
    pub limits: Limits,
    pub trace: bool,
    pub start: u64,
}

pub fn id_of(tag: u8) -> NodeId {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    kp.node_id()
}

/// The address of a hub as clients reach it.
pub fn hub_addr(tag: u8, ip: std::net::IpAddr) -> HubAddr {
    HubAddr {
        id: id_of(tag),
        udp: SocketAddr::new(ip, 4433),
        tcp: SocketAddr::new(ip, 443),
        ws: SocketAddr::new(ip, 8443),
    }
}

/// A command from the scenario.
#[derive(Debug, Clone)]
pub enum NCmd {
    Tick,
    Subscribe(Vec<u8>),
    Unsubscribe(Vec<u8>),
    Publish {
        topic: Vec<u8>,
        body: Vec<u8>,
    },
    Leave,
    Revoke([u8; 32]),
    AddressChanged,
    /// Close every carrier stream of the node (a middlebox reset), as the client sees it.
    DropCarriers,
    /// Answer the access checks of the endpoint with refusals from now on.
    Deny(bool),
    /// Answer the broadcast access checks with this verdict from now on.
    BroadcastAllow(bool),
    /// Fetch a value from providers (node ids).
    ValuesFetch {
        root: [u8; 32],
        length: u64,
        ranges: Vec<(u64, u64)>,
        providers: Vec<[u8; 32]>,
        /// The time (nanoseconds) at which the fetch ends if it has not, `None` for no deadline.
        deadline: Option<u64>,
    },
    /// Cancel a fetch.
    ValuesCancel(u32),
    /// Start a reconcile round against a peer.
    SetsStart {
        peer: [u8; 32],
        set_ref: Vec<u8>,
    },
    /// Create a bundle for a recipient.
    DtnSend {
        to: Box<pinc_dtn::seal::RecipientKeys>,
        payload: Vec<u8>,
        plan: pinc_node::DtnPlan,
    },
}

/// What the scenario reads of a node.
#[derive(Debug, Clone)]
pub enum NEv {
    Node(NodeEvent),
    Stream(StreamEvent),
    Relay(Trace),
}

pub(super) enum Eff {
    Carrier(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, RSession),
    Trace(Trace),
}

#[derive(Default)]
pub(super) struct Collect(pub(super) Vec<Eff>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        self.0.push(match e {
            Effect::Carrier { to, frame } => {
                let mut b = vec![0u8; MAX_FRAME_LEN];
                let n = frame.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Carrier(to, b)
            }
            Effect::Udp { to, datagram } => {
                let mut b = vec![0u8; 2048];
                let n = datagram.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Udp(to, b)
            }
            Effect::Local { from, packet } => Eff::Local(from, packet.to_vec()),
            Effect::Close { node, session, .. } => Eff::Close(node, session),
            Effect::PeerRelay { .. } | Effect::Wake { .. } => return,
            Effect::Trace(t) => Eff::Trace(t),
        });
    }
}

pub(super) struct RStream {
    pub(super) carrier: Box<ProtectedCarrier<Caps>>,
    pub(super) node: Option<NodeId>,
    pub(super) session: Option<RSession>,
    pub(super) ws: Option<Decoder>,
    pub(super) sniffed: bool,
}

/// The relay a hub runs for its members.
pub(super) struct HubSide {
    pub(super) relay: Box<HubRelay>,
    pub(super) streams: HashMap<StreamId, RStream>,
    pub(super) by_node: HashMap<NodeId, StreamId>,
    pub(super) stores: ResponderStores<4, 4>,
    pub(super) slots: Vec<NodeId>,
    pub(super) scid: u64,
}

pub(super) enum Step {
    Idle,
    Flush,
    Frame,
    Open(NodeId),
    Dead,
}

pub(super) fn wrap(rs: &RStream, bytes: &[u8]) -> Vec<u8> {
    if rs.ws.is_some() {
        let mut f = vec![0u8; bytes.len() + 16];
        let n = ws::encode(Opcode::Binary, bytes, None, &mut f).unwrap();
        f.truncate(n);
        f
    } else {
        bytes.to_vec()
    }
}
