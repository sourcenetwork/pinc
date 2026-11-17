//! Building a simulated node: the node and its keys from a spec, and the constructors that seal its records.

use super::*;

fn build<A: SimApps>(
    apps: A,
    spec: &NodeSpec,
    now: u64,
    seal: &SealStore,
    restarted: bool,
) -> (Box<NodeT<A>>, Caps, Keypair, SoftPrekeys<Caps>, Drbg) {
    let alg = IdentityAlg::Ed25519;
    let tag = spec.tag;
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(vinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[tag ^ 0x5a; 32]);
    let mut cfg = EndpointConfig::new(u64::from(tag) * 0x9E37_79B9);
    cfg.conn.max_gso = 1;
    let ep_drbg = Drbg::new(&[tag ^ 0xa5; 32]);
    let mut ep: Box<NEpS<<A as SimApps>::Src>> = Box::new(Endpoint::new(
        now,
        prov,
        ep_drbg,
        identity,
        cfg,
        node_slots::<<A as SimApps>::Src>(),
    ));
    let mut env = Env {
        provider: &prov,
        now,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey_info = prekeys.acquire(&mut env).unwrap();
    ep.set_prekey(prekey_info.clone());
    ep.add_iface(spec.addr).unwrap();
    let mut relays: [Option<RelayCfg>; NRL] = [None; NRL];
    for (d, h) in relays.iter_mut().zip(spec.hubs.iter().filter(|h| h.id != kp.node_id())) {
        *d = Some(RelayCfg {
            id: h.id,
            udp: Some(h.udp),
            tcp: Some(h.tcp),
            ws: Some(h.ws),
        });
    }
    let cfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays,
            phone: false,
            restarted,
            start: now,
            v6: false,
            keep_learn: false,
        },
        is_hub: spec.is_hub,
        version: 1,
        alpn: HUB_ALPN,
        limits: spec.limits,
        map_keys: crate::id_key(0x5eed),
        wall_ms: (WALL_EPOCH + now) / 1_000_000,
        local: spec.addr,
        trace: spec.trace,
    };
    let drbg2 = Drbg::new(&[tag ^ 0x33; 32]);
    let kp2 = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let node = Node::with_apps(
        &cfg,
        *ep,
        prekey_info,
        prov,
        drbg2,
        Box::new(kp2),
        seal.clone(),
        u64::from(tag) << 32,
        apps,
    )
    .expect("the node starts");
    (Box::new(node), prov, kp, prekeys, drbg)
}

impl SimNode<NoApps> {
    pub fn new(spec: &NodeSpec) -> Self {
        Self::with_apps(spec, NoApps::default())
    }
}

impl<A: SimApps> SimNode<A> {
    pub fn with_apps(spec: &NodeSpec, apps: A) -> Self {
        let seal = SealStore {
            persist: spec.persist,
            ks: Rc::new(RefCell::new(SoftwareStore::new().unwrap())),
            blob: Rc::new(RefCell::new(Vec::new())),
        };
        Self::with_seal(apps, spec, seal, false)
    }

    pub(super) fn with_seal(apps: A, spec: &NodeSpec, seal: SealStore, restarted: bool) -> Self {
        let (node, prov, kp, prekeys, hdrbg) = build(apps.clone(), spec, spec.start, &seal, restarted);
        let me = kp.node_id();
        let hub = spec.is_hub.then(|| HubSide {
            relay: Box::new(HubRelay::new(RelayConfig::new(me, 0x5eed ^ u64::from(spec.tag)))),
            streams: HashMap::new(),
            by_node: HashMap::new(),
            stores: ResponderStores::default(),
            slots: Vec::new(),
            scid: 0,
        });
        let mut n = Self {
            incarnations: vec![node.membership().incarnation()],
            node,
            apps,
            spec: spec.clone(),
            me,
            prov,
            kp,
            prekeys,
            hdrbg,
            deny: false,
            bc_allow: true,
            seal,
            clock: Clock::default(),
            streams: [None; NRL],
            opening: [None; NRL],
            kinds: [Kind::Tcp; NRL],
            cws: [None, None, None, None],
            hub,
            out: Outbox::default(),
            events: VecDeque::new(),
            traces: Vec::new(),
            timeouts: 0,
            restored: DtnRestored::default(),
            now: spec.start,
            down: false,
            addr: spec.addr,
            carrier_hold: 0,
            held: Vec::new(),
        };
        n.node.set_local(&[spec.addr]);
        n
    }

    pub(super) fn wall_ms(&self, now: Time) -> u64 {
        u64::try_from((WALL_EPOCH.cast_signed() + self.clock.local(now)).max(0)).unwrap() / 1_000_000
    }

    pub(super) fn slot(&mut self, n: &NodeId) -> u16 {
        let hub = self.hub.as_mut().unwrap();
        let i = hub.slots.iter().position(|x| x == n).unwrap_or_else(|| {
            hub.slots.push(*n);
            hub.slots.len() - 1
        });
        u16::try_from(i).unwrap()
    }

    pub(super) fn member_addr(&self, node: &NodeId) -> Option<SocketAddr> {
        self.node.member_addr(node)
    }

    pub(super) fn member_at(&self, src: &SocketAddr) -> Option<NodeId> {
        self.node.member_at(src)
    }
}
