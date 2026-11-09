//! The canonical text of a world, section by section, and its digests.
//!
//! The reference generator and this crate each write a world as compact JSON with sorted keys (floats in Python's
//! `repr`, bytes as lower-case hex, tuples and sets as arrays) and compare the `BLAKE2b`-128 digest of every
//! section; this is the proof that generation is bit-exact. Invariant: the text is a pure function of the world, and
//! a field the reference leaves out of a dictionary (an absent optional) is left out here too.

use std::fmt::Write;

use super::model::{
    AdvKind, ChangeKind, EnvArg, EnvKind, Intent, IntentKind, Must, NatSpec, NodeSpec, Param, Site, World,
};
use crate::reference::{Py, blake2b_128};

/// A JSON value with the reference's number formatting.
enum J {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(&'static str, J)>),
    Map(Vec<(String, J)>),
}

fn write_obj(out: &mut String, mut fields: Vec<(&str, &J)>) {
    fields.sort_by_key(|(k, _)| *k);
    out.push('{');
    for (i, (k, x)) in fields.into_iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "\"{k}\":");
        x.write(out);
    }
    out.push('}');
}

impl J {
    fn write(&self, out: &mut String) {
        match self {
            J::Null => out.push_str("null"),
            J::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            J::Int(i) => {
                let _ = write!(out, "{i}");
            }
            J::Float(f) => out.push_str(&Py::Float(*f).repr()),
            J::Str(s) => {
                out.push('"');
                out.push_str(s);
                out.push('"');
            }
            J::Arr(v) => {
                out.push('[');
                for (i, x) in v.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    x.write(out);
                }
                out.push(']');
            }
            J::Obj(v) => write_obj(out, v.iter().map(|(k, x)| (*k, x)).collect()),
            J::Map(v) => write_obj(out, v.iter().map(|(k, x)| (k.as_str(), x)).collect()),
        }
    }

    fn text(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }
}

fn int(x: impl Into<i128>) -> J {
    J::Int(x.into())
}

fn idx(x: usize) -> J {
    J::Int(x as i128)
}

fn s(x: &str) -> J {
    J::Str(x.to_string())
}

fn hex(b: &[u8]) -> String {
    b.iter().fold(String::with_capacity(b.len() * 2), |mut o, x| {
        let _ = write!(o, "{x:02x}");
        o
    })
}

fn list<T>(xs: &[T], f: impl Fn(&T) -> J) -> J {
    J::Arr(xs.iter().map(f).collect())
}

fn ids(xs: &[usize]) -> J {
    list(xs, |x| idx(*x))
}

fn opt<T>(x: Option<T>, f: impl Fn(T) -> J) -> J {
    x.map_or(J::Null, f)
}

/// A named section of the canonical text.
pub struct Section {
    /// The section name.
    pub name: &'static str,
    /// The number of top-level elements (the entries of a list or dictionary; 1 for a record).
    pub count: usize,
    /// The canonical text.
    pub text: String,
}

impl Section {
    /// The digest recorded in the vectors: `BLAKE2b`-128 of the text, as lower-case hex.
    pub fn digest(&self) -> String {
        hex(&blake2b_128(self.text.as_bytes()))
    }
}

fn param(p: &Param) -> J {
    match p {
        Param::Int(v) => int(*v),
        Param::Float(v) => J::Float(*v),
        Param::Bool(v) => J::Bool(*v),
        Param::Range { lo, hi, ints: true } => J::Arr(vec![int(*lo as i64), int(*hi as i64)]),
        Param::Range { lo, hi, .. } => J::Arr(vec![J::Float(*lo), J::Float(*hi)]),
        Param::Ints(v) => list(v, |x| int(*x)),
        Param::Strs(v) => list(v, |x| s(x)),
    }
}

fn nat(n: &NatSpec) -> J {
    let mut o = vec![
        ("nid", idx(n.nid)),
        ("ext_ip", int(n.ext_ip)),
        ("mapping", s(&n.mapping)),
        ("filtering", s(&n.filtering)),
        ("timeout_ns", int(n.timeout_ns)),
        ("no_punch", J::Bool(n.no_punch)),
    ];
    if let Some(t) = n.tcp_timeout_ns {
        o.push(("tcp_timeout_ns", int(t)));
    }
    J::Obj(o)
}

fn site(x: &Site) -> J {
    let mut o = vec![
        ("sid", idx(x.sid)),
        ("region", idx(x.region)),
        ("up_bps", int(x.up_bps)),
        ("down_bps", int(x.down_bps)),
        ("up_delay_ns", int(x.up_delay_ns)),
        ("down_delay_ns", int(x.down_delay_ns)),
        ("loss", J::Float(x.loss)),
        ("burst_ns", int(x.burst_ns)),
        ("queue_bytes", int(x.queue_bytes)),
        ("nats", list(&x.nats, nat)),
        ("v6_open", J::Bool(x.v6_open)),
        ("mtu", int(x.mtu)),
    ];
    if let Some(m) = &x.middlebox {
        let mut mb = vec![
            ("udp_block", J::Bool(m.udp_block)),
            ("tcp_ports", list(&m.tcp_ports, |p| int(*p))),
            ("tls_only", J::Bool(m.tls_only)),
            ("fw_reject", J::Bool(m.fw_reject)),
        ];
        if let Some(p) = m.portal_ns {
            mb.push(("portal_ns", int(p)));
        }
        o.push(("middlebox", J::Obj(mb)));
    }
    J::Obj(o)
}

fn node(x: &NodeSpec) -> J {
    let ifaces = list(&x.ifaces, |f| {
        let mut o = vec![
            ("name", s(&f.name)),
            ("kind", s(&f.kind)),
            (
                "addr",
                J::Arr(vec![s(&f.addr.kind), int(f.addr.host), int(f.addr.port)]),
            ),
            ("mtu", int(f.mtu)),
        ];
        if f.public {
            o.push(("public", J::Bool(true)));
        }
        if f.v6 {
            o.push(("v6", J::Bool(true)));
        }
        J::Obj(o)
    });
    let mut o = vec![
        ("device", s(&x.device)),
        ("site", idx(x.site)),
        ("kind", s(&x.kind)),
        ("region", idx(x.region)),
        ("ifaces", ifaces),
        ("topics", list(&x.topics, |t| J::Str(hex(t)))),
    ];
    if !x.sites.is_empty() {
        o.push(("sites", ids(&x.sites)));
    }
    if let Some(c) = &x.clock {
        let mut ck = vec![("offset_ns", int(c.offset_ns)), ("drift_ppm", int(c.drift_ppm))];
        if !c.jumps.is_empty() {
            ck.push(("jumps", list(&c.jumps, |(a, b)| J::Arr(vec![int(*a), int(*b)]))));
        }
        o.push(("clock", J::Obj(ck)));
    }
    if let Some(f) = x.cpu_factor {
        o.push(("cpu_factor", int(f)));
    }
    J::Obj(o)
}

/// The reference name of an environment action kind.
pub fn env_name(k: EnvKind) -> &'static str {
    match k {
        EnvKind::Crash => "crash",
        EnvKind::Handover => "handover",
        EnvKind::Leave => "leave",
        EnvKind::Outage => "outage",
        EnvKind::Rebind => "rebind",
        EnvKind::Restart => "restart",
        EnvKind::Revoke => "revoke",
        EnvKind::Start => "start",
        EnvKind::Suspend => "suspend",
        EnvKind::Upgrade => "upgrade",
    }
}

fn change_name(k: ChangeKind) -> &'static str {
    match k {
        ChangeKind::Join => "join",
        ChangeKind::Crash => "crash",
        ChangeKind::Leave => "leave",
        ChangeKind::Stack => "stack",
        ChangeKind::Revoke => "revoke",
        ChangeKind::Addr => "addr",
    }
}

fn intent_name(k: IntentKind) -> &'static str {
    match k {
        IntentKind::Publish => "publish",
        IntentKind::Push => "push",
        IntentKind::Docsync => "docsync",
        IntentKind::Manage => "manage",
        IntentKind::Echo => "echo",
        IntentKind::Fetch => "fetch",
        IntentKind::Reconcile => "reconcile",
    }
}

fn adv_name(k: AdvKind) -> &'static str {
    match k {
        AdvKind::Amplify => "amplify",
        AdvKind::Eclipse => "eclipse",
        AdvKind::Garbage => "garbage",
    }
}

fn env_arg(a: EnvArg) -> J {
    match a {
        EnvArg::None => J::Null,
        EnvArg::Flag(b) => J::Bool(b),
        EnvArg::Num(n) => int(n),
        EnvArg::SiteGap(s, g) => J::Arr(vec![idx(s), int(g)]),
    }
}

fn intent(d: &Intent) -> J {
    let mut o = vec![
        ("t", int(d.t)),
        ("node", idx(d.node)),
        ("kind", s(intent_name(d.kind))),
        ("deadline_ns", int(d.deadline_ns)),
        (
            "must",
            match &d.must {
                Must::Flag(b) => J::Bool(*b),
                Must::Set(v) => ids(v),
            },
        ),
    ];
    if let Some(x) = d.to {
        o.push(("to", idx(x)));
    }
    if let Some(x) = &d.topic {
        o.push(("topic", J::Str(hex(x))));
    }
    if let Some(x) = d.size {
        o.push(("size", int(x)));
    }
    if let Some(x) = d.req {
        o.push(("req", int(x)));
    }
    if let Some(x) = d.resp {
        o.push(("resp", int(x)));
    }
    if let Some(x) = &d.value {
        o.push(("value", s(x)));
    }
    if d.kind == IntentKind::Fetch {
        o.push(("providers", ids(&d.providers)));
    }
    if d.kind == IntentKind::Publish {
        o.push(("receivers", ids(&d.receivers)));
    }
    if !d.ranges.is_empty() {
        o.push(("ranges", list(&d.ranges, |(a, b)| J::Arr(vec![int(*a), int(*b)]))));
    }
    if let Some(x) = d.stream_rate {
        o.push(("stream_rate", int(x)));
    }
    if d.probe {
        o.push(("probe", J::Bool(true)));
    }
    if d.under_bulk {
        o.push(("under_bulk", J::Bool(true)));
    }
    if let Some(x) = &d.set_ref {
        o.push(("set_ref", J::Str(hex(x))));
    }
    J::Obj(o)
}

fn sec(name: &'static str, count: usize, j: &J) -> Section {
    Section {
        name,
        count,
        text: j.text(),
    }
}

/// The sections of a world's canonical text, in a fixed order: `meta`, `params`, `sites`, `nodes`, `env`, `intents`,
/// `changes`, `values`, `denied`, `partitions`, `adversary`, `sets`.
pub fn sections(w: &World) -> Vec<Section> {
    let meta = J::Obj(vec![
        ("id", s(&w.id)),
        ("seed", int(w.seed)),
        ("region_delay_ns", list(&w.region_delay_ns, |r| list(r, |x| int(*x)))),
        ("bootstrap", ids(&w.bootstrap)),
        ("duration_ns", int(w.duration_ns)),
        ("idle_window", J::Arr(vec![int(w.idle_window.0), int(w.idle_window.1)])),
        ("connect_deadline_ns", int(w.connect_deadline_ns)),
        ("acp_latency_ns", int(w.acp_latency_ns)),
        ("acp_validity_ns", int(w.acp_validity_ns)),
        ("revocation_bound_cap_ns", int(w.revocation_bound_cap_ns)),
        ("awareness_bound_cap_ns", int(w.awareness_bound_cap_ns)),
        ("false_suspicion_cap", J::Float(w.false_suspicion_cap)),
        ("score_c3", J::Bool(w.score_c3)),
        ("clouds", ids(&w.clouds)),
        ("homes", ids(&w.homes)),
        ("mobiles", ids(&w.mobiles)),
        ("hostile", ids(&w.hostile)),
        ("browsers", ids(&w.browsers)),
        ("liars", ids(&w.liars)),
        ("soak", J::Bool(w.soak)),
        ("eclipse_victim", opt(w.eclipse_victim, idx)),
        (
            "compromise_node",
            opt(w.compromise_node, |(t, x)| J::Arr(vec![int(t), idx(x)])),
        ),
        (
            "load_used",
            J::Arr(
                w.load_used
                    .iter()
                    .map(|(i, (a, b))| J::Arr(vec![idx(*i), J::Arr(vec![J::Float(*a), J::Float(*b)])]))
                    .collect(),
            ),
        ),
    ]);
    let params = J::Map(w.params.iter().map(|(k, v)| (k.clone(), param(v))).collect());
    let env = list(&w.env, |e| {
        J::Arr(vec![int(e.t), s(env_name(e.kind)), idx(e.node), env_arg(e.arg)])
    });
    let changes = list(&w.changes, |c| {
        J::Arr(vec![int(c.t), s(change_name(c.kind)), idx(c.node), opt(c.version, int)])
    });
    let values = J::Obj(vec![
        (
            "values",
            J::Map(w.values.iter().map(|(k, v)| (k.clone(), int(*v))).collect()),
        ),
        (
            "provides",
            J::Arr(
                w.provides
                    .iter()
                    .map(|(n, names)| J::Arr(vec![idx(*n), list(names, |x| s(x))]))
                    .collect(),
            ),
        ),
    ]);
    let denied = J::Obj(vec![
        ("denied", ids(&w.denied)),
        ("revoked", list(&w.revoked, |(i, t)| J::Arr(vec![idx(*i), int(*t)]))),
    ]);
    let partitions = list(&w.partitions, |c| {
        J::Arr(vec![
            int(c.from),
            int(c.to),
            ids(&c.x),
            ids(&c.y),
            s(if c.both { "both" } else { "oneway" }),
        ])
    });
    let adversary = J::Obj(vec![
        (
            "adversary",
            opt(w.adversary.as_ref(), |a| {
                J::Obj(vec![
                    ("victims", ids(&a.victims)),
                    ("replay", J::Float(a.replay)),
                    ("modify", J::Float(a.modify)),
                ])
            }),
        ),
        (
            "env",
            list(&w.adversary_env, |(t, k, n)| {
                J::Arr(vec![int(*t), s(adv_name(*k)), idx(*n)])
            }),
        ),
        (
            "compromise",
            list(&w.compromise, |(t, n)| J::Arr(vec![int(*t), idx(*n)])),
        ),
    ]);
    let sets = J::Arr(
        w.sets
            .iter()
            .map(|((n, r), items)| {
                let flat: Vec<u8> = items.iter().flatten().copied().collect();
                let profile = w.set_profiles.get(&(*n, r.clone())).map_or("", String::as_str);
                J::Arr(vec![
                    idx(*n),
                    J::Str(hex(r)),
                    s(profile),
                    idx(items.len()),
                    J::Str(hex(&blake2b_128(&flat))),
                ])
            })
            .collect(),
    );
    vec![
        sec("meta", 1, &meta),
        sec("params", w.params.len(), &params),
        sec("sites", w.sites.len(), &list(&w.sites, site)),
        sec("nodes", w.nodes.len(), &list(&w.nodes, node)),
        sec("env", w.env.len(), &env),
        sec("intents", w.intents.len(), &list(&w.intents, intent)),
        sec("changes", w.changes.len(), &changes),
        sec("values", w.values.len(), &values),
        sec("denied", w.denied.len() + w.revoked.len(), &denied),
        sec("partitions", w.partitions.len(), &partitions),
        sec("adversary", w.adversary_env.len(), &adversary),
        sec("sets", w.sets.len(), &sets),
    ]
}
