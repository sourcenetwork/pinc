//! The intents the recorder tracks: what the application was asked to do, who must receive it, and when each
//! receiver got it.
//!
//! Invariant: an [`IntentRec`] is built once by [`IntentRec::new`] from the same arguments the reference recorder
//! takes, and `must_set`/`must`/`small` follow the reference rules exactly (a fetch or echo is "must" by its flag,
//! every other kind by a non-empty must set).

use std::collections::{BTreeMap, BTreeSet};

use crate::suite::world::model::IntentKind;

/// The reference name of an intent kind, as the trace hash writes it.
pub fn kind_name(kind: IntentKind) -> &'static str {
    match kind {
        IntentKind::Publish => "publish",
        IntentKind::Push => "push",
        IntentKind::Docsync => "docsync",
        IntentKind::Manage => "manage",
        IntentKind::Echo => "echo",
        IntentKind::Fetch => "fetch",
        IntentKind::Reconcile => "reconcile",
    }
}

/// Anything that names an intent kind: an [`IntentKind`] or its reference string.
pub trait AsIntentKind {
    /// The kind, or `None` for a string the reference does not know.
    fn into_intent_kind(self) -> Option<IntentKind>;
}

impl AsIntentKind for IntentKind {
    fn into_intent_kind(self) -> Option<IntentKind> {
        Some(self)
    }
}

impl AsIntentKind for &str {
    fn into_intent_kind(self) -> Option<IntentKind> {
        Some(match self {
            "publish" => IntentKind::Publish,
            "push" => IntentKind::Push,
            "docsync" => IntentKind::Docsync,
            "manage" => IntentKind::Manage,
            "echo" => IntentKind::Echo,
            "fetch" => IntentKind::Fetch,
            "reconcile" => IntentKind::Reconcile,
            _ => return None,
        })
    }
}

/// The `must` argument of an intent: a flag (every receiver, or the single flow) or an explicit receiver set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MustArg {
    /// A flag.
    Flag(bool),
    /// An explicit set of receivers.
    Set(Vec<usize>),
}

/// The optional fields the application stores on an intent (the reference's `meta` dictionary). Echo timelines live
/// in [`crate::suite::rec::Rec::echo`], not here.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct IntentMeta {
    /// The value id of the message or value the intent carries.
    pub vid: Option<u64>,
    /// The peer (docsync, manage, echo, reconcile).
    pub to: Option<usize>,
    /// A G-SURFACE probe echo.
    pub probe: bool,
    /// The providers of a fetch.
    pub providers: Vec<usize>,
    /// The requested byte ranges `(offset, length)` of a fetch; `None` means the whole value.
    pub ranges: Option<Vec<(u64, u64)>>,
    /// The requested bytes of a fetch; absent means the intent size.
    pub req_bytes: Option<u64>,
    /// The playback rate in bits per second of a stream fetch.
    pub stream_rate: Option<u64>,
    /// When the first byte at the first range's offset was verified.
    pub first_byte: Option<u64>,
    /// The stall fraction of a completed stream fetch.
    pub stall_frac: Option<f64>,
    /// `(time, contiguous bytes)` after every store write of the fetch.
    pub progress: Vec<(u64, u64)>,
    /// The collection of a reconcile.
    pub set_ref: Option<Vec<u8>>,
    /// Bytes both session ends had sent when a reconcile started.
    pub tx0: Option<u64>,
    /// The root of the fetched value.
    pub root: Option<Vec<u8>>,
}

/// One recorded intent.
#[derive(Clone, Debug)]
pub struct IntentRec {
    /// Intent id, from 1.
    pub iid: u32,
    /// What it asks.
    pub kind: IntentKind,
    /// The acting node.
    pub node: usize,
    /// When it was issued.
    pub t: u64,
    /// Absolute deadline, if it has one.
    pub deadline: Option<u64>,
    /// The nodes expected to receive.
    pub receivers: BTreeSet<usize>,
    /// Node to the time it received.
    pub delivered: BTreeMap<usize, u64>,
    /// Message or value size.
    pub size: u64,
    /// The receivers that must get it.
    pub must_set: BTreeSet<usize>,
    /// Whether the intent is a must intent (see the module invariant).
    pub must: bool,
    /// The application's optional fields.
    pub meta: IntentMeta,
    /// A small-message kind: publish, push, docsync, manage or reconcile.
    pub small: bool,
    /// The intent runs under bulk transfers (S11).
    pub under_bulk: bool,
}

impl IntentRec {
    /// Builds the record exactly as the reference `Intent.__init__` does.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        iid: u32,
        kind: IntentKind,
        node: usize,
        t: u64,
        deadline: Option<u64>,
        receivers: &[usize],
        size: u64,
        must: MustArg,
        meta: IntentMeta,
    ) -> Self {
        let receivers: BTreeSet<usize> = receivers.iter().copied().collect();
        let (must_set, flag) = match must {
            MustArg::Set(s) => {
                let set: BTreeSet<usize> = s.into_iter().collect();
                let nonempty = !set.is_empty();
                (set, nonempty)
            }
            MustArg::Flag(f) => (if f { receivers.clone() } else { BTreeSet::new() }, f),
        };
        let must = if matches!(kind, IntentKind::Echo | IntentKind::Fetch) {
            flag
        } else {
            !must_set.is_empty()
        };
        let small = matches!(
            kind,
            IntentKind::Publish | IntentKind::Push | IntentKind::Docsync | IntentKind::Manage | IntentKind::Reconcile
        );
        Self {
            iid,
            kind,
            node,
            t,
            deadline,
            receivers,
            delivered: BTreeMap::new(),
            size,
            must_set,
            must,
            meta,
            small,
            under_bulk: false,
        }
    }
}
