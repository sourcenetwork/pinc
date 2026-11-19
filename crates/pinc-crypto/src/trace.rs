//! Observation of the key derivations, for simulation builds.
//!
//! Invariants: a sink only observes (it receives borrowed inputs and the output, and cannot change either); the sink is
//! per thread, so concurrent simulations never see each other's derivations; with no sink installed a derivation
//! costs one thread-local read. The hook exists because the key schedule derives through [`crate::extract`] and
//! [`crate::expand`], not through the [`crate::Provider`], so a provider alone cannot see how a key came about.

use core::cell::Cell;

/// One call of [`crate::extract`] or [`crate::expand`], with its inputs and its output.
#[derive(Debug, Clone, Copy)]
pub enum Derivation<'a> {
    /// `out = extract(salt, ikm)`.
    Extract {
        /// The keying salt.
        salt: &'a [u8; 32],
        /// The input keying material.
        ikm: &'a [u8],
        /// The extracted key.
        out: &'a [u8; 32],
    },
    /// `out = expand(prk, label, ctx)`.
    Expand {
        /// The pseudo-random key.
        prk: &'a [u8; 32],
        /// The domain-separation label.
        label: &'a str,
        /// The derivation context.
        ctx: &'a [u8],
        /// The derived bytes.
        out: &'a [u8],
    },
}

/// Receives every derivation made on the thread it is installed on.
pub trait Sink {
    /// A derivation just completed.
    fn derived(&self, d: &Derivation<'_>);
}

thread_local! {
    static SINK: Cell<Option<&'static dyn Sink>> = const { Cell::new(None) };
}

/// Install (or with `None` remove) the sink of the current thread.
pub fn set_sink(sink: Option<&'static dyn Sink>) {
    SINK.with(|s| s.set(sink));
}

pub(crate) fn emit(d: &Derivation<'_>) {
    if let Some(sink) = SINK.with(Cell::get) {
        sink.derived(d);
    }
}
