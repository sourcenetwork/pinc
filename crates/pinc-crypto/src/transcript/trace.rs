//! Test-only record of what transcripts absorb.
//!
//! Invariant: nothing is recorded until [`arm`] is called on the thread; then every [`super::Transcript::snapshot`]
//! on that thread appends one [`Record`]: the transcript's label and the tag and length of each field absorbed so
//! far, in absorption order. A thread that never arms allocates nothing and touches one flag.

use std::cell::{Cell, RefCell};
use std::thread_local;
use std::vec::Vec;

/// The tags and lengths absorbed by one transcript so far, with its label.
#[derive(Clone, Debug)]
pub(super) struct Seen {
    label: &'static str,
    fields: Vec<(&'static str, usize)>,
}

/// One snapshot of a transcript: its label and the `(tag, length)` of every field absorbed, in order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Record {
    /// The domain label the transcript was created with (empty for [`super::Transcript::new`]).
    pub label: &'static str,
    /// The tag and the byte length of each absorbed field, in order.
    pub fields: Vec<(&'static str, usize)>,
}

thread_local! {
    static ARMED: Cell<bool> = const { Cell::new(false) };
    static LOG: RefCell<Vec<Record>> = const { RefCell::new(Vec::new()) };
}

fn armed() -> bool {
    ARMED.with(Cell::get)
}

impl Seen {
    pub(super) const fn new(label: &'static str) -> Self {
        Self {
            label,
            fields: Vec::new(),
        }
    }

    pub(super) fn push(&mut self, tag: &'static str, len: usize) {
        if armed() {
            self.fields.push((tag, len));
        }
    }

    pub(super) fn publish(&self) {
        if armed() {
            LOG.with_borrow_mut(|log| {
                log.push(Record {
                    label: self.label,
                    fields: self.fields.clone(),
                });
            });
        }
    }
}

/// Start recording on this thread.
pub fn arm() {
    ARMED.with(|a| a.set(true));
}

/// Stop recording on this thread and return the snapshots recorded since [`arm`], in order.
pub fn take() -> Vec<Record> {
    ARMED.with(|a| a.set(false));
    LOG.with_borrow_mut(core::mem::take)
}
