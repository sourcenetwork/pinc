//! What an endpoint that owns its table makes each slot's memory from, the first time the slot is taken.
//!
//! Invariants: a slot's pool holds no memory of its own; its chunks come from the endpoint's chunk store, made once
//! with the endpoint, so no chunk is allocated, freed or mapped after the endpoint is built.

use pinc_transport::conn::Resources;
use pinc_transport::stream::{self, StreamSource};

/// What an endpoint that owns its table makes a slot's memory from, the first time the slot is taken.
pub(crate) struct Fresh {
    pool_chunks: usize,
    loss: alloc::rc::Rc<pinc_transport::recovery::LossEstimate>,
    pub(crate) machines: pinc_transport::conn::Machines,
    /// The pool a new stream table is made against; taking the slot ties the table to the slot's own.
    probe: pinc_transport::stream::pool::BufferPool<'static>,
}

impl Fresh {
    pub(crate) fn new(pool_chunks: usize) -> Self {
        Self {
            pool_chunks,
            loss: alloc::rc::Rc::new(pinc_transport::recovery::LossEstimate::new()),
            machines: pinc_transport::conn::Machines::new(),
            probe: pinc_transport::stream::pool::BufferPool::new_boxed(1),
        }
    }

    /// The memory of slot `slot`: its buffer pool over the endpoint's store, its stream table and its tables, none of
    /// which holds more than the slot's sessions come to use.
    pub(crate) fn memory<'m, S: StreamSource, const N: usize, const C: usize, const F: usize>(
        &mut self,
        slot: usize,
    ) -> Resources<'m, S, N, C, F> {
        use pinc_transport::conn::{Held, Shared, Tables};
        use pinc_transport::stream::Streams;
        use pinc_transport::stream::pool::BufferPool;

        Resources {
            pool: BufferPool::over_store(slot, self.pool_chunks),
            streams: Held::Owned(alloc::boxed::Box::new(Streams::new(
                &stream::Config::new(false),
                &self.probe,
            ))),
            loss: Shared::Counted(alloc::rc::Rc::clone(&self.loss)),
            tables: Tables::sharing(&self.machines),
        }
    }
}
