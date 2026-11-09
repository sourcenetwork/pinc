//! The smallest executor pieces the crate needs: a `block_on` for the blocking API and a spawner trait with a thread
//! implementation. They depend on nothing but `std`.
//!
//! The async API itself needs no executor: its futures wait on channels and wake through the waker they are polled
//! with, so any executor can drive them. A [`Spawn`] is only for background work the crate starts for you, such as the
//! task that serves a registered [`Protocol`](crate::Protocol).

use std::future::Future;
use std::pin::{Pin, pin};
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};
use std::thread::{self, Thread};

/// A boxed task: what a [`Spawn`] runs.
pub type Task = Pin<Box<dyn Future<Output = ()> + Send + 'static>>;

/// How the host runs background tasks: hand the task to your executor.
pub trait Spawn: Send + Sync + 'static {
    /// Run `task` to completion on the host's executor.
    fn spawn(&self, task: Task);
}

impl<F: Fn(Task) + Send + Sync + 'static> Spawn for F {
    fn spawn(&self, task: Task) {
        self(task);
    }
}

struct Unparker(Thread);

impl Wake for Unparker {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}

/// Run `f` to completion on the calling thread, parking it while the future waits.
///
/// ```
/// assert_eq!(vinc::block_on(async { 1 + 2 }), 3);
/// ```
pub fn block_on<F: Future>(f: F) -> F::Output {
    let mut f = pin!(f);
    let waker = Waker::from(Arc::new(Unparker(thread::current())));
    let mut cx = Context::from_waker(&waker);
    loop {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return v;
        }
        thread::park();
    }
}

/// A [`Spawn`] that runs each task on its own thread with [`block_on`]: what the blocking API uses.
///
/// vertexia: one thread per task; the number of tasks is bounded by the number of sessions, so a pooled executor
/// is only needed if a protocol spawns many tasks per session.
#[derive(Debug, Clone, Copy, Default)]
pub struct ThreadSpawner;

impl Spawn for ThreadSpawner {
    fn spawn(&self, task: Task) {
        let _ = thread::Builder::new()
            .name("vinc-task".into())
            .spawn(move || block_on(task));
    }
}
