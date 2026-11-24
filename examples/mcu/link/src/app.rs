//! The acceptor's side of the echo protocol: every byte read on a stream is written back on it.

use pinc_core::{Command, Event, SessionId, Value};
use pinc_transport::stream::StreamId;

use crate::Node;

/// Bytes moved from the read side to the write side at a time.
const STEP: usize = 1024;

/// The echo of one stream at a time.
pub struct Echo {
    buf: [u8; STEP],
    at: usize,
    len: usize,
    stream: Option<(SessionId, StreamId)>,
    ended: bool,
    /// Bytes written back since the node started.
    pub bytes: u64,
}

impl Echo {
    /// An idle echo.
    pub const fn new() -> Self {
        Self {
            buf: [0; STEP],
            at: 0,
            len: 0,
            stream: None,
            ended: false,
            bytes: 0,
        }
    }

    /// Act on an event of the node.
    pub fn on_event(&mut self, node: &mut Node<'_, '_, '_>, now: u64, ev: &Event) {
        match *ev {
            Event::StreamReadable { session, stream } => {
                if self.stream != Some((session, stream)) {
                    *self = Self {
                        stream: Some((session, stream)),
                        bytes: self.bytes,
                        ..Self::new()
                    };
                }
                self.run(node, now);
            }
            Event::StreamWritable { .. } => self.run(node, now),
            Event::Closed { session, .. } if self.stream.is_some_and(|(s, _)| s == session) => self.stream = None,
            _ => {}
        }
    }

    fn run(&mut self, node: &mut Node<'_, '_, '_>, now: u64) {
        let Some((session, stream)) = self.stream else { return };
        loop {
            if self.at == self.len {
                if self.ended {
                    let _ = node.command(now, Command::Finish { session, stream });
                    self.stream = None;
                    return;
                }
                let (n, ended) = node.read(now, session, stream, &mut self.buf);
                self.ended = ended;
                (self.at, self.len) = (0, n);
                if n == 0 && !ended {
                    return;
                }
                continue;
            }
            let Some(data) = self.buf.get(self.at..self.len) else {
                return;
            };
            match node.command(now, Command::Write { session, stream, data }) {
                Ok(Value::Written(w)) if w > 0 => {
                    self.at += w;
                    self.bytes += w as u64;
                }
                _ => return,
            }
        }
    }
}

impl Default for Echo {
    fn default() -> Self {
        Self::new()
    }
}
