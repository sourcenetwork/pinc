//! The PINC endpoint a small device holds, and what its host does for it.
//!
//! This is the host program of the microcontroller run: the SANS-IO `pinc-core` endpoint with tables sized for one
//! session, its memory lent from statics (no heap anywhere), the host duties (software keys, the access answer) and a
//! framing that carries datagrams over a serial line. The board's firmware and the laptop's peer both build on it, so
//! the two ends of the line run the same code with the same table sizes.
//!
//! The crate is `no_std`, never allocates and never uses `unsafe`.
#![no_std]
#![forbid(unsafe_code)]

pub mod app;
pub mod frame;

use core::mem::MaybeUninit;
use core::net::{Ipv4Addr, SocketAddr, SocketAddrV4};

use ed25519_dalek::{Signer as _, SigningKey};
use pinc_core::{Answer, Command, CommandError, Endpoint, EndpointConfig, Event, Query, SessionId, Slot, Value};
use pinc_crypto::{Drbg, IdentityAlg, NodeId, Software};
use pinc_security::{Env, KeyHandle, KeyRequest, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::{BufferPool, RawChunk};
use pinc_transport::stream::{self, NoSource, RecvStatus, StreamId, Streams};

/// Stream slots of the session.
pub const N: usize = 4;
/// Chunk-ring entries per stream half.
pub const C: usize = 9;
/// Packets tracked in flight.
pub const F: usize = 32;
/// Paths of the session.
pub const NP: usize = 2;
/// Sessions in the table. The memory below is that of one session.
pub const K: usize = 1;
/// Entries of the connection id table and of the table of address pairs.
pub const D: usize = 16;
/// Prekeys in the responder's store.
pub const PK: usize = 2;
/// Tickets in the responder's store.
pub const TK: usize = 4;
/// Tickets this node holds as a client.
pub const CT: usize = 2;
/// Pool chunks (16 KiB each) of the session.
pub const CHUNKS: usize = 3;

/// The largest datagram either end sends on the line.
pub const MTU: u16 = 1200;

/// The protocol the two ends speak: the dialer writes on a stream and the acceptor writes the same bytes back.
pub const ALPN: &[u8] = b"pinc/mcu-echo";

/// The first byte of every frame on the line says what the rest is.
pub mod kind {
    /// A PINC datagram.
    pub const DATAGRAM: u8 = 0;
    /// A line of text from the board: what it measured, as `name key=value ...`.
    pub const REPORT: u8 = 1;
    /// A request to the board: one command byte and its operands.
    pub const CONTROL: u8 = 2;
}

/// The board's clocks, which its boot stage sets and its image counts on.
///
/// Without the `fast-clock` feature the chip is left as it leaves reset: the internal oscillator (HSI) at 64 MHz
/// drives everything. With it the boot stage starts the first PLL from that oscillator (64 MHz / 16 x 160 / 2) and
/// the core runs at 320 MHz, with the buses at half and the peripherals at a quarter of that. The supply and the
/// voltage scale are not touched, so the clock stays inside what the chip allows at the scale it resets to.
pub mod clock {
    /// The core's clock.
    pub const CORE_HZ: u32 = if cfg!(feature = "fast-clock") {
        320_000_000
    } else {
        64_000_000
    };
    /// The clock of the buses, which is the flash interface's.
    pub const BUS_HZ: u32 = if cfg!(feature = "fast-clock") {
        CORE_HZ / 2
    } else {
        CORE_HZ
    };
    /// The clock of the peripherals, which is the serial port's.
    pub const PERIPHERAL_HZ: u32 = if cfg!(feature = "fast-clock") {
        CORE_HZ / 4
    } else {
        CORE_HZ
    };
    /// The serial line's speed.
    pub const BAUD: u32 = 1_000_000;
}

/// What the laptop asks of the board's boot stage, in [`kind::CONTROL`] frames: one operation byte, then its operands
/// (addresses and lengths are offsets into the flash, 32 bits, least significant byte first). The boot stage answers
/// each with the same operation byte and a status byte (zero for done), or for [`load::CHECK`] the four bytes of the
/// checksum.
pub mod load {
    /// Stay in the loader instead of starting the image.
    pub const ENTER: u8 = b'L';
    /// Erase the 4 KiB sector that holds the address.
    pub const ERASE: u8 = b'E';
    /// Program the bytes that follow the address.
    pub const WRITE: u8 = b'W';
    /// The CRC-32 of the bytes at the address, for the length that follows it.
    pub const CHECK: u8 = b'C';
    /// Start the image.
    pub const GO: u8 = b'G';
    /// The most bytes one [`WRITE`] carries.
    pub const STEP: usize = 1024;
    /// The longest request: the kind, the operation, an address and a step of bytes.
    pub const BODY: usize = 6 + STEP;
}

/// The address the board's end of the line goes by.
pub const BOARD_ADDR: SocketAddr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 2), 4433));
/// The address the laptop's end of the line goes by.
pub const PEER_ADDR: SocketAddr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 1), 4433));

/// The endpoint of a small device.
pub type Ep<'s, 'a> = Endpoint<'s, 'a, Software, NoSource, N, C, F, NP, K, D, PK, TK, CT>;
/// One slot of its session table.
pub type EpSlot<'a> = Slot<'a, Software, NoSource, N, C, F, NP>;
/// The stream table of one session.
pub type EpStreams = Streams<NoSource, N, C>;
/// The session table, before the endpoint is built.
pub type SlotTable<'a> = MaybeUninit<[EpSlot<'a>; K]>;
/// Where the endpoint is built.
pub type EpPlace<'s, 'a> = MaybeUninit<Ep<'s, 'a>>;

/// The memory of the one session: the pool's chunks, the stream table and the loss average. A host keeps it in a
/// static (it is all zeroes or unwritten until [`Node::new`] runs, so it costs no image bytes).
pub struct Memory {
    slab: [RawChunk; CHUNKS],
    streams: MaybeUninit<EpStreams>,
    loss: MaybeUninit<LossEstimate>,
}

impl Memory {
    /// Unwritten memory.
    #[allow(
        clippy::large_stack_arrays,
        reason = "a constant for a static; the host never builds it on its stack"
    )]
    pub const fn new() -> Self {
        Self {
            slab: [[0; core::mem::size_of::<RawChunk>()]; CHUNKS],
            streams: MaybeUninit::uninit(),
            loss: MaybeUninit::uninit(),
        }
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

/// Events a command produced that the host has not read yet.
const PENDING: usize = 16;

/// An endpoint with its keys and the duties a host performs for it.
pub struct Node<'n, 's, 'a> {
    /// The endpoint: the host feeds it datagrams and timeouts and sends what it writes.
    pub ep: &'n mut Ep<'s, 'a>,
    drbg: Drbg,
    /// The Ed25519 identity key. The library's own `Keypair` holds room for an ML-DSA key whatever the algorithm
    /// (64 KiB), so a device that signs with Ed25519 keeps the key itself.
    signing: SigningKey,
    prekeys: SoftPrekeys<Software>,
    pending: [Option<Event>; PENDING],
    head: usize,
    len: usize,
}

/// Why a node could not be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildError {
    /// The identity could not be made from the seed.
    Identity,
    /// The prekey could not be made.
    Prekey,
    /// The endpoint took neither the protocol nor the local address.
    Register,
}

/// One 32-byte secret out of `seed`, separated by `tag`.
fn derive(seed: &[u8; 32], tag: u8) -> [u8; 32] {
    let mut out = *seed;
    for (i, b) in out.iter_mut().enumerate() {
        #[allow(clippy::cast_possible_truncation, reason = "i is below 32")]
        let i = i as u8;
        *b ^= tag.wrapping_mul(31).wrapping_add(i.wrapping_mul(tag));
    }
    out
}

/// The node id of the node [`Node::new`] builds from `seed`.
///
/// # Errors
/// When the seed makes no identity.
pub fn node_id(seed: &[u8; 32]) -> Result<NodeId, BuildError> {
    Ok(identity(&SigningKey::from_bytes(seed))?.node_id())
}

/// The handle the identity key answers to.
const IDENTITY: KeyHandle = KeyHandle(1);

fn identity(signing: &SigningKey) -> Result<LocalIdentity, BuildError> {
    LocalIdentity::new(IdentityAlg::Ed25519, signing.verifying_key().as_bytes(), IDENTITY)
        .map_err(|_| BuildError::Identity)
}

/// Write the session table into the place the host lent. The slot is built by value and moved there, so this frame
/// holds one slot (67 KiB on a 32-bit target); it is a function of its own so that nothing else is on the stack then.
#[inline(never)]
#[allow(clippy::large_stack_arrays, reason = "see above")]
fn lend<'s, 'a>(memory: &'a mut Memory, slots: &'s mut SlotTable<'a>) -> &'s mut [EpSlot<'a>; K] {
    let Memory { slab, streams, loss } = memory;
    let pool = BufferPool::from_slab(slab);
    let streams = streams.write(Streams::new(&stream::Config::new(false), &pool));
    let loss: &LossEstimate = loss.write(LossEstimate::new());
    slots.write([Slot::new(Resources {
        pool,
        streams: streams.into(),
        loss: loss.into(),
        tables: Tables::new(),
    })])
}

/// Write the endpoint into the place the host lent; as [`lend`], a frame of its own for the one value it moves.
#[inline(never)]
#[allow(
    clippy::large_types_passed_by_value,
    reason = "the endpoint takes the identity by value"
)]
fn place<'n, 's, 'a>(
    now: u64,
    seed: &[u8; 32],
    identity: LocalIdentity,
    slots: &'s mut [EpSlot<'a>; K],
    ep: &'n mut EpPlace<'s, 'a>,
) -> &'n mut Ep<'s, 'a> {
    let mut cfg = EndpointConfig::new(u64::from_le_bytes([
        seed[0], seed[1], seed[2], seed[3], seed[4], seed[5], seed[6], seed[7],
    ]));
    cfg.conn.interface_mtu = MTU;
    cfg.conn.max_gso = 1;
    ep.write(Endpoint::new(
        now,
        Software,
        Drbg::new(&derive(seed, 1)),
        identity,
        cfg,
        slots,
    ))
}

impl<'n, 's, 'a> Node<'n, 's, 'a> {
    /// A node at time `now` (nanoseconds on the host's clock) that answers on `local`, with every secret drawn from
    /// `seed`: the host takes the seed from its random generator. The session's memory, the session table and the
    /// endpoint are written into the three places the host lends, which a device keeps in statics: the node itself
    /// is a few kilobytes of keys.
    ///
    /// # Errors
    /// When a key cannot be made or the endpoint refuses the protocol or the address.
    // Out of line: the key generation's working space must not become part of the caller's frame, which a host's
    // main loop keeps for good.
    #[inline(never)]
    pub fn new(
        now: u64,
        seed: &[u8; 32],
        local: SocketAddr,
        memory: &'a mut Memory,
        slots: &'s mut SlotTable<'a>,
        ep: &'n mut EpPlace<'s, 'a>,
    ) -> Result<Self, BuildError> {
        let signing = SigningKey::from_bytes(seed);
        let identity = identity(&signing)?;
        let ep = place(now, seed, identity, lend(memory, slots), ep);

        let mut drbg = Drbg::new(&derive(seed, 2));
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).map_err(|_| BuildError::Prekey)?;
        ep.set_prekey(prekeys.acquire(&mut env).map_err(|_| BuildError::Prekey)?);
        if !ep.register_alpn(ALPN) || ep.add_iface(local).is_none() {
            return Err(BuildError::Register);
        }
        Ok(Self {
            ep,
            drbg,
            signing,
            prekeys,
            pending: [None; PENDING],
            head: 0,
            len: 0,
        })
    }

    /// The node's id: what a peer dials.
    pub fn id(&self) -> NodeId {
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: self.signing.verifying_key().to_bytes(),
        }
    }

    fn hold(&mut self, ev: Event) {
        if self.len < PENDING {
            self.pending[(self.head + self.len) % PENDING] = Some(ev);
            self.len += 1;
        }
    }

    /// Give the endpoint a command; the events it produced at once are read with [`Node::next_event`].
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn command(&mut self, now: u64, cmd: Command<'_, NoSource>) -> Result<Value, CommandError> {
        let reply = self.ep.command(now, cmd)?;
        for ev in reply.events.iter() {
            self.hold(*ev);
        }
        Ok(reply.value)
    }

    /// The next event for the application. Key requests are answered with the software keys and access checks are
    /// allowed here, as the host's duties; neither is returned.
    pub fn next_event(&mut self, now: u64) -> Option<Event> {
        loop {
            let ev = if self.len > 0 {
                let ev = self.pending[self.head].take();
                self.head = (self.head + 1) % PENDING;
                self.len -= 1;
                ev?
            } else {
                self.ep.poll_event()?
            };
            match ev {
                Event::KeyRequest { session } => self.answer_keys(now, session),
                Event::AcpCheck { check, .. } => {
                    let _ = self.command(now, Command::AcpAnswer { check, allow: true });
                }
                ev => return Some(ev),
            }
        }
    }

    fn answer_keys(&mut self, now: u64, session: SessionId) {
        let soft = SoftKeys {
            signer: None,
            prekeys: Some(&self.prekeys),
        };
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        let mut none = [0u8; pinc_crypto::identity::MAX_SIGNATURE_LEN];
        let sig;
        let response = match self.ep.query(Query::KeyRequest(session)) {
            Answer::KeyRequest(KeyRequest::Sign {
                key: IDENTITY,
                alg: IdentityAlg::Ed25519,
                message,
            }) => {
                sig = self.signing.sign(message).to_bytes();
                KeyResponse::Signature(&sig)
            }
            Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut none) {
                KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                KeyResponse::Signature(_) | KeyResponse::Failed => KeyResponse::Failed,
            },
            _ => return,
        };
        if let Ok(reply) = self.ep.command(now, Command::KeyResponse { session, response }) {
            for ev in reply.events.iter() {
                self.hold(*ev);
            }
        }
    }

    /// Move readable bytes of a stream into `buf` and release them. Returns how many, and whether the stream has
    /// ended with nothing left to read.
    pub fn read(&mut self, now: u64, session: SessionId, stream: StreamId, buf: &mut [u8]) -> (usize, bool) {
        let n = match self.ep.query(Query::Read { session, stream }) {
            Answer::Chunk(chunk) => {
                let n = chunk.len().min(buf.len());
                if let (Some(dst), Some(src)) = (buf.get_mut(..n), chunk.get(..n)) {
                    dst.copy_from_slice(src);
                }
                n
            }
            _ => 0,
        };
        let done = matches!(
            self.command(now, Command::Consume { session, stream, n }),
            Ok(Value::Recv(RecvStatus::Finished))
        );
        (n, done)
    }
}
