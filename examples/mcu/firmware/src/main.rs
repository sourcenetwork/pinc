//! The PINC endpoint on a NUCLEO-H7S3L8: it accepts a session over the board's serial line and writes back what it
//! reads on a stream, or dials the laptop when asked and times round trips itself, and reports what each cost.
//!
//! Frames on the line are byte-stuffed and start with a kind byte (`pinc_mcu_link::kind`): datagrams both ways, from
//! the board lines of text with its measurements, and from the laptop requests (`I`: say what you are; `D` and a node
//! id: dial that node). The time of every call into the endpoint is taken with the core's cycle counter, so the cost
//! of a handshake is known apart from the time its bytes spend on the line.
#![no_std]
#![no_main]

mod board;
mod crypto;

use core::fmt::Write as _;
use core::mem::MaybeUninit;
use core::sync::atomic::Ordering;

use cortex_m_rt::entry;
use pinc_core::{Command, Event, Role, SessionId, Value};
use pinc_mcu_link::app::Echo;
use pinc_mcu_link::frame::{Deframer, encode, encoded_max};
use pinc_mcu_link::{ALPN, BOARD_ADDR, MTU, Memory, PEER_ADDR, kind};

/// The primitives the endpoint runs on: the chip's units where it has them, or the library's software alone.
#[cfg(feature = "chip-crypto")]
type Primitives = crypto::Chip;
#[cfg(not(feature = "chip-crypto"))]
type Primitives = pinc_crypto::Software;

type Ep<'s, 'a> = pinc_mcu_link::Ep<'s, 'a, Primitives>;
type EpSlot<'a> = pinc_mcu_link::EpSlot<'a, Primitives>;
type EpPlace<'s, 'a> = pinc_mcu_link::EpPlace<'s, 'a, Primitives>;
type SlotTable<'a> = pinc_mcu_link::SlotTable<'a, Primitives>;
type Node<'n, 's, 'a> = pinc_mcu_link::Node<'n, 's, 'a, Primitives>;

/// The longest frame body: a kind byte and a datagram.
const BODY: usize = 1 + MTU as usize;
/// Round trips the board times when it dials.
const TRIPS: usize = 200;
/// The bytes of one round trip.
const PING: [u8; 32] = [0x5A; 32];

/// A line of text for the laptop.
struct Line {
    buf: [u8; 240],
    len: usize,
}

impl Line {
    fn new() -> Self {
        let mut buf = [0; 240];
        buf[0] = kind::REPORT;
        Self { buf, len: 1 }
    }

    fn send(&self) {
        let mut enc = [0u8; encoded_max(240)];
        if let Some(n) = encode(&self.buf[..self.len], &mut enc) {
            board::write(&enc[..n]);
        }
    }
}

impl core::fmt::Write for Line {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let room = self.buf.len() - self.len;
        let n = s.len().min(room);
        self.buf[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}

/// Send one line of text.
macro_rules! report {
    ($($arg:tt)*) => {{
        let mut line = Line::new();
        let _ = write!(line, $($arg)*);
        line.send();
    }};
}

/// The time spent in one kind of call into the endpoint.
#[derive(Clone, Copy, Default)]
struct Cost {
    calls: u32,
    total: u64,
    longest: u64,
}

impl Cost {
    fn add(&mut self, ns: u64) {
        self.calls += 1;
        self.total += ns;
        self.longest = self.longest.max(ns);
    }
}

/// The time spent in the endpoint, by what the host asked of it.
#[derive(Clone, Copy, Default)]
struct Costs {
    /// Datagrams handed in.
    rx: Cost,
    /// Events read and commands given; the key operations (the signature, the decapsulation) are answered in here.
    events: Cost,
    /// Datagrams written.
    tx: Cost,
    /// Timers served.
    timer: Cost,
}

impl Costs {
    fn total(&self) -> u64 {
        self.rx.total + self.events.total + self.tx.total + self.timer.total
    }

    fn report(&self, what: &str, wall: u64) {
        report!(
            "{what} wall_us={} cpu_us={} rx={}/{}us/max{}us events={}/{}us/max{}us tx={}/{}us/max{}us timer={}/{}us/max{}us",
            wall / 1000,
            self.total() / 1000,
            self.rx.calls,
            self.rx.total / 1000,
            self.rx.longest / 1000,
            self.events.calls,
            self.events.total / 1000,
            self.events.longest / 1000,
            self.tx.calls,
            self.tx.total / 1000,
            self.tx.longest / 1000,
            self.timer.calls,
            self.timer.total / 1000,
            self.timer.longest / 1000,
        );
    }
}

/// Run one call into the endpoint and add its time to `cost`. Out of line, so that the call's frame is not part of
/// `main`'s, which is on the stack for good: built for size, the compiler otherwise folds 100 KiB of them into it.
#[inline(never)]
fn timed<R>(cost: &mut Cost, f: impl FnOnce() -> R) -> R {
    let t = board::now();
    let r = f();
    cost.add(board::now() - t);
    r
}

/// A session the board dialed: it times round trips of [`PING`] on one stream, then closes.
struct Dial {
    session: SessionId,
    stream: Option<u64>,
    /// When the bytes of the round trip under way were written.
    sent: u64,
    /// How many of them came back.
    back: usize,
    /// The round trips so far, in microseconds.
    trips: [u32; TRIPS],
    done: usize,
}

impl Dial {
    /// Open the stream once the session lets it, and write the first bytes.
    fn open(&mut self, node: &mut Node, now: u64) {
        if self.stream.is_none()
            && let Ok(Value::Stream(stream)) = node.command(
                now,
                Command::OpenStream {
                    session: self.session,
                    bidi: true,
                },
            )
        {
            self.stream = Some(stream);
            self.ping(node, now);
        }
    }

    fn ping(&mut self, node: &mut Node, now: u64) {
        let Some(stream) = self.stream else { return };
        let _ = node.command(
            now,
            Command::Write {
                session: self.session,
                stream,
                data: &PING,
            },
        );
        self.sent = now;
        self.back = 0;
    }

    /// Read what came back. Returns whether the last round trip is in.
    fn read(&mut self, node: &mut Node, now: u64) -> bool {
        let Some(stream) = self.stream else { return false };
        let mut buf = [0u8; 64];
        loop {
            let (n, _) = node.read(now, self.session, stream, &mut buf);
            if n == 0 {
                return false;
            }
            self.back += n;
            if self.back >= PING.len() {
                #[allow(clippy::cast_possible_truncation, reason = "a round trip is far below an hour")]
                let micros = ((now - self.sent) / 1000) as u32;
                self.trips[self.done] = micros;
                self.done += 1;
                if self.done == TRIPS {
                    return true;
                }
                self.ping(node, now);
            }
        }
    }

    fn report(&mut self) {
        self.trips.sort_unstable();
        let pick = |p: usize| self.trips[(TRIPS * p / 100).min(TRIPS - 1)];
        report!(
            "round_trip role=dialer bytes={} n={TRIPS} min_us={} p10_us={} median_us={} p90_us={} max_us={}",
            PING.len(),
            self.trips[0],
            pick(10),
            pick(50),
            pick(90),
            pick(100)
        );
    }
}

/// Open the stream of a session the board dialed, once the session lets it.
fn continue_dial(dial: &mut Option<Dial>, node: &mut Node, costs: &mut Costs, now: u64) {
    if let Some(d) = dial
        && d.stream.is_none()
        && d.done == 0
    {
        timed(&mut costs.events, || d.open(node, now));
    }
}

/// In the DTCM RAM (see `memory.x`), which nothing zeroes: the node's builder writes it before anything reads it.
#[unsafe(link_section = ".dtcm")]
static mut MEMORY: MaybeUninit<Memory> = MaybeUninit::uninit();
static mut SLOTS: SlotTable<'static> = MaybeUninit::uninit();
/// In the ITCM RAM (see `memory.x`).
#[unsafe(link_section = ".itcm")]
static mut ENDPOINT: EpPlace<'static, 'static> = MaybeUninit::uninit();

#[allow(clippy::too_many_lines, reason = "the start and the loop of one program")]
#[entry]
fn main() -> ! {
    board::paint_stack();
    let Some(core) = cortex_m::Peripherals::take() else {
        halt()
    };
    board::init(core);
    crypto::init();

    let Some(seed) = board::random_seed() else {
        report!("failed random_generator");
        halt()
    };
    // SAFETY: `main` runs once and nothing else names these statics, so each is borrowed exactly once.
    let (memory, slots, place) = unsafe {
        (
            (*core::ptr::addr_of_mut!(MEMORY)).write(Memory::new()),
            &mut *core::ptr::addr_of_mut!(SLOTS),
            &mut *core::ptr::addr_of_mut!(ENDPOINT),
        )
    };
    let t = board::now();
    let mut node = match Node::new(t, &seed, BOARD_ADDR, memory, slots, place) {
        Ok(node) => node,
        Err(e) => {
            report!("failed build={e:?}");
            halt()
        }
    };
    let built = board::now() - t;
    let built_stack = board::stack_peak();
    let timings = crypto::measure(board::now);
    // What the board is, in three lines; the last one closes the description.
    let describe = |node: &Node| {
        report!(
            "image clock_hz={} baud={} flash={} statics={} stack_room={}",
            board::CORE_HZ,
            board::BAUD,
            board::image_len(),
            board::statics_len() + size_of::<Memory>() + size_of::<Ep>(),
            board::stack_size()
        );
        let mut id = Line::new();
        let _ = write!(id, "node id=");
        for b in node.id().bytes {
            let _ = write!(id, "{b:02x}");
        }
        id.send();
        report!(
            "crypto provider={}",
            if cfg!(feature = "chip-crypto") {
                "chip"
            } else {
                "software"
            }
        );
        for t in &timings {
            let mut line = Line::new();
            let _ = write!(line, "crypto name={} software_ns={}", t.name, t.software_ns);
            if let Some(chip) = t.chip_ns {
                let _ = write!(line, " chip_ns={chip} agree={}", t.agree);
            }
            line.send();
        }
        report!(
            "built us={} endpoint={} slot={} memory={} node={} stack_peak={}",
            built / 1000,
            size_of::<Ep>(),
            size_of::<EpSlot>(),
            size_of::<Memory>(),
            size_of::<Node>(),
            built_stack
        );
    };
    describe(&node);

    let mut echo = Echo::new();
    let mut dial: Option<Dial> = None;
    let mut line = Deframer::<{ encoded_max(BODY) }>::new();
    let mut out = [0u8; BODY];
    let mut enc = [0u8; encoded_max(BODY)];
    let mut costs = Costs::default();
    // When the handshake under way started: the first datagram of a session the laptop dials, or the board's dial.
    let mut started: Option<u64> = None;
    let mut session_from = 0;
    loop {
        while let Some(byte) = board::read() {
            let Some(frame) = line.push(byte) else { continue };
            let Some((&kind, body)) = frame.split_first_mut().map(|(k, d)| (&*k, d)) else {
                continue;
            };
            match (kind, body.first()) {
                (kind::CONTROL, Some(b'I')) => describe(&node),
                (kind::CONTROL, Some(b'D')) => {
                    let Some(Ok(bytes)) = body.get(1..33).map(<[u8; 32]>::try_from) else {
                        continue;
                    };
                    let peer = pinc_crypto::NodeId {
                        alg: pinc_crypto::IdentityAlg::Ed25519,
                        bytes,
                    };
                    let now = board::now();
                    costs = Costs::default();
                    started = Some(now);
                    let asked = timed(&mut costs.events, || {
                        node.command(
                            now,
                            Command::Connect {
                                node: peer,
                                alpn: ALPN,
                                addrs: &[PEER_ADDR],
                                role: Role::Other,
                            },
                        )
                    });
                    match asked {
                        Ok(Value::Session(session)) => {
                            dial = Some(Dial {
                                session,
                                stream: None,
                                sent: 0,
                                back: 0,
                                trips: [0; TRIPS],
                                done: 0,
                            });
                        }
                        other => report!("failed dial={other:?}"),
                    }
                }
                (kind::DATAGRAM, _) => {
                    if started.is_none() {
                        started = Some(board::now());
                        costs = Costs::default();
                    }
                    timed(&mut costs.rx, || {
                        node.ep.handle_datagram(board::now(), BOARD_ADDR, PEER_ADDR, body);
                    });
                    break;
                }
                _ => {}
            }
        }
        if node.ep.poll_timeout().is_some_and(|t| t <= board::now()) {
            timed(&mut costs.timer, || node.ep.handle_timeout(board::now()));
        }
        while let Some(ev) = timed(&mut costs.events, || node.next_event(board::now())) {
            let now = board::now();
            match ev {
                // A session the laptop dialed is open, or one the board dialed ended its handshake: a first session
                // is reported when it does, and one that resumes is reported at once and answered later.
                Event::Incoming { .. } | Event::Connected { .. } | Event::Answered { .. } => {
                    let wall = now - started.unwrap_or(now);
                    match ev {
                        Event::Connected { .. } if costs.rx.calls == 0 => {
                            report!(
                                "reported early=true wall_us={} cpu_us={}",
                                wall / 1000,
                                costs.total() / 1000
                            );
                            continue_dial(&mut dial, &mut node, &mut costs, now);
                            continue;
                        }
                        Event::Connected { .. } => costs.report("handshake role=dialer resumed=false", wall),
                        Event::Answered { resumed: true, .. } => {
                            costs.report("handshake role=dialer resumed=true", wall);
                        }
                        Event::Answered { .. } => costs.report("handshake role=dialer resumed=false early=true", wall),
                        _ => costs.report("handshake role=acceptor", wall),
                    }
                    report!("stack peak={} after=handshake", board::stack_peak());
                    costs = Costs::default();
                    session_from = now;
                }
                Event::ConnectFailed { reason, .. } => {
                    report!("failed dial={reason:?}");
                    dial = None;
                    started = None;
                }
                Event::Closed { reason, session } => {
                    costs.report("session", now - session_from);
                    report!(
                        "closed reason={reason:?} echoed={} stack_peak={} rx_lost={}",
                        echo.bytes,
                        board::stack_peak(),
                        board::RX_LOST.load(Ordering::Relaxed)
                    );
                    report!(
                        "crypto packets aes_on_chip={} chacha_in_software={}",
                        crypto::AES_PACKETS.load(Ordering::Relaxed),
                        crypto::CHACHA_PACKETS.load(Ordering::Relaxed)
                    );
                    started = None;
                    if dial.as_ref().is_some_and(|d| d.session == session) {
                        dial = None;
                    }
                }
                _ => {}
            }
            // A session the board dialed is the board's to drive; any other is echoed.
            match &mut dial {
                Some(d) if ev.session() == Some(d.session) => {
                    let ended = matches!(ev, Event::StreamReadable { .. })
                        && timed(&mut costs.events, || d.read(&mut node, now));
                    if ended {
                        d.report();
                        let session = d.session;
                        let _ = timed(&mut costs.events, || {
                            node.command(now, Command::Close { session, error: 0 })
                        });
                    }
                }
                _ => timed(&mut costs.events, || echo.on_event(&mut node, now, &ev)),
            }
        }
        continue_dial(&mut dial, &mut node, &mut costs, board::now());
        while let Some(t) = timed(&mut costs.tx, || node.ep.poll_transmit(board::now(), &mut out[1..])) {
            out[0] = kind::DATAGRAM;
            if let Some(n) = encode(&out[..=t.len], &mut enc) {
                board::write(&enc[..n]);
            }
        }
    }
}

fn halt() -> ! {
    loop {
        cortex_m::asm::nop();
    }
}

/// A fault most likely means the stack left its region at the lower end, so the handler starts by giving itself the
/// whole stack again; nothing returns from it.
#[unsafe(naked)]
#[unsafe(no_mangle)]
unsafe extern "C" fn HardFault() -> ! {
    core::arch::naked_asm!("ldr r0, =_stack_start", "msr msp, r0", "b {fault}", fault = sym fault)
}

extern "C" fn fault() -> ! {
    // The configurable fault status and the two faulting addresses, where the core recorded them. A stack that left
    // its room reads as `cfsr=0x00000092` with `mmfar` below the stack's lower end.
    // SAFETY: plain reads of three registers of the system control block.
    let (cfsr, mmfar, bfar) = unsafe {
        (
            (0xE000_ED28 as *const u32).read_volatile(),
            (0xE000_ED34 as *const u32).read_volatile(),
            (0xE000_ED38 as *const u32).read_volatile(),
        )
    };
    report!(
        "fault cfsr={cfsr:#010x} mmfar={mmfar:#010x} bfar={bfar:#010x} stack_room={}",
        board::stack_size()
    );
    halt()
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    cortex_m::interrupt::disable();
    if let Some(at) = info.location() {
        report!("panic at={}:{}", at.file(), at.line());
    } else {
        report!("panic");
    }
    halt()
}
