//! The laptop's end of the board's serial line.
//!
//! ```text
//! pinc-mcu-peer flash <image.elf> [--port /dev/ttyACM0]    load an image into the board's external flash
//! pinc-mcu-peer run [--out <file>] [--rounds 10]           handshakes and round trips with the board, both ways
//!                    [--laptop-dials-only]                  (or only the sessions the laptop dials)
//! pinc-mcu-peer watch [--port /dev/ttyACM0]                print what the board reports
//! ```
//!
//! `flash` talks to the boot stage, which listens for half a second after it starts: start this first, then the
//! boot stage. `run` talks to the image: it runs the same endpoint as the board, with the tables of a host, over the
//! same framing.

use std::io::{Read as _, Write as _};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use pinc_core::{Command, Event, Role, SessionId, Value};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_mcu_link::app::Echo;
use pinc_mcu_link::frame::{Deframer, encode, encoded_max};
use pinc_mcu_link::{ALPN, BOARD_ADDR, EpPlace, MTU, Memory, Node, PEER_ADDR, SlotTable, kind, load};

/// Where the board's external flash is mapped.
const FLASH_BASE: u64 = 0x7000_0000;
const FLASH_LEN: u64 = 32 << 20;
const SECTOR: usize = 4096;
const BAUD: u32 = 1_000_000;

type Failure = Box<dyn std::error::Error>;

/// The serial line, in frames.
struct Line {
    port: Box<dyn serialport::SerialPort>,
    deframer: Box<Deframer<8192>>,
    /// Bytes read from the port and not yet deframed.
    pending: Vec<u8>,
    at: usize,
}

impl Line {
    fn open(path: &str) -> Result<Self, Failure> {
        let port = serialport::new(path, BAUD).timeout(Duration::from_millis(1)).open()?;
        // What the board said before this program listened is not for it.
        port.clear(serialport::ClearBuffer::Input)?;
        Ok(Self {
            port,
            deframer: Box::new(Deframer::new()),
            pending: Vec::new(),
            at: 0,
        })
    }

    fn send(&mut self, kind: u8, body: &[u8]) -> Result<(), Failure> {
        let mut raw = Vec::with_capacity(body.len() + 1);
        raw.push(kind);
        raw.extend_from_slice(body);
        let mut enc = vec![0u8; encoded_max(raw.len())];
        let n = encode(&raw, &mut enc).ok_or("the frame does not fit")?;
        // The port's timeout is short, for the reads; a frame takes longer than that to leave.
        let mut rest = &enc[..n];
        while !rest.is_empty() {
            match self.port.write(rest) {
                Ok(n) => rest = &rest[n..],
                Err(e) if e.kind() == std::io::ErrorKind::TimedOut => {}
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    }

    /// The next frame, if one is complete within the port's timeout: its kind and its body.
    fn next(&mut self) -> Result<Option<(u8, Vec<u8>)>, Failure> {
        loop {
            while let Some(&byte) = self.pending.get(self.at) {
                self.at += 1;
                if let Some(frame) = self.deframer.push(byte)
                    && let Some((&kind, body)) = frame.split_first()
                {
                    return Ok(Some((kind, body.to_vec())));
                }
            }
            self.pending.resize(4096, 0);
            self.at = 0;
            match self.port.read(&mut self.pending) {
                Ok(n) => self.pending.truncate(n),
                Err(e) if e.kind() == std::io::ErrorKind::TimedOut => {
                    self.pending.clear();
                    return Ok(None);
                }
                Err(e) => return Err(e.into()),
            }
            if self.pending.is_empty() {
                return Ok(None);
            }
        }
    }
}

fn text(body: &[u8]) -> String {
    String::from_utf8_lossy(body).into_owned()
}

/// The bytes an ELF image puts in the external flash, from its first byte there.
fn flash_image(elf: &[u8]) -> Result<Vec<u8>, Failure> {
    let u16_at = |at: usize| elf.get(at..at + 2).map(|b| u16::from_le_bytes([b[0], b[1]]));
    let u32_at = |at: usize| {
        elf.get(at..at + 4)
            .map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    };
    if elf.get(..6) != Some(b"\x7fELF\x01\x01") {
        return Err("not a 32-bit little-endian ELF file".into());
    }
    let bad = || -> Failure { "the ELF file is cut short".into() };
    let (phoff, phentsize, phnum) = (
        u32_at(0x1c).ok_or_else(bad)? as usize,
        usize::from(u16_at(0x2a).ok_or_else(bad)?),
        usize::from(u16_at(0x2c).ok_or_else(bad)?),
    );
    let mut image = Vec::new();
    for i in 0..phnum {
        let ph = phoff + i * phentsize;
        let (kind, offset, paddr, filesz) = (
            u32_at(ph).ok_or_else(bad)?,
            u32_at(ph + 4).ok_or_else(bad)? as usize,
            u64::from(u32_at(ph + 12).ok_or_else(bad)?),
            u32_at(ph + 16).ok_or_else(bad)? as usize,
        );
        if kind != 1 || filesz == 0 {
            continue;
        }
        if !(FLASH_BASE..FLASH_BASE + FLASH_LEN).contains(&paddr) {
            return Err(format!("a segment loads at {paddr:#x}, outside the external flash").into());
        }
        let at = usize::try_from(paddr - FLASH_BASE)?;
        if image.len() < at + filesz {
            image.resize(at + filesz, 0xff);
        }
        image[at..at + filesz].copy_from_slice(elf.get(offset..offset + filesz).ok_or_else(bad)?);
    }
    if image.is_empty() {
        return Err("the ELF file loads nothing".into());
    }
    // The boot stage programs whole words.
    image.resize(image.len().next_multiple_of(4), 0xff);
    Ok(image)
}

fn crc32(data: &[u8]) -> u32 {
    let mut crc = !0u32;
    for &b in data {
        crc ^= u32::from(b);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xEDB8_8320 & 0u32.wrapping_sub(crc & 1));
        }
    }
    !crc
}

/// Send a request to the boot stage and wait for its answer.
fn ask(line: &mut Line, request: &[u8], wait: Duration) -> Result<Vec<u8>, Failure> {
    line.send(kind::CONTROL, request)?;
    let until = Instant::now() + wait;
    while Instant::now() < until {
        match line.next()? {
            Some((kind::CONTROL, body)) if body.first() == request.first() => return Ok(body),
            Some((kind::REPORT, body)) => println!("board: {}", text(&body)),
            _ => {}
        }
    }
    Err(format!("no answer to request {:?}", char::from(request[0])).into())
}

fn done(answer: &[u8]) -> Result<(), Failure> {
    if answer.get(1) == Some(&0) {
        Ok(())
    } else {
        Err(format!(
            "the boot stage refused request {:?}",
            answer.first().map(|b| char::from(*b))
        )
        .into())
    }
}

fn flash(port: &str, path: &str) -> Result<(), Failure> {
    let image = flash_image(&std::fs::read(path)?)?;
    let mut line = Line::open(port)?;
    println!(
        "{} bytes for the external flash; waiting for the boot stage",
        image.len()
    );
    let until = Instant::now() + Duration::from_secs(60);
    loop {
        if ask(&mut line, &[load::ENTER], Duration::from_millis(40)).is_ok() {
            break;
        }
        if Instant::now() > until {
            return Err("the boot stage did not answer in 60 s".into());
        }
    }
    let started = Instant::now();
    for sector in 0..image.len().div_ceil(SECTOR) {
        let mut req = vec![load::ERASE];
        req.extend_from_slice(&u32::try_from(sector * SECTOR)?.to_le_bytes());
        done(&ask(&mut line, &req, Duration::from_secs(5))?)?;
    }
    println!("erased in {:.1} s", started.elapsed().as_secs_f64());
    for (i, step) in image.chunks(load::STEP).enumerate() {
        let mut req = vec![load::WRITE];
        req.extend_from_slice(&u32::try_from(i * load::STEP)?.to_le_bytes());
        req.extend_from_slice(step);
        done(&ask(&mut line, &req, Duration::from_secs(5))?)?;
    }
    println!("programmed in {:.1} s", started.elapsed().as_secs_f64());
    let mut req = vec![load::CHECK];
    req.extend_from_slice(&0u32.to_le_bytes());
    req.extend_from_slice(&u32::try_from(image.len())?.to_le_bytes());
    let answer = ask(&mut line, &req, Duration::from_secs(60))?;
    let theirs = answer.get(1..5).map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]));
    if theirs != Some(crc32(&image)) {
        return Err(format!("the flash reads back {theirs:08x?}, the image is {:08x}", crc32(&image)).into());
    }
    println!(
        "checked in {:.1} s; starting the image",
        started.elapsed().as_secs_f64()
    );
    done(&ask(&mut line, &[load::GO], Duration::from_secs(2))?)?;
    let until = Instant::now() + Duration::from_secs(3);
    while Instant::now() < until {
        if let Some((kind::REPORT, body)) = line.next()? {
            println!("board: {}", text(&body));
        }
    }
    Ok(())
}

fn watch(port: &str) -> Result<(), Failure> {
    let mut line = Line::open(port)?;
    loop {
        if let Some((kind::REPORT, body)) = line.next()? {
            println!("board: {}", text(&body));
        }
    }
}

/// The laptop's endpoint on the line.
struct Host {
    line: Line,
    node: Node<'static, 'static, 'static>,
    epoch: Instant,
    /// Everything said, in order: the board's reports as `board ...`, the laptop's own lines as `laptop ...`.
    log: Vec<String>,
    /// Datagrams and their bytes, each way.
    sent: (u64, u64),
    received: (u64, u64),
    /// When the peer answered a session that was reported before its handshake ended, and whether it resumed.
    answered: Option<(Instant, bool)>,
}

/// A node with a new identity, on memory that lives as long as the program.
fn fresh_node(now: u64) -> Result<Node<'static, 'static, 'static>, Failure> {
    let mut seed = [0u8; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut seed)?;
    let memory: &'static mut Memory = Box::leak(Box::new(Memory::new()));
    let slots: &'static mut SlotTable<'static> = Box::leak(Box::new(SlotTable::uninit()));
    let place: &'static mut EpPlace<'static, 'static> = Box::leak(Box::new(EpPlace::uninit()));
    Node::new(now, &seed, PEER_ADDR, memory, slots, place).map_err(|e| format!("{e:?}").into())
}

impl Host {
    fn now(&self) -> u64 {
        1_000_000_000 + u64::try_from(self.epoch.elapsed().as_nanos()).unwrap_or(u64::MAX)
    }

    /// The node's next event. The answer to an early session is noted on the way.
    fn event(&mut self) -> Option<Event> {
        let now = self.now();
        let ev = self.node.next_event(now)?;
        if let Event::Answered { resumed, .. } = ev {
            self.answered = Some((Instant::now(), resumed));
        }
        Some(ev)
    }

    fn say(&mut self, line: String) {
        println!("{line}");
        self.log.push(line);
    }

    /// How many of the board's reports start with `prefix`.
    fn count(&self, prefix: &str) -> usize {
        self.log
            .iter()
            .filter(|l| l.strip_prefix("board ").is_some_and(|r| r.starts_with(prefix)))
            .count()
    }

    /// Carry datagrams both ways and serve the endpoint's timer, for at most the port's timeout.
    fn turn(&mut self) -> Result<(), Failure> {
        self.flush()?;
        while let Some((kind, mut body)) = self.line.next()? {
            match kind {
                kind::DATAGRAM => {
                    self.received.0 += 1;
                    self.received.1 += body.len() as u64;
                    let now = self.now();
                    self.node.ep.handle_datagram(now, PEER_ADDR, BOARD_ADDR, &mut body);
                    break;
                }
                kind::REPORT => self.say(format!("board {}", text(&body))),
                _ => {}
            }
        }
        let now = self.now();
        if self.node.ep.poll_timeout().is_some_and(|t| t <= now) {
            self.node.ep.handle_timeout(now);
        }
        self.flush()
    }

    fn flush(&mut self) -> Result<(), Failure> {
        let mut out = [0u8; 2048];
        loop {
            let now = self.now();
            let Some(t) = self.node.ep.poll_transmit(now, &mut out) else {
                return Ok(());
            };
            if t.len > usize::from(MTU) {
                return Err("the endpoint wrote a datagram above the line's size".into());
            }
            self.sent.0 += 1;
            self.sent.1 += t.len as u64;
            self.line.send(kind::DATAGRAM, &out[..t.len])?;
        }
    }

    /// Run the line until `stop` returns a value for an event, or `wait` has passed.
    fn until<T>(&mut self, wait: Duration, mut stop: impl FnMut(&mut Self, Event) -> Option<T>) -> Result<T, Failure> {
        let until = Instant::now() + wait;
        loop {
            while let Some(ev) = self.event() {
                if let Event::ConnectFailed { reason, .. } = ev {
                    return Err(format!("the dial failed: {reason:?}").into());
                }
                if let Some(v) = stop(self, ev) {
                    return Ok(v);
                }
            }
            if Instant::now() > until {
                return Err("timed out".into());
            }
            self.turn()?;
        }
    }

    /// Run the line until the board has made `n` reports that start with `prefix`.
    fn until_reports(&mut self, prefix: &str, n: usize, wait: Duration) -> Result<(), Failure> {
        let until = Instant::now() + wait;
        while self.count(prefix) < n {
            if Instant::now() > until {
                return Err(format!("the board did not report `{prefix}`").into());
            }
            while self.event().is_some() {}
            self.turn()?;
        }
        Ok(())
    }

    /// Dial the board, and write 32 bytes as soon as the session is reported. A first session is reported when its
    /// handshake ends; one that resumes is reported at once, its first bytes leave with the first flight, and the
    /// handshake ends when the board answers. Returns the session, its stream, the time to the end of the handshake
    /// and the time to the first bytes back, in microseconds, and whether the session resumed.
    fn dial(&mut self, board: NodeId) -> Result<(SessionId, u64, f64, f64, bool), Failure> {
        let before = (self.sent, self.received);
        self.answered = None;
        let dialed = Instant::now();
        let now = self.now();
        let Value::Session(session) = self
            .node
            .command(
                now,
                Command::Connect {
                    node: board,
                    alpn: ALPN,
                    addrs: &[BOARD_ADDR],
                    role: Role::Other,
                },
            )
            .map_err(|e| format!("{e:?}"))?
        else {
            return Err("the dial named no session".into());
        };
        self.until(Duration::from_secs(30), |_, ev| {
            matches!(ev, Event::Connected { .. }).then_some(())
        })?;
        let connected = dialed.elapsed();
        let early = self.received.0 == before.1.0;
        let stream = self.open(session)?;
        self.echo(session, stream, &[0xA5; 32])?;
        let first_byte = dialed.elapsed();
        let (handshake, resumed) = if early {
            let until = Instant::now() + Duration::from_secs(10);
            loop {
                if let Some((at, resumed)) = self.answered {
                    break (at.duration_since(dialed), resumed);
                }
                if Instant::now() > until {
                    return Err("the board never answered the early session".into());
                }
                while self.event().is_some() {}
                self.turn()?;
            }
        } else {
            (connected, false)
        };
        self.say(format!(
            "laptop handshake role=dialer resumed={resumed} reported_us={:.0} handshake_us={:.0} first_byte_us={:.0} datagrams_out={} bytes_out={} datagrams_in={} bytes_in={}",
            micros(connected),
            micros(handshake),
            micros(first_byte),
            self.sent.0 - before.0.0,
            self.sent.1 - before.0.1,
            self.received.0 - before.1.0,
            self.received.1 - before.1.1,
        ));
        Ok((session, stream, micros(handshake), micros(first_byte), resumed))
    }

    /// Open a stream both ways, once the handshake's own buffers are back in the pool.
    fn open(&mut self, session: SessionId) -> Result<u64, Failure> {
        let opening = Instant::now();
        loop {
            let now = self.now();
            match self.node.command(now, Command::OpenStream { session, bidi: true }) {
                Ok(Value::Stream(stream)) => return Ok(stream),
                Ok(_) => return Err("no stream".into()),
                Err(e) if opening.elapsed() > Duration::from_secs(10) => return Err(format!("no stream: {e:?}").into()),
                Err(_) => self.turn()?,
            }
        }
    }

    /// Close the session and wait until the board says it saw the close.
    fn close(&mut self, session: SessionId) -> Result<(), Failure> {
        let closed = self.count("closed ");
        let now = self.now();
        let _ = self.node.command(now, Command::Close { session, error: 0 });
        self.until_reports("closed ", closed + 1, Duration::from_secs(10))
    }

    /// Write `data` on the stream and wait until as many bytes came back. Returns the time it took.
    fn echo(&mut self, session: SessionId, stream: u64, data: &[u8]) -> Result<Duration, Failure> {
        let started = Instant::now();
        let (mut written, mut back) = (0, 0);
        let mut buf = vec![0u8; 16 * 1024];
        let until = started + Duration::from_secs(120);
        while back < data.len() {
            let now = self.now();
            if written < data.len()
                && let Ok(Value::Written(w)) = self.node.command(
                    now,
                    Command::Write {
                        session,
                        stream,
                        data: &data[written..],
                    },
                )
            {
                written += w;
            }
            while let Some(ev) = self.event() {
                if let Event::Closed { reason, .. } = ev {
                    return Err(format!("the session closed: {reason:?}").into());
                }
            }
            loop {
                let (n, _) = self.node.read(now, session, stream, &mut buf);
                if n == 0 {
                    break;
                }
                if buf[..n] != data[back..back + n] {
                    return Err("the echo differs from what was written".into());
                }
                back += n;
            }
            if back == data.len() {
                break;
            }
            if Instant::now() > until {
                return Err(format!("the echo stalled at {back} of {} bytes", data.len()).into());
            }
            self.turn()?;
        }
        Ok(started.elapsed())
    }

    /// Time `n` round trips of 32 bytes on the session's stream (the pool of a small endpoint holds one stream's
    /// buffers both ways and little else).
    fn round_trips(&mut self, session: SessionId, stream: u64, n: usize) -> Result<(), Failure> {
        let ping = [0xA5u8; 32];
        let mut trips = Vec::new();
        for _ in 0..n {
            trips.push(micros(self.echo(session, stream, &ping)?));
        }
        self.say(format!("laptop round_trip role=dialer bytes=32 {}", spread(&mut trips)));
        Ok(())
    }

    /// Ask the board to dial this node, write back what it sends, and wait until it has closed the session.
    fn accept(&mut self) -> Result<(), Failure> {
        let closed = self.count("closed ");
        let mut request = vec![b'D'];
        request.extend_from_slice(&self.node.id().bytes);
        self.line.send(kind::CONTROL, &request)?;
        let mut echo = Echo::new();
        let until = Instant::now() + Duration::from_secs(60);
        while self.count("closed ") <= closed {
            if Instant::now() > until {
                return Err("the board's session did not end".into());
            }
            while let Some(ev) = self.event() {
                let now = self.now();
                echo.on_event(&mut self.node, now, &ev);
            }
            self.turn()?;
        }
        if self.log.iter().rev().take(8).any(|l| l.starts_with("board failed")) {
            return Err("the board's dial failed".into());
        }
        Ok(())
    }
}

fn micros(d: Duration) -> f64 {
    d.as_secs_f64() * 1e6
}

/// `n=.. min_us=.. p10_us=.. median_us=.. p90_us=.. max_us=..` of times in microseconds.
fn spread(v: &mut [f64]) -> String {
    if v.is_empty() {
        return "n=0".into();
    }
    v.sort_by(f64::total_cmp);
    let pick = |p: usize| v[(v.len() * p / 100).min(v.len() - 1)];
    format!(
        "n={} min_us={:.0} p10_us={:.0} median_us={:.0} p90_us={:.0} max_us={:.0}",
        v.len(),
        v[0],
        pick(10),
        pick(50),
        pick(90),
        pick(100)
    )
}

/// The value of `key=` in a report.
fn field(line: &str, key: &str) -> Option<f64> {
    line.split(' ')
        .find_map(|w| w.strip_prefix(key)?.strip_prefix('=')?.parse().ok())
}

fn parse_node(line: &str) -> Option<NodeId> {
    let hex = line.strip_prefix("node id=")?;
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    })
}

/// The board's reports of one kind made from log line `from` on: one of their fields, as a spread.
fn board_spread(log: &[String], from: usize, prefix: &str, key: &str) -> String {
    let mut v: Vec<f64> = log[from..]
        .iter()
        .filter_map(|l| {
            l.strip_prefix("board ")?
                .strip_prefix(prefix)
                .and_then(|r| field(r, key))
        })
        .collect();
    if v.is_empty() { "n=0".into() } else { spread(&mut v) }
}

#[allow(
    clippy::too_many_lines,
    clippy::cast_precision_loss,
    reason = "the run is one sequence of steps; byte counts are far below 2^52"
)]
fn run(port: &str, out: Option<&str>, rounds: usize, board_dials: bool) -> Result<(), Failure> {
    let mut line = Line::open(port)?;
    // Ask the board what it is; it also says so when it starts.
    let mut log = Vec::new();
    let until = Instant::now() + Duration::from_secs(20);
    let mut asked: Option<Instant> = None;
    let board = loop {
        if asked.is_none_or(|t| t.elapsed() > Duration::from_millis(500)) {
            line.send(kind::CONTROL, b"I")?;
            asked = Some(Instant::now());
        }
        if let Some((kind::REPORT, body)) = line.next()? {
            println!("board {}", text(&body));
            log.push(format!("board {}", text(&body)));
        }
        // The line that follows the id closes the board's description of itself.
        let id = log.iter().find_map(|l| parse_node(l.strip_prefix("board ")?));
        if log.iter().any(|l| l.starts_with("board built "))
            && let Some(id) = id
        {
            break id;
        }
        if Instant::now() > until {
            return Err("the board did not say who it is".into());
        }
    };
    // One description is enough: a second answer to the request may still be on the line.
    log.dedup();

    let mut host = Host {
        line,
        node: fresh_node(1_000_000_000)?,
        epoch: Instant::now(),
        log,
        sent: (0, 0),
        received: (0, 0),
        answered: None,
    };
    let mut summary = Vec::new();

    // 1. The laptop dials with an identity the board has not seen: a full handshake each time.
    // 2. The same identity dials again: the ticket of the session before resumes.
    let mut first_long = true;
    for resume in [false, true] {
        let from = host.log.len();
        let (mut handshakes, mut first_bytes) = (Vec::new(), Vec::new());
        for _ in 0..rounds {
            if !resume {
                let now = host.now();
                host.node = fresh_node(now)?;
            }
            let (session, stream, handshake, first_byte, resumed) = host.dial(board)?;
            if resumed != resume {
                return Err(format!("a session that should have resumed={resume} resumed={resumed}").into());
            }
            handshakes.push(handshake);
            first_bytes.push(first_byte);
            if first_long {
                // The long measurements, once: 200 round trips, then 256 KiB there and back.
                first_long = false;
                host.round_trips(session, stream, 200)?;
                let bulk: Vec<u8> = (0..256 * 1024u32)
                    .map(|i| (i.wrapping_mul(2_654_435_761) >> 24) as u8)
                    .collect();
                let took = host.echo(session, stream, &bulk)?;
                host.say(format!(
                    "laptop echo bytes={} wall_us={:.0} kib_per_s={:.1}",
                    bulk.len(),
                    micros(took),
                    bulk.len() as f64 / 1024.0 / took.as_secs_f64()
                ));
            } else {
                host.round_trips(session, stream, 20)?;
            }
            host.close(session)?;
        }
        let what = format!("summary handshake board=acceptor resumed={resume}");
        summary.push(format!("{what} laptop_handshake {}", spread(&mut handshakes)));
        summary.push(format!("{what} laptop_first_byte {}", spread(&mut first_bytes)));
        for key in ["cpu_us", "wall_us"] {
            summary.push(format!(
                "{what} board_{} {}",
                key.trim_end_matches("_us"),
                board_spread(&host.log, from, "handshake role=acceptor", key)
            ));
        }
    }

    // 3. The board dials a laptop it has not seen, and times its own round trips: a full handshake each time.
    let from = host.log.len();
    let rounds = if board_dials { rounds } else { 0 };
    for _ in 0..rounds {
        let now = host.now();
        host.node = fresh_node(now)?;
        host.accept()?;
    }
    for key in ["cpu_us", "wall_us"] {
        summary.push(format!(
            "summary handshake board=dialer resumed=false board_{} {}",
            key.trim_end_matches("_us"),
            board_spread(&host.log, from, "handshake role=dialer resumed=false", key)
        ));
    }
    // 4. The board dials the same laptop again.
    let from = host.log.len();
    for _ in 0..rounds {
        host.accept()?;
    }
    for key in ["cpu_us", "wall_us"] {
        summary.push(format!(
            "summary handshake board=dialer resumed=true board_{} {}",
            key.trim_end_matches("_us"),
            board_spread(&host.log, from, "handshake role=dialer resumed=true", key)
        ));
    }
    summary.push(format!(
        "summary round_trip bytes=32 timed_by=board median_of_medians {}",
        board_spread(&host.log, 0, "round_trip role=dialer", "median_us")
    ));
    summary.push(format!(
        "summary stack board_peak_bytes={:.0}",
        host.log
            .iter()
            .filter_map(|l| field(l, "stack_peak").or_else(|| field(l, "peak")))
            .fold(0.0, f64::max)
    ));
    summary.push(format!(
        "summary line baud={BAUD} datagrams_out={} bytes_out={} datagrams_in={} bytes_in={}",
        host.sent.0, host.sent.1, host.received.0, host.received.1
    ));
    println!();
    for s in &summary {
        println!("{s}");
    }
    if let Some(path) = out {
        let mut text = host.log.join("\n");
        text.push('\n');
        text.push_str(&summary.join("\n"));
        text.push('\n');
        std::fs::write(path, text)?;
        println!("written to {path}");
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let option = |name: &str| {
        args.iter()
            .position(|a| a == name)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let port = option("--port").unwrap_or_else(|| "/dev/ttyACM0".into());
    let done = match args.first().map(String::as_str) {
        Some("flash") => match args.get(1) {
            Some(path) => flash(&port, path),
            None => Err("flash needs the image's path".into()),
        },
        Some("watch") => watch(&port),
        Some("run") => {
            // The endpoint is built by value before it is moved to its place, so the thread has the stack for it.
            let out = option("--out");
            let rounds = option("--rounds").and_then(|r| r.parse().ok()).unwrap_or(10);
            let board_dials = !args.iter().any(|a| a == "--laptop-dials-only");
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn(move || run(&port, out.as_deref(), rounds, board_dials).map_err(|e| e.to_string()))
                .map_err(Failure::from)
                .and_then(|t| t.join().map_err(|_| Failure::from("the run panicked")))
                .and_then(|r| r.map_err(Failure::from))
        }
        _ => Err(
            "usage: pinc-mcu-peer flash <image.elf> | run [--out <file>] [--rounds <n>] | watch   [--port <tty>]"
                .into(),
        ),
    };
    match done {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}
