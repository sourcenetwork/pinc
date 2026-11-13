//! The hub stream codec, recorded for the proofs (`mcodec.ndjson`).
//!
//! The real `Frame::parse`, `Frame::read` and `Frame::encode` run on valid frames of every kind and boundary
//! (incarnations at every limb boundary, flags, snapshots of 0 to 65 entries, DOWN proofs of 1 to 4 probes on every
//! path, passthrough frames with topics of 0, 1 and 255 bytes), on every proper cut of them, with trailing bytes, with
//! every single byte changed, on streams with a partial tail, on prefixes that name a body above the limit, on
//! encodings into buffers too small, and on seeded random garbage. One line per call: the bytes in, the result out
//! (the frame in the schema of `SPEC`, or the refusal as the class the Lean model and `HubCodec.tla` name).
//!
//! The test asserts the codec's laws itself against a plain tracker: a valid frame parses back from its encoding,
//! the encoding has the length `body_len` states, an accepted body (changed, cut or extended) re-encodes to the same
//! bytes, every proper prefix of a frame is a partial read, and a prefix naming a body above `MAX_BODY` is refused.
//! The TLA+ check (`TraceHubCodec.tla`) and the Lean replay (`Vinc.TraceMembershipCodec`) apply the proved model
//! to the same bytes and compare.

use vinc_membership::codec::{
    Alive, Down, ENTRY_LEN, Frame, FrameError, Hello, MAX_BODY, MAX_PROBES, Other, Path, Probe, Proof, Record, Snap,
    entry_bytes, ty,
};
use vinc_tests::SplitMix64;
use vinc_wire::WireError;

use crate::common::{TraceWriter, b, limbs, list};

const FILE: &str = "mcodec.ndjson";

fn class(e: &FrameError) -> &'static str {
    match e {
        FrameError::Wire(WireError::Truncated { .. }) => "short",
        FrameError::Wire(WireError::BufferTooSmall { .. }) => "bufferSmall",
        FrameError::Wire(w) => panic!("unexpected wire error {w:?}"),
        FrameError::TooLarge => "tooLarge",
        FrameError::Malformed(m) => match *m {
            "membership frame with a topic" => "topic",
            "reserved HELLO flag" => "helloFlag",
            "HELLO length" => "helloLen",
            "ACK is empty" => "ackLen",
            "PROBE is empty" => "probeLen",
            "DELTA length" => "deltaLen",
            "reserved SNAP flag" => "snapFlag",
            "snapshot size" => "snapSize",
            "snapshot entry is not alive" => "snapNotAlive",
            "alive byte" => "aliveByte",
            "probe count" => "probeCount",
            "probe path" => "probePath",
            "DOWN length" => "downLen",
            "topic longer than 255 bytes" => "topicLong",
            other => panic!("unexpected refusal {other}"),
        },
    }
}

fn entry_json(m: &[u8; 32], r: &Record, a: Alive) -> String {
    format!(
        r#"{{"m":{},"inc":{},"ver":{},"th":{},"a":{}}}"#,
        list(m),
        limbs(r.inc),
        r.ver,
        list(&r.thash),
        a as u8
    )
}

/// A frame in the trace schema.
fn fj(f: &Frame<'_>) -> String {
    match f {
        Frame::Hello(h) => format!(
            r#"{{"k":"hello","inc":{},"ver":{},"th":{},"snap":{},"homed":{}}}"#,
            limbs(h.rec.inc),
            h.rec.ver,
            list(&h.rec.thash),
            b(h.snap),
            b(h.homed)
        ),
        Frame::Ack => r#"{"k":"ack"}"#.to_owned(),
        Frame::Probe => r#"{"k":"probe"}"#.to_owned(),
        Frame::Delta(e) => format!(r#"{{"k":"delta","e":{}}}"#, entry_json(e.member, &e.rec, e.alive)),
        Frame::Snap(s) => {
            let es: Vec<String> = s.entries().map(|e| entry_json(e.member, &e.rec, e.alive)).collect();
            format!(
                r#"{{"k":"snap","part":{},"more":{},"es":[{}]}}"#,
                b(s.partial),
                b(s.more),
                es.join(",")
            )
        }
        Frame::Down(d) => {
            let pr: Vec<String> = d
                .proof
                .probes()
                .iter()
                .map(|p| format!(r#"{{"age":{},"path":{}}}"#, limbs(u64::from(p.age_ms)), p.path as u8))
                .collect();
            format!(
                r#"{{"k":"down","m":{},"inc":{},"sil":{},"pr":[{}]}}"#,
                list(d.member),
                limbs(d.inc),
                limbs(u64::from(d.proof.silence_ms)),
                pr.join(",")
            )
        }
        Frame::Other(o) => format!(
            r#"{{"k":"other","ty":{},"topic":{},"rest":{}}}"#,
            o.ty,
            list(o.topic),
            list(o.rest)
        ),
    }
}

/// The recorder and the tallies the test asserts on.
struct Rec<'a> {
    tw: &'a mut TraceWriter,
    parsed_ok: usize,
    parsed_err: usize,
}

impl Rec<'_> {
    fn line(&mut self, s: &str) {
        self.tw.line(FILE, s);
    }

    /// `Frame::parse` on `body`, recorded; the frame if it parsed.
    fn parse(&mut self, body: &[u8]) -> Option<Vec<u8>> {
        match Frame::parse(body) {
            Ok(f) => {
                self.parsed_ok += 1;
                self.line(&format!(
                    r#"{{"t":"mc","op":"parse","b":{},"ok":{}}}"#,
                    list(body),
                    fj(&f)
                ));
                // An accepted body re-encodes to the same bytes (canonical form).
                let mut buf = vec![0u8; 8 + body.len() * 2 + 16];
                let enc = f.encode(&mut buf).unwrap().to_vec();
                assert_eq!(&enc[4..], body, "accepted body re-encodes to itself");
                assert_eq!(
                    u32::from_be_bytes(enc[..4].try_into().unwrap()) as usize,
                    body.len(),
                    "length prefix is the body length"
                );
                Some(enc)
            }
            Err(e) => {
                self.parsed_err += 1;
                self.line(&format!(
                    r#"{{"t":"mc","op":"parse","b":{},"err":"{}"}}"#,
                    list(body),
                    class(&e)
                ));
                None
            }
        }
    }

    /// `Frame::read` on `buf`, recorded.
    fn read(&mut self, buf: &[u8]) -> Result<Option<usize>, &'static str> {
        match Frame::read(buf) {
            Ok(Some((f, n))) => {
                self.line(&format!(
                    r#"{{"t":"mc","op":"read","b":{},"ok":{},"n":{}}}"#,
                    list(buf),
                    fj(&f),
                    n
                ));
                Ok(Some(n))
            }
            Ok(None) => {
                self.line(&format!(r#"{{"t":"mc","op":"read","b":{},"more":true}}"#, list(buf)));
                Ok(None)
            }
            Err(e) => {
                self.line(&format!(
                    r#"{{"t":"mc","op":"read","b":{},"err":"{}"}}"#,
                    list(buf),
                    class(&e)
                ));
                Err(class(&e))
            }
        }
    }

    /// `Frame::encode` of `f` into `cap` bytes, recorded; the bytes if it fitted.
    fn encode(&mut self, f: &Frame<'_>, cap: usize) -> Result<Vec<u8>, &'static str> {
        let mut buf = vec![0u8; cap];
        match f.encode(&mut buf) {
            Ok(bytes) => {
                let v = bytes.to_vec();
                self.line(&format!(
                    r#"{{"t":"mc","op":"enc","f":{},"cap":{},"b":{}}}"#,
                    fj(f),
                    cap,
                    list(&v)
                ));
                Ok(v)
            }
            Err(e) => {
                self.line(&format!(
                    r#"{{"t":"mc","op":"enc","f":{},"cap":{},"err":"{}"}}"#,
                    fj(f),
                    cap,
                    class(&e)
                ));
                Err(class(&e))
            }
        }
    }
}

fn rec(inc: u64, ver: u16, n: u8) -> Record {
    Record {
        inc,
        ver,
        thash: [n, 2, 3, 4, 5, 6, 7, 8],
    }
}

/// The incarnations at every limb and byte boundary.
fn incs() -> Vec<u64> {
    let mut v = vec![0, 1, 255, 256, 65_535, 65_536];
    for k in [32u32, 48, 63] {
        v.extend([(1u64 << k) - 1, 1 << k, (1u64 << k) + 1]);
    }
    v.push(u64::MAX);
    v
}

fn mid(n: u8) -> [u8; 32] {
    let mut m = [0u8; 32];
    for (i, x) in m.iter_mut().enumerate() {
        *x = n.wrapping_add(u8::try_from(i).unwrap());
    }
    m
}

fn entries(n: usize, base: u8) -> Vec<u8> {
    let mut v = Vec::new();
    for i in 0..n {
        let k = base.wrapping_add(u8::try_from(i % 200).unwrap());
        v.extend_from_slice(&entry_bytes(
            &mid(k),
            &rec(0x0102_0304_0506_0000 + i as u64, k.into(), k),
            Alive::Alive,
        ));
    }
    v
}

/// The fixed-size valid frames (their cuts and trailing bytes are all refused) as `(frame bytes without the prefix)`.
fn small_frames(out: &mut Vec<Vec<u8>>) {
    let mut buf = [0u8; 400];
    let mut add = |f: &Frame<'_>| {
        let e = f.encode(&mut buf).unwrap();
        out.push(e[4..].to_vec());
    };
    for inc in incs() {
        for ver in [0u16, 1, 255, 256, 65_535] {
            for (s, h) in [(false, false), (true, false), (false, true), (true, true)] {
                add(&Frame::Hello(Hello {
                    rec: rec(inc, ver, 1),
                    snap: s,
                    homed: h,
                }));
            }
        }
    }
    add(&Frame::Ack);
    add(&Frame::Probe);
    for a in [Alive::Down, Alive::Alive, Alive::Left] {
        for inc in [0, u64::from(u32::MAX), u64::MAX] {
            let m = mid(5);
            add(&Frame::Delta(vinc_membership::codec::Entry {
                member: &m,
                rec: rec(inc, 65_535, 3),
                alive: a,
            }));
        }
    }
    let m = mid(9);
    let paths = [Path::Session, Path::Direct, Path::Relay];
    for n in 1..=MAX_PROBES {
        for sh in 0..9usize {
            let probes: Vec<Probe> = (0..n)
                .map(|i| Probe {
                    age_ms: [0u32, 1000, u32::MAX][(sh + i) % 3],
                    path: paths[(sh / 3 + i) % 3],
                })
                .collect();
            let proof = Proof::new([0u32, 1, u32::MAX][sh % 3], &probes).unwrap();
            add(&Frame::Down(Down {
                member: &m,
                inc: [0, 1 << 40, u64::MAX][sh / 3],
                proof,
            }));
        }
    }
}

fn big_frames() -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut buf = vec![0u8; 8000];
    for n in [0usize, 1, 2, 3, 64, 65] {
        for (p, m) in [(false, false), (true, true), (false, true)] {
            let es = entries(n, 7);
            let f = Frame::Snap(Snap::new(p, m, &es).unwrap());
            out.push(f.encode(&mut buf).unwrap()[4..].to_vec());
        }
    }
    for t in [0u8, 5, 11, ty::FLOOR, 255] {
        for topic_len in [0usize, 1, 255] {
            for rest_len in [0usize, 1, 9, 300] {
                let topic = vec![7u8; topic_len];
                let rest: Vec<u8> = (0..rest_len).map(|i| u8::try_from(i % 251).unwrap()).collect();
                let f = Frame::Other(Other {
                    ty: t,
                    topic: &topic,
                    rest: &rest,
                });
                out.push(f.encode(&mut buf).unwrap()[4..].to_vec());
            }
        }
    }
    out
}

/// Run the codec part.
pub fn run(tw: &mut TraceWriter) {
    let mut r = Rec {
        tw,
        parsed_ok: 0,
        parsed_err: 0,
    };
    let mut small = Vec::new();
    small_frames(&mut small);
    let big = big_frames();
    let mut rng = SplitMix64::traced(0xC0DEC);

    // Valid frames: the body parses back, the stream read returns it with the bytes it used, every proper prefix of
    // the stream form is a partial read, and an encoding into a buffer one byte too small is refused.
    for body in small.iter().chain(big.iter()) {
        let enc = r.parse(body).expect("a valid frame parses");
        let f = Frame::parse(body).unwrap();
        let mut tail = enc.clone();
        tail.extend_from_slice(&[7, 7]);
        assert_eq!(r.read(&tail), Ok(Some(enc.len())));
        let mut ks = vec![0, 1, 2, 3, 4, 5, enc.len() / 2, enc.len() - 1];
        ks.retain(|k| *k < enc.len());
        ks.dedup();
        for k in ks {
            assert_eq!(r.read(&enc[..k]), Ok(None), "a proper prefix is a partial frame");
        }
        assert_eq!(r.encode(&f, enc.len()), Ok(enc.clone()));
        if enc.len() > 4 {
            assert!(r.encode(&f, enc.len() - 1).is_err());
        }
        assert!(r.encode(&f, 4).is_err());
    }

    // Cuts, trailing bytes and single-byte changes of the small frames.
    for (idx, body) in small.iter().enumerate() {
        // Every fourth frame gets every cut, every sixth the single-byte changes; all get a trailing byte.
        if idx % 4 == 0 || body.len() > 30 {
            for k in 0..body.len() {
                assert!(
                    r.parse(&body[..k]).is_none(),
                    "a proper cut of a fixed frame is refused"
                );
            }
        } else {
            assert!(
                r.parse(&body[..body.len() - 1]).is_none(),
                "a proper cut of a fixed frame is refused"
            );
        }
        for x in [1u8, 255] {
            let mut v = body.clone();
            v.push(x);
            assert!(r.parse(&v).is_none(), "a trailing byte is refused");
        }
        if idx % 6 == 0 {
            for i in 0..body.len() {
                for x in [0u8, 1, 2, 3, 4, 13, 255] {
                    if body[i] != x {
                        let mut v = body.clone();
                        v[i] = x;
                        let _ = r.parse(&v);
                    }
                }
            }
        }
    }
    // The big frames: cuts at the structure boundaries, trailing bytes and some changes.
    for body in &big {
        let cuts: Vec<usize> = (0..body.len().min(8)).chain((0..body.len()).step_by(51)).collect();
        for k in cuts {
            let _ = r.parse(&body[..k]);
        }
        for x in [0u8, 1, 255] {
            let mut v = body.clone();
            v.push(x);
            let _ = r.parse(&v);
        }
        for _ in 0..6 {
            let i = (rng.next_u64() as usize) % body.len();
            let mut v = body.clone();
            v[i] = rng.next_u64() as u8;
            let _ = r.parse(&v);
        }
        let mut v = body.clone();
        if v.len() > 60 {
            v.truncate(v.len() - 1);
            let _ = r.parse(&v);
        }
    }

    // Malformed classes by name.
    let hello = &small[0];
    for fl in [4u8, 5, 128, 255] {
        let mut v = hello.clone();
        *v.last_mut().unwrap() = fl;
        assert!(r.parse(&v).is_none());
    }
    let snap2 = {
        let es = entries(2, 3);
        Frame::Snap(Snap::new(false, false, &es).unwrap())
            .encode(&mut [0u8; 400])
            .unwrap()[4..]
            .to_vec()
    };
    for fl in [4u8, 7, 128, 255] {
        let mut v = snap2.clone();
        v[2] = fl;
        assert!(r.parse(&v).is_none());
    }
    for a in [0u8, 2, 3, 255] {
        let mut v = snap2.clone();
        let n = v.len();
        v[n - 1] = a;
        assert!(r.parse(&v).is_none());
        let mut w = snap2.clone();
        w[3 + ENTRY_LEN - 1] = a;
        assert!(r.parse(&w).is_none());
    }
    let mut v = snap2.clone();
    v.extend_from_slice(&[1; ENTRY_LEN - 1]);
    assert!(r.parse(&v).is_none());
    for t in [ty::HELLO, ty::ACK, ty::DELTA, ty::SNAP, ty::PROBE, ty::DOWN] {
        for topic_len in [1usize, 3] {
            let mut v = vec![t, u8::try_from(topic_len).unwrap()];
            v.extend(std::iter::repeat_n(9u8, topic_len));
            v.extend_from_slice(&small[0][2..]);
            assert!(r.parse(&v).is_none());
        }
    }
    let down = small.iter().find(|b| b[0] == ty::DOWN).unwrap().clone();
    for c in [0u8, 5, 255] {
        let mut v = down.clone();
        v[2 + 45 - 1] = c;
        assert!(r.parse(&v).is_none());
    }
    let mut v = down.clone();
    v[2 + 45 + 4] = 3;
    assert!(r.parse(&v).is_none());

    // Streams of several frames with a partial tail, read to the end.
    let mut stream = Vec::new();
    for body in small.iter().step_by(37).chain(big.iter().step_by(5)) {
        stream.extend_from_slice(&u32::try_from(body.len()).unwrap().to_be_bytes());
        stream.extend_from_slice(body);
    }
    stream.extend_from_slice(&[0, 0, 0, 30, 1]);
    let mut at = 0;
    let mut frames = 0;
    loop {
        match r.read(&stream[at..]) {
            Ok(Some(n)) => {
                at += n;
                frames += 1;
            }
            Ok(None) => break,
            Err(e) => panic!("stream read refused: {e}"),
        }
    }
    assert!(frames > 10 && at < stream.len());

    // A prefix that names a body above the limit is refused with or without the body, a body at the limit is partial.
    for len in [
        MAX_BODY as u32 + 1,
        MAX_BODY as u32 + 2,
        5 << 16,
        30_000 << 16,
        u32::MAX,
    ] {
        let mut v = len.to_be_bytes().to_vec();
        assert_eq!(r.read(&v), Err("tooLarge"));
        v.extend_from_slice(&[ty::PROBE, 0]);
        assert_eq!(r.read(&v), Err("tooLarge"));
    }
    assert_eq!(r.read(&(MAX_BODY as u32).to_be_bytes()), Ok(None));
    for n in 0..4 {
        assert_eq!(r.read(&[0, 0, 0][..n.min(3)]), Ok(None));
    }

    // Encoding errors: a topic of 256 bytes, a buffer too small for the prefix, a body above the limit (not recorded
    // as a line: the frame is 262 kB).
    let topic = vec![1u8; 256];
    let f = Frame::Other(Other {
        ty: 99,
        topic: &topic,
        rest: &[],
    });
    assert_eq!(r.encode(&f, 400), Err("topicLong"));
    assert_eq!(r.encode(&f, 4), Err("bufferSmall"));
    let big_rest = vec![0u8; MAX_BODY - 1];
    let f = Frame::Other(Other {
        ty: 99,
        topic: &[],
        rest: &big_rest,
    });
    assert_eq!(
        f.encode(&mut vec![0u8; MAX_BODY + 8]).unwrap_err(),
        FrameError::TooLarge
    );
    for cap in 0..6 {
        assert_eq!(r.encode(&Frame::Ack, cap).is_err(), cap < 6);
    }

    // Seeded garbage: random bytes with a biased header.
    for _ in 0..4000 {
        let n = (rng.next_u64() % 90) as usize;
        let mut v: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
        if n >= 2 && !rng.next_u64().is_multiple_of(4) {
            v[0] = [1u8, 2, 3, 4, 12, 13, 14, 0, 77][(rng.next_u64() % 9) as usize];
            if !rng.next_u64().is_multiple_of(3) {
                v[1] = 0;
            }
        }
        let _ = r.parse(&v);
    }
    // Garbage streams.
    for _ in 0..300 {
        let n = (rng.next_u64() % 40) as usize;
        let mut v: Vec<u8> = (0..n).map(|_| rng.next_u64() as u8).collect();
        if n >= 4 && !rng.next_u64().is_multiple_of(3) {
            v[0] = 0;
            v[1] = 0;
            v[2] = 0;
            v[3] = (rng.next_u64() % 40) as u8;
        }
        let _ = r.read(&v);
    }
    assert!(
        r.parsed_ok > 200 && r.parsed_err > 1000,
        "{} ok, {} refused",
        r.parsed_ok,
        r.parsed_err
    );
}
