//! Trace generation for the key templates of the TPM store against a software TPM (`swtpm`): the TPM2B_PUBLIC (the
//! `inPublic` of the template) that the client sends in every `CreatePrimary` and `Create` command, cut off the bytes
//! of the command, recorded as ndjson (`keystore_template.ndjson`) for the TLA+ trace check
//! (`TraceKeystoreTemplate.tla`).
//!
//! The templates are private to the client, so the test reads them off the wire: a recording transport keeps every
//! command, and after each store call (`open`, `generate`, `seal`) the commands sent since the last call are cut. An
//! event carries the bytes and whether the `tpm2-protocol` library reads exactly that many bytes as a `Tpm2bPublic`.
//! The three pairs of auth values and the repeated calls show that the bytes depend on neither.
//!
//! The test asserts, without the model: the library reads every template whole, the bytes of each kind are the
//! same in every event, the three kinds differ, each kind occurs (2 `sign` and 3 `seal` per store) and the size
//! prefix is the length of the rest. The trace is written to the directory in `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![cfg(feature = "hwenc")]
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::doc_markdown
)]

use std::fmt::Write as _;
use std::io;
use std::sync::{Arc, Mutex};

use pinc_crypto::IdentityAlg;
use pinc_keystore::tpm::{SimTransport, Transport};
use pinc_keystore::{KeyStore, TpmConfig, TpmStore};
use pinc_tests::Swtpm;
use tpm2_protocol::TpmUnmarshal;
use tpm2_protocol::data::Tpm2bPublic;

const CREATE_PRIMARY: u32 = 0x131;
const CREATE: u32 = 0x153;

fn arr(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

fn be16(b: &[u8]) -> usize {
    usize::from(u16::from_be_bytes(b[..2].try_into().unwrap()))
}

fn be32(b: &[u8]) -> u32 {
    u32::from_be_bytes(b[..4].try_into().unwrap())
}

/// A transport that keeps a copy of every command.
struct Recorder<T: Transport> {
    inner: T,
    cmds: Arc<Mutex<Vec<Vec<u8>>>>,
}

impl<T: Transport> Transport for Recorder<T> {
    fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>> {
        self.cmds.lock().unwrap().push(command.to_vec());
        self.inner.transmit(command)
    }
}

/// One template cut out of a command.
struct Template {
    kind: &'static str,
    cc: u32,
    op: &'static str,
    b: Vec<u8>,
    lib: bool,
}

#[derive(Default)]
struct Run {
    out: String,
    events: Vec<Template>,
    cursor: usize,
}

impl Run {
    /// The templates in the commands sent since the last call, which was `op`.
    fn cut(&mut self, cmds: &Mutex<Vec<Vec<u8>>>, op: &'static str) {
        let cmds = cmds.lock().unwrap();
        for cmd in &cmds[self.cursor..] {
            let cc = be32(&cmd[6..10]);
            if cc != CREATE_PRIMARY && cc != CREATE {
                continue;
            }
            assert_eq!(
                be16(&cmd[0..2]),
                0x8002,
                "a template command without an authorization area"
            );
            let p = 18 + be32(&cmd[14..18]) as usize;
            let q = p + 2 + be16(&cmd[p..]);
            let len = 2 + be16(&cmd[q..]);
            assert!(q + len <= cmd.len(), "a template that runs past its command");
            let b = cmd[q..q + len].to_vec();
            let lib = Tpm2bPublic::unmarshal(&cmd[q..]).is_ok_and(|(_, rest)| cmd.len() - q - rest.len() == len);
            let kind = match (cc, op) {
                (CREATE_PRIMARY, _) => "storage",
                (_, "generate") => "sign",
                (_, "seal") => "seal",
                _ => op,
            };
            writeln!(
                self.out,
                r#"{{"t":"ktpl","kind":"{kind}","cc":{cc},"op":"{op}","b":{},"lib":{}}}"#,
                arr(&b),
                u8::from(lib)
            )
            .unwrap();
            self.events.push(Template { kind, cc, op, b, lib });
        }
        self.cursor = cmds.len();
    }
}

#[test]
fn keystore_template_traces() {
    let tpm = Swtpm::start();
    let cmds = Arc::new(Mutex::new(Vec::new()));
    let mut run = Run::default();
    for (owner, key) in [(&b""[..], &b""[..]), (b"", b"key-auth"), (b"", &[9u8; 32][..])] {
        let sim = SimTransport::connect(("127.0.0.1", tpm.port)).unwrap();
        let mut store = TpmStore::open(
            Recorder {
                inner: sim,
                cmds: Arc::clone(&cmds),
            },
            TpmConfig::new().owner_auth(owner).key_auth(key),
        )
        .unwrap();
        run.cut(&cmds, "open");
        // Sealing first: TPM2_Create needs a free object slot, and the primary with two loaded keys fills all three.
        for pt in [&b"sealed by the tpm"[..], b"sealed by the tpm", &[0u8; 32][..]] {
            store.seal(pt).unwrap();
            run.cut(&cmds, "seal");
        }
        for _ in 0..2 {
            store.generate(IdentityAlg::EcdsaP256).unwrap();
            run.cut(&cmds, "generate");
        }
    }

    let count = |kind: &str| run.events.iter().filter(|e| e.kind == kind).count();
    assert!(
        run.events.iter().all(|e| e.lib),
        "the library did not read a template whole"
    );
    assert_eq!(count("sign"), 6, "two sign templates per store");
    assert_eq!(count("seal"), 9, "three seal templates per store");
    assert!(count("storage") >= 3, "no storage template per store");
    let first = |kind: &str| run.events.iter().find(|e| e.kind == kind).map(|e| e.b.clone()).unwrap();
    for e in &run.events {
        assert_eq!(e.b, first(e.kind), "the {} template changed between calls", e.kind);
        assert_eq!(
            be16(&e.b),
            e.b.len() - 2,
            "the size prefix is not the length of the rest"
        );
        assert!(matches!(e.cc, CREATE_PRIMARY | CREATE));
        assert!(matches!(e.op, "open" | "generate" | "seal"));
    }
    let (s, g, e) = (first("storage"), first("sign"), first("seal"));
    assert!(s != g && g != e && s != e, "two kinds share a template");

    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("keystore_template.ndjson"), run.out).unwrap();
    }
}
