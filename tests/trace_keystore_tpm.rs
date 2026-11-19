//! Trace generation for the TPM store against a software TPM (`swtpm`): the bytes of every command the client sends and
//! of every response it reads, the program of commands each store operation runs, the handles the TPM holds after it,
//! the sealed blob and every error of `unseal`, recorded as ndjson (`keystore_tpm.ndjson`) for the TLA+ trace check
//! (`TraceKeystore.tla`) and the Lean replay (`Pinc.TraceKeystore`).
//!
//! A recording transport wraps the TPM link and logs every command with its response and keeps the set of transient
//! handles the TPM holds (a handle is added by a successful `CreatePrimary` or `Load` and removed by a successful
//! `FlushContext`). Events (`t = "kt"`):
//! * `resp`: a canned response (or a link failure) read by `get_random`, with the verdict of the `tpm2-protocol` library
//!   on its body and the error the client reported;
//! * `prog`: one store operation: the commands (bytes of command and response), the auth values in force, the handles
//!   held before and after, the entries the store tracks, and the result;
//! * `seal`, `unseal`: sealed blobs and what `unseal` does with genuine, altered, cut and foreign blobs, with the commands
//!   it sent and the library's verdict on the header;
//! * `hnd`, `auth`: the refusals that send no command (a handle outside the persistent range, a key already
//!   persistent, an auth value over 64 bytes).
//!
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![cfg(feature = "hwenc")]
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::collections::HashSet;
use std::fmt::Write as _;
use std::io;
use std::sync::{Arc, Mutex};

use tpm2_protocol::TpmUnmarshal;
use tpm2_protocol::data::{Tpm2bPrivate, Tpm2bPublic};
use tpm2_protocol::frame::{TpmGetRandomResponse, TpmResponse};
use pinc_crypto::IdentityAlg;
use pinc_keystore::tpm::{SimTransport, TpmClient, Transport};
use pinc_keystore::{KeyHandle, KeyStore, KeyStoreError, TpmConfig, TpmStore};
use pinc_tests::Swtpm;

fn arr(b: &[u8]) -> String {
    format!("[{}]", b.iter().map(u8::to_string).collect::<Vec<_>>().join(","))
}

fn be32(b: &[u8]) -> u32 {
    u32::from_be_bytes(b[..4].try_into().unwrap())
}

/// A command and its response.
type Exchange = (Vec<u8>, Vec<u8>);

#[derive(Default)]
struct Log {
    cmds: Vec<Exchange>,
    live: HashSet<u32>,
}

/// A transport that logs every exchange and tracks the transient handles.
struct Recorder<T: Transport> {
    inner: T,
    log: Arc<Mutex<Log>>,
}

impl<T: Transport> Transport for Recorder<T> {
    fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>> {
        let rsp = self.inner.transmit(command)?;
        let mut log = self.log.lock().unwrap();
        let cc = be32(&command[6..10]);
        let rc = be32(&rsp[6..10]);
        if rc == 0 {
            match cc {
                0x131 | 0x157 => {
                    log.live.insert(be32(&rsp[10..14]));
                }
                0x165 => {
                    log.live.remove(&be32(&command[10..14]));
                }
                _ => {}
            }
        }
        log.cmds.push((command.to_vec(), rsp.clone()));
        Ok(rsp)
    }
}

/// A link that answers with canned responses, or fails.
struct Script(Vec<Result<Vec<u8>, io::ErrorKind>>);

impl Transport for Script {
    fn transmit(&mut self, _command: &[u8]) -> io::Result<Vec<u8>> {
        match self.0.pop() {
            Some(Ok(r)) => Ok(r),
            Some(Err(k)) => Err(k.into()),
            None => Err(io::ErrorKind::UnexpectedEof.into()),
        }
    }
}

/// The TPM response code of an error as two 16-bit limbs (most significant first), or zeros.
fn code_of<T>(r: &Result<T, KeyStoreError>) -> String {
    match r {
        Err(KeyStoreError::Tpm { code }) => format!("[{},{}]", code >> 16, code & 0xffff),
        _ => "[0,0]".into(),
    }
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn describe(e: &KeyStoreError) -> String {
    match e {
        KeyStoreError::Tpm { .. } => "Tpm".to_string(),
        KeyStoreError::Transport(_) => "Transport".to_string(),
        other => format!("{other:?}"),
    }
}

/// A result as a name and, for a TPM refusal, a trailing code field kept apart.
fn res_of<T>(r: &Result<T, KeyStoreError>) -> String {
    match r {
        Ok(_) => "ok".into(),
        Err(KeyStoreError::Tpm { code }) => {
            format!("Tpm#{}", [code >> 16, code & 0xffff].map(|x| x.to_string()).join(","))
        }
        Err(e) => describe(e),
    }
}

/// Split `Tpm#hi,lo` into the name and the limbs field.
fn split_res(res: &str) -> (String, String) {
    match res.split_once('#') {
        Some((name, limbs)) => (name.to_string(), format!("[{limbs}]")),
        None => (res.to_string(), "[0,0]".to_string()),
    }
}

struct Run {
    log: Arc<Mutex<Log>>,
    out: String,
    /// The entries the store tracks: the primary and the keys that are not persistent.
    slots: i64,
}

impl Run {
    /// Take the commands logged since the last call, as events fields.
    fn take(&mut self) -> (Vec<Exchange>, usize) {
        let mut log = self.log.lock().unwrap();
        (std::mem::take(&mut log.cmds), log.live.len())
    }

    fn cmds_json(cmds: &[Exchange]) -> String {
        cmds.iter()
            .map(|(c, r)| format!(r#"{{"cmd":{},"rsp":{}}}"#, arr(c), arr(r)))
            .collect::<Vec<_>>()
            .join(",")
    }

    #[allow(clippy::too_many_arguments)]
    fn prog(&mut self, op: &str, n: usize, owner: &[u8], key: &[u8], before: usize, res: &str, slots_delta: i64) {
        let (res, code) = split_res(res);
        let (cmds, after) = self.take();
        self.slots += slots_delta;
        let _ = writeln!(
            self.out,
            r#"{{"t":"kt","op":"prog","prog":"{op}","n":{n},"owner":{},"key":{},"live_before":{before},"live_after":{after},"slots":{},"res":"{res}","code":{code},"cmds":[{}]}}"#,
            arr(owner),
            arr(key),
            self.slots,
            Self::cmds_json(&cmds)
        );
        assert_eq!(
            i64::try_from(after).unwrap(),
            self.slots,
            "the TPM holds exactly the handles the store tracks"
        );
    }

    fn live(&self) -> usize {
        self.log.lock().unwrap().live.len()
    }
}

fn resp_trace(out: &mut String) {
    let mut valid = vec![0x80, 0x01, 0, 0, 0, 20, 0, 0, 0, 0, 0, 8];
    valid.extend_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
    let mut cases: Vec<Result<Vec<u8>, io::ErrorKind>> = vec![
        Ok(vec![]),
        Ok(vec![0x80, 0x01, 0, 0, 0, 10, 0, 0, 0]),
        Ok(vec![0x80, 0x01, 0, 0, 0, 10, 0, 0, 0, 0]),
        Ok(valid.clone()),
    ];
    let mut trailing = valid.clone();
    trailing.push(9);
    cases.push(Ok(trailing.clone()));
    trailing[5] = 21;
    cases.push(Ok(trailing));
    for delta in [-1i32, 1] {
        let mut v = valid.clone();
        v[5] = u8::try_from(20 + delta).unwrap();
        cases.push(Ok(v));
    }
    for code in [0x100u32, 0x1D, 0x98E, 0xFFFF_FFFF] {
        let mut v = vec![0x80, 0x01, 0, 0, 0, 10];
        v.extend_from_slice(&code.to_be_bytes());
        cases.push(Ok(v.clone()));
        v[5] = 11;
        v.push(0);
        cases.push(Ok(v.clone()));
        v[5] = 9;
        cases.push(Ok(v));
    }
    let mut bad_body = valid.clone();
    bad_body[11] = 200;
    cases.push(Ok(bad_body));
    cases.push(Err(io::ErrorKind::ConnectionReset));
    cases.push(Err(io::ErrorKind::TimedOut));
    for case in cases {
        let (rsp, link) = match &case {
            Ok(r) => (r.clone(), String::new()),
            Err(k) => (vec![], format!("{k:?}")),
        };
        let body_ok = TpmResponse::cast(&rsp)
            .and_then(TpmResponse::unmarshal::<TpmGetRandomResponse>)
            .is_ok();
        let mut client = TpmClient::new(Script(vec![case]));
        let r = client.get_random(16);
        let r = r.map(|_| ());
        let (res, code) = (split_res(&res_of(&r)).0, code_of(&r));
        let _ = writeln!(
            out,
            r#"{{"t":"kt","op":"resp","rsp":{},"link":"{link}","body_ok":{body_ok},"res":"{res}","code":{code}}}"#,
            arr(&rsp)
        );
    }
}

fn config(owner: &[u8], key: &[u8]) -> TpmConfig {
    TpmConfig::new().owner_auth(owner).key_auth(key)
}

fn open(tpm: &Swtpm, run: &mut Run, owner: &[u8], key: &[u8]) -> TpmStore<Recorder<SimTransport>> {
    let sim = SimTransport::connect(("127.0.0.1", tpm.port)).unwrap();
    let before = run.live();
    let store = TpmStore::open(
        Recorder {
            inner: sim,
            log: Arc::clone(&run.log),
        },
        config(owner, key),
    )
    .unwrap();
    run.prog("open", 0, owner, key, before, "ok", 1);
    store
}

/// A list of the commands sent since the last event, with the result of the operation just done.
fn programs(tpm: &Swtpm, run: &mut Run) {
    for (owner, key) in [(&b""[..], &b""[..]), (b"", b"key-auth"), (b"", &[9u8; 32][..])] {
        let mut store = open(tpm, run, owner, key);
        let mut b = run.live();
        // random: from none to several calls
        for n in [0usize, 1, 31, 32, 33, 64, 100] {
            let mut buf = vec![0u8; n];
            let r = store.random(&mut buf);
            run.prog("random", n, owner, key, b, &res_of(&r), 0);
            b = run.live();
        }
        // a key: created, loaded and read
        let k: KeyHandle = store.generate(IdentityAlg::EcdsaP256).unwrap();
        run.prog("generate", 0, owner, key, b, "ok", 1);
        b = run.live();
        let r = store.sign(&k, b"message");
        run.prog("sign", 0, owner, key, b, &res_of(&r), 0);
        b = run.live();
        // not a P-256 key: refused before any command
        let r = store.generate(IdentityAlg::Ed25519);
        run.prog("generate_unsupported", 0, owner, key, b, &res_of(&r), 0);
        // a persistent handle outside the range, and inside it
        for h in [0u32, 0x80FF_FFFF, 0x8200_0000, 0xFFFF_FFFF, 0x0100_0000] {
            let r = store.persist(&k, h);
            let (cmds, _) = run.take();
            let _ = writeln!(
                run.out,
                r#"{{"t":"kt","op":"hnd","call":"persist","h":[{},{}],"res":"{}","ncmds":{}}}"#,
                h >> 16,
                h & 0xffff,
                split_res(&res_of(&r)).0,
                cmds.len()
            );
            let r = store.load_persistent(h);
            let (cmds, _) = run.take();
            let _ = writeln!(
                run.out,
                r#"{{"t":"kt","op":"hnd","call":"load","h":[{},{}],"res":"{}","ncmds":{}}}"#,
                h >> 16,
                h & 0xffff,
                split_res(&res_of(&r)).0,
                cmds.len()
            );
        }
        b = run.live();
        let at = 0x8101_0000 + u32::from(key.len() as u8);
        let r = store.persist(&k, at);
        run.prog("persist", 0, owner, key, b, &res_of(&r), -1);
        b = run.live();
        // a second persist of a persistent key is refused before any command
        let r = store.persist(&k, at + 0x100);
        let (cmds, _) = run.take();
        let _ = writeln!(
            run.out,
            r#"{{"t":"kt","op":"hnd","call":"persist_again","h":[{},{}],"res":"{}","ncmds":{}}}"#,
            (at + 0x100) >> 16,
            (at + 0x100) & 0xffff,
            split_res(&res_of(&r)).0,
            cmds.len()
        );
        // another key cannot take a taken handle: the TPM refuses
        let k2 = store.generate(IdentityAlg::EcdsaP256).unwrap();
        run.prog("generate", 0, owner, key, b, "ok", 1);
        b = run.live();
        let r = store.persist(&k2, at);
        run.prog("persist", 0, owner, key, b, &res_of(&r), 0);
        b = run.live();
        // an empty persistent handle
        let r = store.load_persistent(0x8100_0099);
        run.prog("load_persistent", 0, owner, key, b, &res_of(&r), 0);
        b = run.live();
        let r = store.load_persistent(at);
        run.prog("load_persistent", 0, owner, key, b, &res_of(&r), 0);
        b = run.live();
        sealed(&mut store, run, owner, key);
        let _ = b;
        drop(store);
        // dropping flushes every transient handle and the primary
        let (_, after) = run.take();
        assert_eq!(after, 0, "dropping the store leaves a transient handle in the TPM");
        run.slots = 0;
        let _ = writeln!(run.out, r#"{{"t":"kt","op":"dropped","live_after":{after}}}"#);
    }
}

/// A TPM2B: the library's verdict on a sealed header, and the bytes it consumed.
fn header_verdict(blob: &[u8]) -> (bool, usize) {
    let Some((&version, body)) = blob.split_first() else {
        return (false, 0);
    };
    if version != 2 {
        return (false, 0);
    }
    let Ok((_, after_private)) = Tpm2bPrivate::unmarshal(body) else {
        return (false, 0);
    };
    let Ok((_, after_public)) = Tpm2bPublic::unmarshal(after_private) else {
        return (false, 0);
    };
    let private_len = body.len() - after_private.len();
    let public_len = after_private.len() - after_public.len();
    (true, 1 + private_len + public_len)
}

fn sealed(store: &mut TpmStore<Recorder<SimTransport>>, run: &mut Run, owner: &[u8], key: &[u8]) {
    let mut b = run.live();
    let pt = b"sealed by the tpm".to_vec();
    let blob = store.seal(&pt).unwrap();
    run.prog("seal", pt.len(), owner, key, b, "ok", 0);
    let (lib_ok, hdr) = header_verdict(&blob);
    assert!(lib_ok);
    assert_eq!(blob.len(), hdr + 12 + pt.len() + 16);
    let _ = writeln!(
        run.out,
        r#"{{"t":"kt","op":"seal","pt":{},"blob":{},"lib_ok":{lib_ok},"hdr":{hdr}}}"#,
        arr(&pt),
        arr(&blob)
    );
    let mut variants: Vec<Vec<u8>> = vec![blob.clone()];
    let positions = [
        0usize,
        1,
        2,
        3,
        10,
        hdr / 2,
        hdr - 1,
        hdr,
        hdr + 5,
        hdr + 11,
        hdr + 12,
        hdr + 14,
        blob.len() - 17,
        blob.len() - 16,
        blob.len() - 1,
    ];
    for &i in &positions {
        let mut v = blob.clone();
        v[i] ^= 0x01;
        variants.push(v);
    }
    for cut in [
        0usize,
        1,
        2,
        3,
        hdr / 2,
        hdr,
        hdr + 11,
        hdr + 12,
        blob.len() - 17,
        blob.len() - 1,
    ] {
        variants.push(blob[..cut].to_vec());
    }
    let mut longer = blob.clone();
    longer.push(0);
    variants.push(longer);
    for v in [0u8, 1, 3, 255] {
        let mut w = blob.clone();
        w[0] = v;
        variants.push(w);
    }
    variants.push(blob.clone());
    for v in variants {
        b = run.live();
        let (lib_ok, hdr_lib) = header_verdict(&v);
        let r = store.unseal(&v);
        let (rname, rcode) = split_res(&res_of(&r));
        let genuine = v == blob;
        let (cmds, after) = run.take();
        let _ = writeln!(
            run.out,
            r#"{{"t":"kt","op":"unseal","owner":{},"key":{},"blob":{},"genuine":{genuine},"lib_ok":{lib_ok},"hdr":{hdr_lib},"live_before":{b},"live_after":{after},"res":"{rname}","code":{rcode},"cmds":[{}]}}"#,
            arr(owner),
            arr(key),
            arr(&v),
            Run::cmds_json(&cmds)
        );
        assert_eq!(after, b, "an unseal leaves no handle behind");
        if genuine {
            assert_eq!(r.unwrap().as_slice(), pt.as_slice());
        }
    }
}

fn auth_trace(tpm: &Swtpm, run: &mut Run) {
    for len in [0usize, 63, 64, 65, 100] {
        let owner = vec![3u8; len];
        let sim = SimTransport::connect(("127.0.0.1", tpm.port)).unwrap();
        let before = run.log.lock().unwrap().cmds.len();
        let r = TpmStore::open(
            Recorder {
                inner: sim,
                log: Arc::clone(&run.log),
            },
            config(&owner, b""),
        );
        let ncmds = run.log.lock().unwrap().cmds.len() - before;
        let res = match &r {
            Ok(_) => "ok".to_string(),
            Err(e) => describe(e),
        };
        let _ = writeln!(
            run.out,
            r#"{{"t":"kt","op":"auth","len":{len},"res":"{res}","ncmds":{ncmds}}}"#
        );
        drop(r);
        run.take();
    }
    run.slots = 0;
}

#[test]
fn keystore_tpm_traces() {
    let tpm = Swtpm::start();
    let mut run = Run {
        log: Arc::new(Mutex::new(Log::default())),
        out: String::new(),
        slots: 0,
    };
    resp_trace(&mut run.out);
    programs(&tpm, &mut run);
    auth_trace(&tpm, &mut run);
    assert!(run.out.lines().count() > 100);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("keystore_tpm.ndjson"), run.out).unwrap();
    }
}
