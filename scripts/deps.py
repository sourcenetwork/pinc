#!/usr/bin/env python3
"""Dependency rules, checked by the gate.

1. Every dependency of every workspace member is declared once, in the root `[workspace.dependencies]`; a member
   manifest may only say `{ workspace = true }` (plus features or `optional`).
2. Every member has the one workspace version (`version.workspace = true`), and every VINC crate entry in
   `[workspace.dependencies]` pins that same version.
3. Every library crate under `crates/` forbids unsafe code in its root (`#![forbid(unsafe_code)]`); the workspace lint is only `deny` so the test allocator can allow it.
4. No library crate under `crates/` depends, directly or transitively, on an async runtime. The facade takes the host's
   I/O as three async closures, so it needs none; nuclei, the runtime its documentation and examples run on, is a
   dev-dependency of `vinc` only. The tests and benches may use nuclei, tokio and smol; every other member refuses all
   of them, as a dependency of any kind.
5. Pure Rust: no crate that compiles or links C (crypto or otherwise) is anywhere in the workspace graph.
6. No QUIC library in VINC: no member except the comparison harness (`vinc-benches`, which measures iroh and
   rust-libp2p, both built on QUIC stacks) may depend, directly or transitively, on a QUIC implementation.
"""
import json
import subprocess
import sys
import tomllib

RUNTIMES = {"tokio", "async-std", "smol", "async-executor", "glommio", "monoio", "embassy-executor", "nuclei"}
# The runtimes each member may depend on directly; the facade only as a dev-dependency (its docs and examples).
RUNTIME_HOMES = {"vinc": {"nuclei"}, "vinc-tests": {"nuclei", "tokio", "smol"}, "vinc-benches": {"nuclei", "tokio", "smol"}}
DEV_ONLY = {"vinc"}
SECTIONS = ("dependencies", "dev-dependencies", "build-dependencies")

try:
    meta = json.loads(subprocess.check_output(["cargo", "-q", "metadata", "--format-version", "1", "--all-features"]))
except subprocess.CalledProcessError:
    sys.exit("deps: cargo could not resolve the workspace; fix the error above (a version mismatch between members fails here)")
members = set(meta["workspace_members"])
failed = []
for pkg in meta["packages"]:
    if pkg["id"] not in members:
        continue
    manifest = tomllib.load(open(pkg["manifest_path"], "rb"))
    tables = [manifest.get(s, {}) for s in SECTIONS]
    tables += [t.get(s, {}) for t in manifest.get("target", {}).values() for s in SECTIONS]
    for table in tables:
        for name, spec in table.items():
            if not (isinstance(spec, dict) and spec.get("workspace") is True):
                failed.append(f"{pkg['name']}: dependency `{name}` must be `{{ workspace = true }}`; declare it in the root Cargo.toml")

for pkg in meta["packages"]:
    if pkg["id"] not in members:
        continue
    for dep in pkg["dependencies"]:
        if dep["name"] not in RUNTIMES:
            continue
        if dep["name"] not in RUNTIME_HOMES.get(pkg["name"], set()):
            failed.append(f"{pkg['name']}: depends on the runtime {dep['name']}; only the tests and benches (and the facade's dev-dependency nuclei) may")
        elif dep["kind"] != "dev" and pkg["name"] in DEV_ONLY:
            failed.append(f"{pkg['name']}: the runtime {dep['name']} must be a dev-dependency here; the facade takes the host's I/O as closures")

root = tomllib.load(open(meta["workspace_root"] + "/Cargo.toml", "rb"))["workspace"]
version = root["package"]["version"]
member_names = {p["name"] for p in meta["packages"] if p["id"] in members}
for pkg in meta["packages"]:
    if pkg["id"] in members:
        manifest = tomllib.load(open(pkg["manifest_path"], "rb"))
        if manifest["package"].get("version") != {"workspace": True}:
            failed.append(f"{pkg['name']}: must use `version.workspace = true`")
for name, spec in root.get("dependencies", {}).items():
    if name in member_names and (not isinstance(spec, dict) or spec.get("version") != version):
        failed.append(f"workspace dependency `{name}` must pin the workspace version {version}")

for pkg in meta["packages"]:
    if pkg["id"] in members and "/crates/" in pkg["manifest_path"]:
        lib = pkg["manifest_path"].removesuffix("Cargo.toml") + "src/lib.rs"
        if "#![forbid(unsafe_code)]" not in open(lib).read():
            failed.append(f"{pkg['name']}: {lib} must contain `#![forbid(unsafe_code)]`")

nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
names = {p["id"]: p["name"] for p in meta["packages"]}
for pkg in meta["packages"]:
    if pkg["id"] not in members or "/crates/" not in pkg["manifest_path"]:
        continue
    seen, stack = set(), [pkg["id"]]
    while stack:
        node = nodes[stack.pop()]
        for dep in node["deps"]:
            if any(k["kind"] in (None, "build") for k in dep["dep_kinds"]) and dep["pkg"] not in seen:
                seen.add(dep["pkg"])
                stack.append(dep["pkg"])
    bad = sorted(names[d] for d in seen if names[d] in RUNTIMES)
    if bad:
        failed.append(f"{pkg['name']}: depends on an async runtime ({', '.join(bad)}); VINC crates must stay runtime-free")

C_CRATES = {"alloca", "openssl", "openssl-sys", "ring", "aws-lc-rs", "aws-lc-sys", "tss-esapi", "tss-esapi-sys", "cryptoki",
            "cryptoki-sys", "libsodium-sys", "pqcrypto", "pqcrypto-internals"} | {n for n in names.values() if n.startswith("libcrux")}
bad = sorted({n for n in names.values() if n in C_CRATES})
if bad:
    failed.append(f"pure Rust: crates that compile or link C are in the graph: {', '.join(bad)}")

QUIC = {"quinn", "quinn-proto", "quinn-udp", "quiche", "s2n-quic", "s2n-quic-core", "noq", "noq-proto", "noq-udp",
        "msquic", "neqo-transport", "neqo-crypto", "tquic", "lsquic", "quic-rpc", "iroh-quinn", "iroh-quinn-proto",
        "libp2p-quic", "h3", "h3-quinn", "quicly", "ngtcp2", "ngtcp2-sys"}
COMPARISON = {"vinc-benches"}
for pkg in meta["packages"]:
    if pkg["id"] not in members or pkg["name"] in COMPARISON:
        continue
    seen, stack = set(), [pkg["id"]]
    while stack:
        node = nodes[stack.pop()]
        for dep in node["deps"]:
            if dep["pkg"] not in seen:
                seen.add(dep["pkg"])
                stack.append(dep["pkg"])
    bad = sorted(names[d] for d in seen if names[d] in QUIC)
    if bad:
        failed.append(f"{pkg['name']}: depends on a QUIC library ({', '.join(bad)}); VINC uses no QUIC implementation")

for line in failed:
    print(line, file=sys.stderr)
sys.exit(1 if failed else 0)
