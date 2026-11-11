#!/usr/bin/env python3
"""Dependency rules, checked by the gate, over the three workspaces of the repository: the library (the root
manifest), the benchmarks (`benches/`) and the distributed harness (`distributed/`).

1. Every dependency of every member is declared once, in its workspace's root `[workspace.dependencies]`; a member
   manifest may only say `{ workspace = true }` (plus features or `optional`).
2. Every member has its workspace's version (`version.workspace = true`), every workspace has the library's version,
   and every VINC crate entry in any `[workspace.dependencies]` pins that same version.
3. Every library crate under `crates/` forbids unsafe code in its root (`#![forbid(unsafe_code)]`); the workspace lint
   is only `deny` so the test allocator can allow it.
4. No library crate under `crates/` depends, directly or transitively, on an async runtime. The facade takes the host's
   I/O as three async closures, so it needs none; nuclei, the runtime its documentation and examples run on, is a
   dev-dependency of `vinc` only. The tests may use nuclei, tokio and smol; every other member of the library's
   workspace refuses all of them, as a dependency of any kind.
5. Pure Rust: no crate that compiles or links C (crypto or otherwise) is anywhere in the library's workspace.
6. No QUIC library in VINC: no member of the library's workspace depends, directly or transitively, on a QUIC
   implementation.

The benchmarks and the distributed harness measure VINC against iroh and rust-libp2p, so rules 4 to 6 do not apply to
them: those libraries, their runtimes and their C code live there and nowhere else, which is why each is a workspace of
its own with its own lockfile.
"""
import json
import os
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# The library's workspace first: the version every other workspace must carry is read from it.
WORKSPACES = [".", "benches", "distributed"]

RUNTIMES = {"tokio", "async-std", "smol", "async-executor", "glommio", "monoio", "embassy-executor", "nuclei"}
# The runtimes each member of the library's workspace may depend on directly; the facade only as a dev-dependency.
RUNTIME_HOMES = {"vinc": {"nuclei"}, "vinc-tests": {"nuclei", "tokio", "smol"}}
DEV_ONLY = {"vinc"}
SECTIONS = ("dependencies", "dev-dependencies", "build-dependencies")
QUIC = {"quinn", "quinn-proto", "quinn-udp", "quiche", "s2n-quic", "s2n-quic-core", "noq", "noq-proto", "noq-udp",
        "msquic", "neqo-transport", "neqo-crypto", "tquic", "lsquic", "quic-rpc", "iroh-quinn", "iroh-quinn-proto",
        "libp2p-quic", "h3", "h3-quinn", "quicly", "ngtcp2", "ngtcp2-sys"}
C_CRATES = {"alloca", "openssl", "openssl-sys", "ring", "aws-lc-rs", "aws-lc-sys", "tss-esapi", "tss-esapi-sys", "cryptoki",
            "cryptoki-sys", "libsodium-sys", "pqcrypto", "pqcrypto-internals"}

failed = []


def metadata(ws):
    manifest = os.path.join(ROOT, ws, "Cargo.toml")
    try:
        return json.loads(subprocess.check_output(
            ["cargo", "-q", "metadata", "--format-version", "1", "--all-features", "--manifest-path", manifest]))
    except subprocess.CalledProcessError:
        sys.exit(f"deps: cargo could not resolve the workspace {manifest}; fix the error above")


def closure(nodes, start, kinds=None):
    """Every package reachable from `start`, following only the dependency kinds in `kinds` (all when None)."""
    seen, stack = set(), [start]
    while stack:
        for dep in nodes[stack.pop()]["deps"]:
            if kinds is not None and not any(k["kind"] in kinds for k in dep["dep_kinds"]):
                continue
            if dep["pkg"] not in seen:
                seen.add(dep["pkg"])
                stack.append(dep["pkg"])
    return seen


def check_declarations(meta, version, library_names):
    """Rules 1 and 2 for one workspace."""
    members = set(meta["workspace_members"])
    for pkg in meta["packages"]:
        if pkg["id"] not in members:
            continue
        manifest = tomllib.load(open(pkg["manifest_path"], "rb"))
        tables = [manifest.get(s, {}) for s in SECTIONS]
        tables += [t.get(s, {}) for t in manifest.get("target", {}).values() for s in SECTIONS]
        for table in tables:
            for name, spec in table.items():
                if not (isinstance(spec, dict) and spec.get("workspace") is True):
                    failed.append(f"{pkg['name']}: dependency `{name}` must be `{{ workspace = true }}`; declare it in its workspace's root Cargo.toml")
        if manifest["package"].get("version") != {"workspace": True}:
            failed.append(f"{pkg['name']}: must use `version.workspace = true`")
    root = tomllib.load(open(os.path.join(meta["workspace_root"], "Cargo.toml"), "rb"))["workspace"]
    if root.get("package", {}).get("version") != version:
        failed.append(f"{meta['workspace_root']}: the workspace version must be the library's, {version}")
    for name, spec in root.get("dependencies", {}).items():
        if name in library_names and (not isinstance(spec, dict) or spec.get("version") != version):
            failed.append(f"{meta['workspace_root']}: workspace dependency `{name}` must pin the library's version {version}")


def check_library(meta):
    """Rules 3 to 6: the library's workspace only."""
    members = set(meta["workspace_members"])
    names = {p["id"]: p["name"] for p in meta["packages"]}
    nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}
    graph = set()
    for pkg in meta["packages"]:
        if pkg["id"] not in members:
            continue
        for dep in pkg["dependencies"]:
            if dep["name"] not in RUNTIMES:
                continue
            if dep["name"] not in RUNTIME_HOMES.get(pkg["name"], set()):
                failed.append(f"{pkg['name']}: depends on the runtime {dep['name']}; only the tests (and the facade's dev-dependency nuclei) may")
            elif dep["kind"] != "dev" and pkg["name"] in DEV_ONLY:
                failed.append(f"{pkg['name']}: the runtime {dep['name']} must be a dev-dependency here; the facade takes the host's I/O as closures")
        if "/crates/" in pkg["manifest_path"]:
            lib = pkg["manifest_path"].removesuffix("Cargo.toml") + "src/lib.rs"
            if "#![forbid(unsafe_code)]" not in open(lib).read():
                failed.append(f"{pkg['name']}: {lib} must contain `#![forbid(unsafe_code)]`")
            bad = sorted(names[d] for d in closure(nodes, pkg["id"], (None, "build")) if names[d] in RUNTIMES)
            if bad:
                failed.append(f"{pkg['name']}: depends on an async runtime ({', '.join(bad)}); VINC crates must stay runtime-free")
        reach = closure(nodes, pkg["id"])
        graph |= reach
        bad = sorted(names[d] for d in reach if names[d] in QUIC)
        if bad:
            failed.append(f"{pkg['name']}: depends on a QUIC library ({', '.join(bad)}); VINC uses no QUIC implementation")
    bad = sorted({names[d] for d in graph if names[d] in C_CRATES or names[d].startswith("libcrux")})
    if bad:
        failed.append(f"pure Rust: crates that compile or link C are in the library's graph: {', '.join(bad)}")


library = metadata(WORKSPACES[0])
library_names = {p["name"] for p in library["packages"] if p["id"] in set(library["workspace_members"])}
version = tomllib.load(open(os.path.join(ROOT, "Cargo.toml"), "rb"))["workspace"]["package"]["version"]
check_declarations(library, version, library_names)
check_library(library)
for ws in WORKSPACES[1:]:
    check_declarations(metadata(ws), version, library_names)

for line in failed:
    print(line, file=sys.stderr)
sys.exit(1 if failed else 0)
