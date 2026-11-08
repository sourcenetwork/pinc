#!/usr/bin/env python3
"""Dependency rules, checked by the gate.

1. Every dependency of every workspace member is declared once, in the root `[workspace.dependencies]`; a member
   manifest may only say `{ workspace = true }` (plus features or `optional`).
2. Every member has the one workspace version (`version.workspace = true`), and every VINC crate entry in
   `[workspace.dependencies]` pins that same version.
3. Every library crate under `crates/` forbids unsafe code in its root (`#![forbid(unsafe_code)]`); the workspace lint is only `deny` so the test allocator can allow it.
4. No library crate under `crates/` depends, directly or transitively, on an async runtime.
"""
import json
import subprocess
import sys
import tomllib

RUNTIMES = {"tokio", "async-std", "smol", "async-executor", "glommio", "monoio", "embassy-executor"}
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

for line in failed:
    print(line, file=sys.stderr)
sys.exit(1 if failed else 0)
