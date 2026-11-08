#!/usr/bin/env bash
# The gate: every check must pass before a push. Usage: scripts/gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== deps";     python3 scripts/deps.py
echo "== fmt";      cargo fmt --all --check
echo "== clippy";   cargo clippy --workspace --all-targets --all-features -- -D warnings
echo "== doc";      RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --all-features
echo "== no_std";   for c in $(cargo metadata --no-deps --format-version 1 | python3 -c 'import json,sys; print(" ".join(p["name"] for p in json.load(sys.stdin)["packages"] if "no_std" in (p.get("keywords") or [])))'); do for t in thumbv7em-none-eabihf wasm32-unknown-unknown; do cargo build -q -p "$c" --no-default-features --target "$t"; done; done
echo "== pure";     ! find target -path '*/build/*' \( -name '*.o' -o -name '*.a' -o -name '*.so' -o -name '*.obj' \) | grep . || { echo "a build script compiled C (listed above); VINC is pure Rust" >&2; exit 1; }
echo "== tests";    cargo nextest run --workspace --all-features --profile ci
echo "== doctests"; cargo test --workspace --doc --all-features -q
echo "== proofs";   scripts/proofs.sh
echo "gate: ok"
