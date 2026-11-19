#!/usr/bin/env bash
# Coverage of the library crates under the trace tests only, and, for the Rust items docs/PROOFS.md names as modelled, the
# lines (and, with BRANCH=1, the branches) the trace tests never run. Needs cargo-llvm-cov and the llvm-tools component
# (cargo install cargo-llvm-cov; rustup component add llvm-tools-preview). BRANCH=1 uses the nightly toolchain, since
# branch coverage is not stable. Output stays under target/; nothing is committed. Usage: [BRANCH=1] scripts/trace-cov.sh
set -euo pipefail
cd "$(dirname "$0")/.."
tc=() lcov=target/cov.lcov br=()
if [ "${BRANCH:-0}" = 1 ]; then tc=(+nightly) br=(--branch) lcov=target/cov-branch.lcov; fi
tests=$(grep -o -- '--test trace_[a-z_]*' scripts/proofs.sh | sort -u | tr '\n' ' ')
ignore='(tests|pinc-sim)/'
cargo "${tc[@]}" llvm-cov clean --workspace
# shellcheck disable=SC2086
CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}" cargo "${tc[@]}" llvm-cov "${br[@]}" --no-report -p pinc-tests --features hwenc $tests
cargo "${tc[@]}" llvm-cov report "${br[@]}" --lcov --output-path "$lcov" --ignore-filename-regex "$ignore"
cargo "${tc[@]}" llvm-cov report "${br[@]}" --summary-only --ignore-filename-regex "$ignore" | tail -n +1 > "${lcov%.lcov}.summary"
python3 -I scripts/cov-modelled.py "$lcov" | tee "${lcov%.lcov}-modelled.txt"
