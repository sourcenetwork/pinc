#!/usr/bin/env bash
# Soak the link between the Rust code and its models: record the trace tests under fresh seeds and replay them in the
# Lean model, over and over, so a divergence on inputs the fixed seeds of the gate never produce shows up.
#
# Usage: scripts/trace-soak.sh [-n iterations] [-b first_seed] [-k tlc_every]
#   -n  stop after this many iterations (default: run until a mismatch or until interrupted)
#   -b  the seed base of the first iteration (default: from the clock); iteration i uses base+i, so a failure
#       reproduces with: PINC_TRACE_SEED=<seed> PINC_TRACE_DIR=<dir> cargo test -p pinc-tests --features hwenc --test trace_<x>
#   -x  comma-separated names of ndjson files (without the extension) not to replay: those of a component whose model
#       is known to be stale, so that it does not hide a mismatch in the others
#   -k  also run every TLC trace check on the recorded files every k-th iteration (default 0: Lean replay only);
#       TLC uses 2 workers. Needs the jars of scripts/proofs.sh.
# Each iteration sets PINC_TRACE_SEED, which moves every seed of every trace test that draws from `SplitMix64::traced`
# (tests/support/lib.rs); unset, the tests run their fixed seeds. On a mismatch the recorded ndjson is kept in
# target/trace-soak/fail-<seed>/ and the script exits 1. A trace test that fails one of its own assertions (it then writes no
# trace) is reported, its log kept in target/trace-soak/assert-<seed>.log, and the run goes on.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

iters=0 base=$(( $(date +%s) * 1000 )) every=0 skip=,
while getopts n:b:k:x: o; do
    case $o in
        n) iters=$OPTARG ;; b) base=$OPTARG ;; k) every=$OPTARG ;; x) skip=,$OPTARG, ;;
        *) sed -n 2,15p "$0"; exit 2 ;;
    esac
done
if [ "$every" -gt 0 ]; then
    command -v java >/dev/null || { echo "trace-soak: -k needs java on PATH" >&2; exit 1; }
fi
replay=proofs/lean/.lake/build/bin/replay
[ -x "$replay" ] || { echo "trace-soak: build the replay binary first: (cd proofs/lean && lake build)" >&2; exit 1; }

# The trace tests are the ones the gate runs: its cargo line names them.
tests=$(grep -o -- '--test trace_[a-z_]*' scripts/proofs.sh | sort -u | tr '\n' ' ')
# shellcheck disable=SC2086
cargo test -q -p pinc-tests --features hwenc --no-run $tests >/dev/null 2>&1 || true

tlc_check() { # tlc_check <dir> : the TLC trace checks of the gate over the ndjson in <dir>
    local tla="${TLA_HOME:-$HOME/.local/share/tla}" spec out st
    st=$(mktemp -d)
    for spec in $(grep -o '^trace_tlc Trace[A-Za-z]*' scripts/proofs.sh | cut -d' ' -f2); do
        # a -x name that is the spec's name without "Trace" (membership, streams) skips its TLC check too
        lower=$(echo "${spec#Trace}" | tr 'A-Z' 'a-z')
        case "$skip" in *,"$lower",*) continue ;; esac
        out=$(PINC_TRACE_DIR="$1" java -Xss256m -XX:+UseParallelGC -Djava.io.tmpdir="$st" \
            -cp "$tla/tla2tools-2026.11.06.jar:$tla/CommunityModules-deps-202611060952.jar" tlc2.TLC -workers 2 \
            -metadir "$st/$spec" -config "proofs/tla/$spec.cfg" "proofs/tla/$spec.tla" 2>&1) \
            || {
                # TLC's integers are 32-bit: a recorded value beyond them is TLC's limit (the Lean replay has none), not a mismatch.
                if grep -q "Overflow when computing" <<<"$out"; then
                    echo "trace-soak: TLC trace check $spec: $(echo "$out" | grep -m1 'Overflow when computing') (32-bit limit; skipped)"
                    continue
                fi
                echo "$out" | grep -v '^[0-9]*\. Line' | tail -40; echo "trace-soak: TLC trace check $spec failed"; rm -rf "$st"; return 1
            }
    done
    rm -rf "$st"
}

i=0 asserts=0 start=$SECONDS
while [ "$iters" -eq 0 ] || [ "$i" -lt "$iters" ]; do
    i=$((i + 1)) seed=$((base + i))
    dir=$(mktemp -d)
    ok=1
    # shellcheck disable=SC2086
    PINC_TRACE_SEED=$seed PINC_TRACE_DIR="$dir" cargo test -q -p pinc-tests --features hwenc --no-fail-fast $tests >"$dir/cargo.log" 2>&1 \
        || {
            # A test's own assertion failed (not a model mismatch): the test writes no trace, the others are still replayed.
            # It is a finding about the test or the code, so its log is kept.
            echo "trace-soak: seed $seed: a trace test failed its own assertions: $(grep -o '`-p pinc-tests --test [a-z_]*`' "$dir/cargo.log" | sort -u | tr '\n' ' ')"
            mkdir -p target/trace-soak && cp "$dir/cargo.log" "target/trace-soak/assert-$seed.log"
            asserts=$((asserts + 1))
        }
    if [ $ok = 1 ]; then
        # One file at a time: the replay stops at the first mismatch, and every file that mismatches is a finding.
        for f in "$dir"/*.ndjson; do
            name=$(basename "$f" .ndjson)
            case "$skip" in *,"$name",*) continue ;; esac
            "$replay" "$f" >"$dir/replay.log" 2>&1 \
                || { echo "trace-soak: seed $seed: Lean replay mismatch in $name"; tail -3 "$dir/replay.log"; ok=0; }
        done
    fi
    if [ $ok = 1 ] && [ "$every" -gt 0 ] && [ $((i % every)) -eq 0 ]; then
        tlc_check "$dir" || ok=0
    fi
    if [ $ok = 0 ]; then
        keep=target/trace-soak/fail-$seed
        mkdir -p target/trace-soak && rm -rf "$keep" && mv "$dir" "$keep"
        echo "trace-soak: failing traces kept in $keep (seed $seed, iteration $i)"
        exit 1
    fi
    rm -rf "$dir"
    echo "trace-soak: iteration $i seed $seed ok ($((SECONDS - start))s)"
done
echo "trace-soak: $i iterations ok ($asserts with a test failing its own assertion)"
