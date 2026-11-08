#!/usr/bin/env bash
# The proofs step of the gate: the Lean proofs, TLC on every TLA+ model, and trace validation of the Rust code
# against the TLA+ spec and the Lean model. Usage: scripts/proofs.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

TLA_HOME="${TLA_HOME:-$HOME/.local/share/tla}"
# The trace check reads ndjson with the CommunityModules Json module, which needs a TLC of the same era as the jar.
TRACE_TLC="$TLA_HOME/tla2tools-2026.11.06.jar"
COMMUNITY="$TLA_HOME/CommunityModules-deps-202611060952.jar"

need() { # need <file> <download command>
    [ -f "$1" ] || { echo "proofs: missing $1; fetch it with: $2" >&2; exit 1; }
}
need "$COMMUNITY" "curl -fsSL -o $COMMUNITY https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps.jar"
need "$TRACE_TLC" "curl -fsSL -o $TRACE_TLC https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
command -v tlc >/dev/null || { echo "proofs: tlc not found; install TLC (a wrapper around tla2tools.jar) on PATH" >&2; exit 1; }
command -v lake >/dev/null || { echo "proofs: lake not found; install Lean 4 with elan (https://github.com/leanprover/elan)" >&2; exit 1; }

echo "-- lean"
if grep -rnE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' proofs/lean/Vinc proofs/lean/Replay.lean proofs/lean/Vinc.lean \
    | grep -v '^proofs/lean/Vinc/Axioms.lean'; then
    echo "proofs: sorry, admit, axiom or native_decide in the Lean sources" >&2
    exit 1
fi
(cd proofs/lean && lake build)

run_tlc() { # run_tlc <name> <spec> <cfg> : model check one config, show the summary lines
    local out
    out=$(tlc -workers auto -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
echo "-- tlc"
run_tlc ranges VerifiedRanges VerifiedRanges
run_tlc ranges_n1 VerifiedRanges VerifiedRanges_n1
run_tlc verifier RangeVerifier RangeVerifier

echo "-- trace"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
VINC_TRACE_DIR="$dir" cargo test -q -p vinc-tests --test trace_ranges --test trace_verifier
trace_tlc() { # trace_tlc <spec> <what> : TLC of the newer era over the recorded ndjson in $dir
    local out
    out=$(VINC_TRACE_DIR="$dir" java -XX:+UseParallelGC -cp "$TRACE_TLC:$COMMUNITY" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$1" -config "proofs/tla/$1.cfg" "proofs/tla/$1.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: the recorded $2 trace is not a behaviour of its TLA+ model" >&2; exit 1; }
    echo "tlc $1: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
trace_tlc TraceVerifiedRanges ranges
trace_tlc TraceRangeVerifier verifier
proofs/lean/.lake/build/bin/replay "$dir"/*.ndjson
echo "proofs: ok"
