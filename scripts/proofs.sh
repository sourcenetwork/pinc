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
run_tlc_deep() { # run_tlc_deep <name> <spec> <cfg> : like run_tlc, with the deep thread stack the word arithmetic of the specs needs
    local out
    out=$(java -Xss256m -XX:+UseParallelGC -cp "$TLA_HOME/tla2tools.jar" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
witness_tlc() { # witness_tlc <name> <spec> <cfg> <property> : TLC must find a violation of <property> (a reachability witness or a documented finding)
    local out
    if out=$(tlc -workers auto -metadir "proofs/tla/states/$1" -config "proofs/tla/$3.cfg" "proofs/tla/$2.tla" 2>&1); then
        echo "$out" >&2; echo "proofs: TLC found no violation of $4 in $3: the witness is gone" >&2; exit 1
    fi
    grep -q "$4 is violated" <<<"$out" \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3 for another reason than $4" >&2; exit 1; }
    echo "tlc $3: finds the expected violation of $4"
}
echo "-- tlc"
# The independent model checks run at most 3 at a time; a failure of any stops the script.
par() {
    while [ "$(jobs -rp | wc -l)" -ge 3 ]; do wait -n || exit 1; done
    "$@" &
}
par run_tlc ranges VerifiedRanges VerifiedRanges
par run_tlc ranges_n1 VerifiedRanges VerifiedRanges_n1
par run_tlc verifier RangeVerifier RangeVerifier
par run_tlc handshake Handshake Handshake
par run_tlc handshake_resume Handshake Handshake_resume
par run_tlc handshake_late Handshake Handshake_late
par run_tlc handshake_stores Handshake Handshake_stores
par run_tlc record Record Record
par run_tlc record_chacha Record Record_chacha
par run_tlc headerprot HeaderProt HeaderProt
par run_tlc headerprot_pn HeaderProt HeaderProt_pn
par run_tlc keyroll KeyRoll KeyRoll
par run_tlc keyroll_collide KeyRoll KeyRoll_collide
par run_tlc keyroll_two KeyRoll KeyRoll_two
par run_tlc keyroll_forge KeyRoll KeyRoll_forge
par witness_tlc keyroll_good KeyRoll KeyRoll_good NotGood
par run_tlc keyroll_stale KeyRoll KeyRoll_stale
par run_tlc keyroll_gate KeyRoll KeyRoll_gate
par run_tlc keyroll_orphan KeyRoll KeyRoll_orphan
par run_tlc labels Labels Labels
par run_tlc credit_w2 Credit Credit_w2
par run_tlc credit Credit Credit
par run_tlc transcript Transcript Transcript
par run_tlc amp Amp Amp
par run_tlc padding Padding Padding
par run_tlc_deep varint Varint Varint
par run_tlc_deep rekeycodec RekeyCodec RekeyCodec
par run_tlc_deep partition PartitionPoint PartitionPoint
par run_tlc_deep layout Layout Layout
par run_tlc_deep encoder Encoder Encoder
par run_tlc_deep builderbytes BuilderBytes BuilderBytes
par run_tlc_deep verifierbytes VerifierBytes VerifierBytes
par run_tlc tickets_client Tickets Tickets
par run_tlc tickets_client3 Tickets Tickets_n3
par run_tlc tickets_server Tickets Tickets_server
par run_tlc tickets_zero Tickets Tickets_zero
par run_tlc prekeycache PrekeyCache PrekeyCache
par run_tlc prekeycache_n0 PrekeyCache PrekeyCache_n0
par run_tlc prekeycache_n3 PrekeyCache PrekeyCache_n3
while [ -n "$(jobs -rp)" ]; do wait -n || exit 1; done

echo "-- trace"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
VINC_TRACE_DIR="$dir" cargo test -q -p vinc-tests --test trace_ranges --test trace_verifier --test trace_builder --test trace_tla --test trace_handshake --test trace_security --test trace_keyroll --test trace_keylayer --test trace_stores
trace_tlc() { # trace_tlc <spec> <what> : TLC of the newer era over the recorded ndjson in $dir
    local out
    # -Xss: TLC's evaluator recurses deeply on the larger builder tables, which overflows the default thread stack.
    out=$(VINC_TRACE_DIR="$dir" java -Xss256m -XX:+UseParallelGC -cp "$TRACE_TLC:$COMMUNITY" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$1" -config "proofs/tla/$1.cfg" "proofs/tla/$1.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: the recorded $2 trace is not a behaviour of its TLA+ model" >&2; exit 1; }
    echo "tlc $1: $(echo "$out" | grep -E 'states generated, ' | tail -1)"
}
trace_tlc TraceVerifiedRanges ranges
trace_tlc TraceVarint varint
trace_tlc TraceLayout layout
trace_tlc TraceEncoder encoder
trace_tlc TraceRangeVerifier verifier
trace_tlc TraceBuilder builder
trace_tlc TraceHandshake handshake
trace_tlc TraceSecurity security
trace_tlc TraceKeyRoll keyroll
trace_tlc TraceKeyLayer "key layer"
trace_tlc TraceStores stores
proofs/lean/.lake/build/bin/replay "$dir"/*.ndjson
echo "proofs: ok"
