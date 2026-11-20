#!/usr/bin/env bash
# The proofs step of the gate: the Lean proofs, TLC on every TLA+ model, trace validation of the Rust code against the
# TLA+ spec and the Lean model, and model-based tests (the Rust code driven along TLC's state graph of a model).
# Usage: scripts/proofs.sh [deep]
# Without an argument it runs the quick profile: a model with a file under proofs/tla/quick/ is checked over the
# smaller bounds of that file (the same specification and the same properties), so the whole step takes minutes.
# `deep` checks every model over the bounds docs/proofs/properties.md states for it.
set -euo pipefail
PROFILE="${1:-quick}"
case "$PROFILE" in quick|deep) ;; *) echo "usage: scripts/proofs.sh [deep]" >&2; exit 2 ;; esac
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

TLA_HOME="${TLA_HOME:-$HOME/.local/share/tla}"
# Parallel TLC runs unpack the standard modules into the temp directory; give this run its own.
mkdir -p proofs/tla/states/tmp
export JAVA_TOOL_OPTIONS="${JAVA_TOOL_OPTIONS:-} -Djava.io.tmpdir=$PWD/proofs/tla/states/tmp"
# The trace check reads ndjson with the CommunityModules Json module, which needs a TLC of the same era as the jar.
TRACE_TLC="$TLA_HOME/tla2tools-2026.11.06.jar"
COMMUNITY="$TLA_HOME/CommunityModules-deps-202611060952.jar"
# TLC unpacks its standard modules into the JVM's temporary directory; runs that share one race on those files, so
# every run gets its own. The JVM's default heap bound is a quarter of the memory it sees, so 3 parallel runs could
# take 75% of the machine; 15% each keeps the 3 under half (of the cgroup limit, when the run has one).
# A quick model is small and its run is mostly TLC's start: it gets one worker, and one check runs per processor (16 at
# most), each with its share of the same half. A deep model gets every processor, 3 at a time.
if [ "$PROFILE" = quick ]; then
    JOBS=$(getconf _NPROCESSORS_ONLN); [ "$JOBS" -le 16 ] || JOBS=16
    WORKERS=1; HEAP=$((45 / JOBS)); [ "$HEAP" -ge 2 ] || HEAP=2
    # A run of a second or two never repays the optimising compiler: the first tier alone starts a third faster.
    JIT=' -XX:TieredStopAtLevel=1'
else
    JOBS=3; WORKERS=auto; HEAP=15; JIT=''
    # the trace tests record their full count of generated cases (the quick profile records fewer)
    export PINC_TRACE_DEEP=1
fi
jtmp_root=$(mktemp -d)
trap 'rm -rf "$jtmp_root"' EXIT
jopts() { printf -- '-XX:MaxRAMPercentage=%s%s -Djava.io.tmpdir=%s' "$HEAP" "$JIT" "$(mktemp -d "$jtmp_root/XXXXXX")"; }
cfg() { # cfg <config> : the file TLC reads for <config> in this profile
    if [ "$PROFILE" = quick ] && [ -f "proofs/tla/quick/$1.cfg" ]; then echo "proofs/tla/quick/$1.cfg"; else echo "proofs/tla/$1.cfg"; fi
}


# `wait -n` (bash 4.3) runs the model checks in parallel; macOS ships bash 3.2.
if [ "${BASH_VERSINFO[0]}" -lt 4 ] || { [ "${BASH_VERSINFO[0]}" -eq 4 ] && [ "${BASH_VERSINFO[1]}" -lt 3 ]; }; then
    echo "proofs: bash 4.3 or newer is needed (this is $BASH_VERSION); on macOS: brew install bash" >&2; exit 1
fi

need() { # need <file> <download command>
    [ -f "$1" ] || { echo "proofs: missing $1; fetch it with: $2" >&2; exit 1; }
}
need "$COMMUNITY" "curl -fsSL -o $COMMUNITY https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps.jar"
need "$TRACE_TLC" "curl -fsSL -o $TRACE_TLC https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
command -v tlc >/dev/null || { echo "proofs: tlc not found; install TLC (a wrapper around tla2tools.jar) on PATH" >&2; exit 1; }
command -v lake >/dev/null || { echo "proofs: lake not found; install Lean 4 with elan (https://github.com/leanprover/elan)" >&2; exit 1; }

echo "-- lean"
if grep -rnE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' proofs/lean/Pinc proofs/lean/Replay.lean proofs/lean/Pinc.lean \
    | grep -v '^proofs/lean/Pinc/Axioms.lean'; then
    echo "proofs: sorry, admit, axiom or native_decide in the Lean sources" >&2
    exit 1
fi
(cd proofs/lean && lake build)

run_tlc() { # run_tlc <name> <spec> <cfg> : model check one config, show the summary lines
    local out t0=$SECONDS
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers "$WORKERS" -metadir "proofs/tla/states/$1" -config "$(cfg "$3")" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1) [$((SECONDS - t0))s]"
}
run_tlc_deep() { # run_tlc_deep <name> <spec> <cfg> : like run_tlc, with the deep thread stack the word arithmetic of the specs needs
    local out t0=$SECONDS
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" java -Xss256m -XX:+UseParallelGC -cp "$TLA_HOME/tla2tools.jar" tlc2.TLC -workers "$WORKERS" \
        -metadir "proofs/tla/states/$1" -config "$(cfg "$3")" "proofs/tla/$2.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3" >&2; exit 1; }
    echo "tlc $3: $(echo "$out" | grep -E 'states generated, ' | tail -1) [$((SECONDS - t0))s]"
}
witness_tlc() { # witness_tlc <name> <spec> <cfg> <property> : TLC must find a violation of <property> (a reachability witness or a documented finding)
    local out t0=$SECONDS
    if out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers "$WORKERS" -metadir "proofs/tla/states/$1" -config "$(cfg "$3")" "proofs/tla/$2.tla" 2>&1); then
        echo "$out" >&2; echo "proofs: TLC found no violation of $4 in $3: the witness is gone" >&2; exit 1
    fi
    grep -q "$4 is violated" <<<"$out" \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3 for another reason than $4" >&2; exit 1; }
    echo "tlc $3: finds the expected violation of $4 [$((SECONDS - t0))s]"
}
witness_live_tlc() { # witness_live_tlc <name> <spec> <cfg> : TLC must find a counterexample to the liveness property (the stuck states the code had)
    local out t0=$SECONDS
    if out=$(JAVA_TOOL_OPTIONS="$(jopts)" tlc -workers "$WORKERS" -metadir "proofs/tla/states/$1" -config "$(cfg "$3")" "proofs/tla/$2.tla" 2>&1); then
        echo "$out" >&2; echo "proofs: TLC found no liveness violation in $3: the witness is gone" >&2; exit 1
    fi
    grep -q "Temporal properties were violated" <<<"$out" \
        || { echo "$out" >&2; echo "proofs: TLC failed on $3 for another reason than a liveness violation" >&2; exit 1; }
    echo "tlc $3: finds the expected liveness violation [$((SECONDS - t0))s]"
}
echo "-- tlc"
# The independent model checks run at most $JOBS at a time; a failure of any stops the script.
par() {
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n || exit 1; done
    "$@" &
}
. scripts/proofs/tlc.sh
. scripts/proofs/tlc-broadcast.sh
. scripts/proofs/tlc-connect.sh
. scripts/proofs/tlc-core.sh
. scripts/proofs/tlc-dag.sh
. scripts/proofs/tlc-node.sh
. scripts/proofs/tlc-portmap.sh
. scripts/proofs/tlc-security.sh
. scripts/proofs/tlc-table.sh
. scripts/proofs/tlc-transport.sh
. scripts/proofs/tlc-wire.sh
. scripts/proofs/tlc-facade.sh
while [ -n "$(jobs -rp)" ]; do wait -n || exit 1; done

echo "-- trace"
# A trace check passes only if the replay reaches the end of its trace (proofs/tla/TraceEnd.tla); every config says so,
# a quick one too (`cfg` prefers it).
for c in proofs/tla/Trace*.cfg proofs/tla/quick/Trace*.cfg; do
    [ -e "$c" ] || continue
    grep -qx 'INVARIANT ReplayAtEnd' "$c" && grep -qx 'POSTCONDITION ReplayEnded' "$c" && continue
    echo "proofs: $c does not check that the replay reaches the end of the trace; add INVARIANT ReplayAtEnd and POSTCONDITION ReplayEnded" >&2
    exit 1
done
dir=$(mktemp -d)
trap 'rm -rf "$dir" "$jtmp_root"' EXIT
trace_tlc() { # trace_tlc <spec> <what> : TLC of the newer era over the recorded ndjson in $dir
    local out t0=$SECONDS
    # -Xss: TLC's evaluator recurses deeply on the larger builder tables, which overflows the default thread stack.
    # One worker: the end check (proofs/tla/TraceEnd.tla) keeps its mark in a TLC register, which is per worker.
    out=$(JAVA_TOOL_OPTIONS="$(jopts)" PINC_TRACE_DIR="$dir" java -Xss256m -XX:+UseParallelGC -cp "$TRACE_TLC:$COMMUNITY" tlc2.TLC -workers 1 \
        -metadir "proofs/tla/states/$1" -config "$(cfg "$1")" "proofs/tla/$1.tla" 2>&1) \
        || { echo "$out" >&2; echo "proofs: the recorded $2 trace is not a behaviour of its TLA+ model" >&2; exit 1; }
    echo "tlc $1: $(echo "$out" | grep -E 'states generated, ' | tail -1) [$((SECONDS - t0))s]"
}
. scripts/proofs/trace.sh
while [ -n "$(jobs -rp)" ]; do wait -n || exit 1; done
proofs/lean/.lake/build/bin/replay "$dir"/*.ndjson

echo "-- model-based tests"
mbt_cases() { # mbt_cases <spec> <cfg> <out> : TLC's state graph of <cfg> as paths that take every edge, in $dir/mbt/<out>
    local log="$dir/mbt/$2.log"
    # the labels of the edges carry the actions' arguments from the 2026 TLC on
    JAVA_TOOL_OPTIONS="$(jopts)" java -Xss256m -XX:+UseParallelGC -cp "$TRACE_TLC" tlc2.TLC -workers auto \
        -metadir "proofs/tla/states/$2" -dump dot,actionlabels,constrained "$dir/mbt/$2.dot" \
        -config "proofs/tla/$2.cfg" "proofs/tla/$1.tla" > "$log" 2>&1 \
        || { cat "$log" >&2; echo "proofs: TLC failed on $2" >&2; exit 1; }
    python3 scripts/mbt.py "$dir/mbt/$2.dot" "proofs/tla/$2.cfg" "$log" "$dir/mbt/$3"
}
mkdir -p "$dir/mbt"
. scripts/proofs/mbt.sh
echo "proofs: ok"
