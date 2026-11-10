#!/usr/bin/env bash
cd "$(dirname "$0")"
export PATH="$HOME/.local/bin:$PATH"
jt=$(mktemp -d)
start=$(date +%s)
out=$(JAVA_TOOL_OPTIONS="-XX:MaxRAMPercentage=15 -Djava.io.tmpdir=$jt" tlc -workers auto -metadir proofs/tla/states/lwlive_$1 -config proofs/tla/$1.cfg proofs/tla/Streams.tla 2>&1) && echo "OK $1 $(( $(date +%s) - start ))s: $(echo "$out" | grep -E 'states generated, ' | tail -1)" || { echo "FAIL $1"; echo "$out" | grep -E 'violated|Error' | head; }
echo LIVEDONE
