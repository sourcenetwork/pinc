#!/usr/bin/env bash
# The largest stack frames of the functions of one binary whose name matches a pattern, from its disassembly: the bytes
# the prologue reserves, the stack-probe loop of a frame over 4 KiB included. Usage: scripts/frames.sh <binary> [pattern]
# [count].
set -euo pipefail
bin=$1
pat=${2:-vinc}
n=${3:-20}
objdump -d --demangle --no-show-raw-insn "$bin" | awk -v pat="$pat" '
    /^[0-9a-f]+ <.*>:$/ { name = $0; sub(/^[0-9a-f]+ </, "", name); sub(/>:$/, "", name); seen = 0; next }
    name ~ pat && !seen && /lea +-0x[0-9a-f]+\(%rsp\),%r11/ {
        match($0, /-0x[0-9a-f]+/); v = strtonum(substr($0, RSTART + 2, RLENGTH - 2));
        printf "%d %s\n", v, name; seen = 1; next
    }
    name ~ pat && !seen && /sub +\$0x[0-9a-f]+,%rsp/ {
        match($0, /\$0x[0-9a-f]+/); v = strtonum(substr($0, RSTART + 1, RLENGTH - 1));
        printf "%d %s\n", v, name; seen = 1
    }' | sort -rn | head -"$n"
