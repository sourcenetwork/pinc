#!/usr/bin/env bash
# The NUCLEO-H7S3L8 from the laptop: build the board's programs, load the image, run the measurement.
#
#   examples/mcu/board.sh build [3|s|z] [fast|full|slow] [chip]
#                                                  the boot stage and the image, at an optimisation level and a clock;
#                                                  `chip` runs AES-128-GCM and SHA-256 on the chip's units
#   examples/mcu/board.sh flash                    load the image into the board's external flash and start it
#   examples/mcu/board.sh run <file> [rounds]      start the image and measure; the lines measured go to <file>
#   examples/mcu/board.sh session <dir> [rounds] [chip]
#                                                  every optimisation level at each clock, one file each in <dir>
#   examples/mcu/board.sh check                    what needs no board: lints, the images linked, both ends in one process
#
# It needs the board on USB (its ST-LINK is the debug probe and the serial line) and probe-rs. PROBE_RS names the
# probe-rs command when it is not on the PATH, for instance PROBE_RS="nix shell nixpkgs#probe-rs-tools -c probe-rs";
# PORT names the serial line when it is not /dev/ttyACM0.
#
# The chip's own flash is never written: the probe loads the boot stage into RAM after a reset, and the boot stage
# maps the external flash and starts the image, or loads a new one when the laptop asks within half a second. The
# probe stays attached while the image runs, because the board stops when the probe lets go of it.
set -euo pipefail
# A file or a directory named on the command line is the caller's, relative to where the caller stands.
caller="$PWD"
cd "$(dirname "$0")"

# The sizes of the endpoint's fixed tables on the board (`pinc-core`, `sizes`): with the sizes of a host one endpoint
# holds 319 KiB, more than half of the chip's RAM. They are given to the builds for the board and to no other, so the
# laptop's end keeps the tables of a host.
device_sizes=(PINC_EVENT_BASE=128 PINC_LEDGER_ENTRIES=32 PINC_SUBS_SEEN=32 PINC_PEER_RTTS=16 PINC_PREKEY_PEERS=16
    PINC_REJOIN_ADDRS=16 PINC_MAX_DATAGRAM=1500)

read -r -a probe <<<"${PROBE_RS:-probe-rs}"
port="${PORT:-/dev/ttyACM0}"
target=thumbv7em-none-eabihf
out="target/$target/release"
peer=target/release/pinc-mcu-peer
boot_pid=""

stop_boot() {
    if [ -n "$boot_pid" ]; then
        kill "$boot_pid" 2>/dev/null || true
        wait "$boot_pid" 2>/dev/null || true
        boot_pid=""
    fi
}
trap stop_boot EXIT

# Reset the chip and run the boot stage from RAM; the probe stays attached until stop_boot.
# The probe does not stop the core at a fault: the image's own handler reports it on the serial line.
start_boot() {
    stop_boot
    "${probe[@]}" run --chip STM32H7S3L8 --protocol swd --connect-under-reset --no-catch-hardfault \
        "$out/pinc-mcu-boot" >/dev/null 2>&1 &
    boot_pid=$!
}

build() {
    local level="${1:-3}" features=()
    case "${2:-}" in
    fast) features=(--features pinc-mcu-boot/fast-clock,pinc-mcu-firmware/fast-clock) ;;
    full) features=(--features pinc-mcu-boot/full-clock,pinc-mcu-firmware/full-clock) ;;
    esac
    if [ "${3:-}" = chip ]; then
        features+=(--features pinc-mcu-firmware/chip-crypto)
    fi
    env "${device_sizes[@]}" CARGO_PROFILE_RELEASE_OPT_LEVEL="$level" cargo build -q --release --target "$target" \
        -p pinc-mcu-boot -p pinc-mcu-firmware "${features[@]}"
    cargo build -q --release -p pinc-mcu-peer
}

flash() {
    # The laptop asks for the loader until the boot stage, started after it, answers.
    "$peer" flash "$out/pinc-mcu-firmware" --port "$port" &
    local loader=$!
    sleep 0.5
    start_boot
    wait "$loader"
}

run() {
    local file="$1" rounds="${2:-10}" status=0
    start_boot
    # The boot stage waits half a second for a load request, and the image takes a moment to build its node.
    sleep 3
    "$peer" run --port "$port" --out "$file" --rounds "$rounds" "${@:3}" || status=$?
    stop_boot
    return "$status"
}

session() {
    local dir="$1" rounds="${2:-10}" crypto="${3:-}" failed=0
    mkdir -p "$dir"
    for clock in slow fast full; do
        for level in 3 s z; do
            local name="64mhz"
            [ "$clock" = fast ] && name="320mhz"
            [ "$clock" = full ] && name="600mhz"
            echo "== $name, opt-level $level"
            build "$level" "$clock" "$crypto"
            flash
            stop_boot
            local note=""
            if ! run "$dir/$name-opt-$level.txt" "$rounds"; then
                # A dial is the deepest path of the stack; an image whose run does not end is measured accepting.
                note=" note=\"a first run did not end; this is a second run, of the sessions the laptop dials only\""
                if ! run "$dir/$name-opt-$level.txt" "$rounds" --laptop-dials-only; then
                    echo "error: $name at opt-level $level ran neither way; the session goes on" >&2
                    failed=1
                    continue
                fi
            fi
            # What the file's numbers were measured on.
            {
                echo "conditions date=$(date -u +%Y-%m-%dT%H:%MZ) commit=$(git rev-parse --short HEAD)$(git diff --quiet HEAD -- . ../../crates ':!results' || echo +changes) opt_level=$level$note"
                echo "conditions rustc=\"$(rustc --version)\" probe=\"$("${probe[@]}" --version | head -1)\""
                echo "conditions laptop=\"$(uname -srm)\" cpu=\"$(sed -n 's/^model name[^:]*: //p' /proc/cpuinfo | head -1)\""
            } >>"$dir/$name-opt-$level.txt"
        done
    done
    return "$failed"
}

# What needs no board. The board's programs are linted and linked with the device's sizes; the two ends of the line
# run in one process with the tables of a host, and again with those of a device in a build directory of its own.
check() {
    local board=(-p pinc-mcu-boot -p pinc-mcu-firmware --release --target "$target")
    cargo clippy -q -p pinc-mcu-link -p pinc-mcu-peer --all-targets -- -D warnings
    env "${device_sizes[@]}" cargo clippy -q "${board[@]}" -- -D warnings
    env "${device_sizes[@]}" cargo clippy -q "${board[@]}" --all-features -- -D warnings
    env "${device_sizes[@]}" cargo build -q "${board[@]}"
    cargo test -q -p pinc-mcu-link
    env "${device_sizes[@]}" cargo test -q -p pinc-mcu-link --target-dir target/device-sizes
}

case "${1:-}" in
check) check ;;
build) build "${2:-3}" "${3:-}" "${4:-}" ;;
flash) flash ;;
run) run "$(cd "$caller" && realpath -m "${2:?the file for the measured lines}")" "${3:-10}" ;;
session) session "$(cd "$caller" && realpath -m "${2:?the directory for the session}")" "${3:-10}" "${4:-}" ;;
*)
    sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
