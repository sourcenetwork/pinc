# PINC tasks. `just` lists them; `just gate` runs everything a change must pass; CI runs the same recipes.

set shell := ["bash", "-euo", "pipefail", "-c"]

tla_home := env_var_or_default("TLA_HOME", env_var("HOME") / ".local/share/tla")
no_std_targets := "thumbv7em-none-eabihf wasm32-unknown-unknown"
# Targets without 32-bit compare-and-swap (the Cortex-M0 class): only the program's crates build there.
cas_less_targets := "thumbv6m-none-eabi"
# The benchmarks and the distributed harness are workspaces of their own (the libraries they measure PINC against,
# their runtime and their C code stay out of the library's graph). They build into one directory beside the library's,
# so the library's build output, which `pure` scans, never holds the comparators' C code.
target := env_var_or_default("CARGO_TARGET_DIR", justfile_directory() / "target")
harness_target := target + "-harness"
benches := "--manifest-path benches/Cargo.toml --target-dir " + harness_target
dist := "--manifest-path distributed/Cargo.toml --target-dir " + harness_target
# A measurement compiles every stack for the machine that runs it, so each stack's ciphers use the widest vector code
# the CPU has (the library's own AES otherwise stays on 128-bit vectors on a CPU with VAES and no AVX-512). Its own
# build directory, so the gate's builds are not rebuilt.
native := "-C target-cpu=native"
measure_target := target + "-measure"

# List the recipes.
default:
    @just --list

# Install everything: Java, swtpm, Python, the pinned Rust toolchain, cargo-nextest, Lean and the TLA+ tools.
setup: _system _rust _nextest _lean tla-tools
    @echo "setup: ok"

_system:
    #!/usr/bin/env bash
    set -euo pipefail
    missing=()
    command -v java >/dev/null || missing+=(java)
    command -v swtpm >/dev/null || missing+=(swtpm)
    command -v python3 >/dev/null || missing+=(python3)
    command -v curl >/dev/null || missing+=(curl)
    [ ${#missing[@]} -eq 0 ] && { echo "system packages: present"; exit 0; }
    sudo=""; [ "$(id -u)" -ne 0 ] && sudo="sudo"
    pkgs=()
    if command -v pacman >/dev/null; then
        for m in "${missing[@]}"; do case $m in java) pkgs+=(jre-openjdk-headless);; python3) pkgs+=(python);; *) pkgs+=("$m");; esac; done
        $sudo pacman -S --needed --noconfirm "${pkgs[@]}"
    elif command -v apt-get >/dev/null; then
        for m in "${missing[@]}"; do case $m in java) pkgs+=(default-jre-headless);; *) pkgs+=("$m");; esac; done
        $sudo apt-get update -q && $sudo apt-get install -y -q "${pkgs[@]}"
    elif command -v dnf >/dev/null; then
        for m in "${missing[@]}"; do case $m in java) pkgs+=(java-latest-openjdk-headless);; *) pkgs+=("$m");; esac; done
        $sudo dnf install -y "${pkgs[@]}"
    elif command -v brew >/dev/null; then
        for m in "${missing[@]}"; do case $m in java) pkgs+=(openjdk);; python3) pkgs+=(python);; *) pkgs+=("$m");; esac; done
        brew install "${pkgs[@]}"
    else
        echo "setup: install these with your package manager, then run just setup again: ${missing[*]}" >&2; exit 1
    fi

_rust:
    #!/usr/bin/env bash
    set -euo pipefail
    if ! command -v rustup >/dev/null; then
        curl -sSfL https://sh.rustup.rs | sh -s -- -y --default-toolchain none
        . "$HOME/.cargo/env"
    fi
    rustup toolchain install

_nextest:
    #!/usr/bin/env bash
    set -euo pipefail
    command -v cargo-nextest >/dev/null && { cargo nextest --version | head -1; exit 0; }
    case "$(uname -s)" in
        Linux) curl -sSfL https://get.nexte.st/latest/linux | tar zxf - -C "${CARGO_HOME:-$HOME/.cargo}/bin" ;;
        Darwin) curl -sSfL https://get.nexte.st/latest/mac | tar zxf - -C "${CARGO_HOME:-$HOME/.cargo}/bin" ;;
        *) cargo install --locked cargo-nextest ;;
    esac
    cargo nextest --version | head -1

_lean:
    #!/usr/bin/env bash
    set -euo pipefail
    export PATH="$HOME/.elan/bin:$PATH"
    if ! command -v elan >/dev/null; then
        curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
    fi
    elan toolchain install "$(cat proofs/lean/lean-toolchain)"
    (cd proofs/lean && lake --version)

# Everything a change must pass before it is pushed.
gate: checks test unoptimised test-distributed doctest proofs
    @echo "gate: ok"

# Every static check: dependency rules, format, lints, docs, no_std builds, pure Rust.
checks: deps hygiene fmt-check clippy build doc no-std pure

# Dependency rules: declared only at the root, one version, unsafe forbidden, no async runtime, no C.
deps:
    $(command -v python3.11 || command -v python3) scripts/deps.py

# Public-repository hygiene: no internal project names and no em-dash or en-dash in any tracked file.
hygiene:
    #!/usr/bin/env bash
    set -euo pipefail
    names='finalist|grader|pinc_experiments|eurekagent|roster_settle|kindling|scramdb'
    if git grep -nIiE --untracked "$names" -- . ':!justfile'; then echo "hygiene: internal names in the files above" >&2; exit 1; fi
    if git grep -nIP --untracked '[\x{2013}\x{2014}]' -- .; then echo "hygiene: em-dash or en-dash in the files above" >&2; exit 1; fi

# Format every crate.
fmt:
    cargo fmt --all
    cargo fmt --all --manifest-path benches/Cargo.toml
    cargo fmt --all --manifest-path distributed/Cargo.toml

# Fail if any file is not formatted.
fmt-check:
    cargo fmt --all --check
    cargo fmt --all --check --manifest-path benches/Cargo.toml
    cargo fmt --all --check --manifest-path distributed/Cargo.toml

# Lints on every target and feature, warnings as errors.
clippy:
    cargo clippy --workspace --all-targets --all-features -- -D warnings
    cargo clippy -p pinc -p pinc-keystore --no-default-features --all-targets -- -D warnings
    cargo clippy {{benches}} --all-targets --all-features -- -D warnings
    cargo clippy {{dist}} --all-targets --all-features -- -D warnings

# Build every target, benches and examples included: post-monomorphization checks (const assertions in generic
# code) are evaluated only by a real build, not by clippy or by building the tests.
build:
    cargo build --workspace --all-targets --all-features
    cargo build {{benches}} --all-targets --all-features
    cargo build {{dist}} --all-targets --all-features

# Build the docs, warnings as errors.
doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --all-features
    RUSTDOCFLAGS="-D warnings" cargo doc -p pinc --no-default-features --no-deps
    RUSTDOCFLAGS="-D warnings" cargo doc {{dist}} --no-deps

# Build every no_std crate for a microcontroller and for wasm, then link a program with no allocator for each target.
# The program (tests/noalloc) runs an endpoint from caller storage, a handshake and a stream between two endpoints in
# one program, so a crate it reaches that asks for the heap fails the link. It does not cover membership, broadcast,
# reconcile or the node crate, which still need an allocator (pinc#640). The facade and the keystore build for the
# targets too, but they need an allocator as well, so the no-allocator program does not cover them. The targets without
# compare-and-swap build the program's crates (wire, crypto, security, transport, core) and pinc-table.
no-std:
    list=$(cargo metadata --no-deps --format-version 1 | python3 -c 'import json,sys; print(" ".join(p["name"] for p in json.load(sys.stdin)["packages"] if "no_std" in (p.get("keywords") or [])))'); \
    for c in pinc pinc-keystore; do \
        case " $list " in *" $c "*) ;; *) echo "no-std: $c is not in the list of crates built for the targets; give its manifest the no_std keyword" >&2; exit 1;; esac; \
    done; \
    for c in $list; do \
        for t in {{no_std_targets}}; do cargo build -q -p "$c" --no-default-features --target "$t"; done; \
    done
    for t in {{cas_less_targets}}; do cargo build -q -p pinc-table --no-default-features --target "$t"; done
    for t in {{no_std_targets}} {{cas_less_targets}}; do cargo build -q -p pinc-noalloc --target "$t"; done

# Fail if any build script of the library's workspace compiled C (run after a build; checks cargo's real target
# directory). The comparators' C code builds in the benchmarks' own workspace and directory, never here. A build
# script's output directory is the `out` beside the `run` directory of its run: every other `out` under `build/` holds
# what the compiler itself wrote for a crate, its object files among it.
pure:
    dir=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])'); \
    [ -d "$dir" ] || { echo "pure: no build output in $dir; build first" >&2; exit 1; }; \
    runs=$(find "$dir" -path '*/build/*' -type d -name run -printf '%h/out\n'); \
    [ -n "$runs" ] || { echo "pure: no build script has run in $dir; build first" >&2; exit 1; }; \
    ! find $runs \( -name '*.o' -o -name '*.a' -o -name '*.so' -o -name '*.obj' \) 2>/dev/null | grep . \
        || { echo "a build script compiled C (listed above); PINC is pure Rust" >&2; exit 1; }

# Measure PINC against iroh and rust-libp2p on this machine (loopback, then netem-shaped); writes benches/results/.
# Run it on the benchmark host with nothing else running: PINC_JOB_EXCLUSIVE=1 pinc-job just compare. Needs sudo and tc.
compare *args:
    RUSTFLAGS="{{native}}" python3 benches/compare.py --target-dir {{measure_target}} {{args}}

# Every test, hwenc included (the TPM tests need `swtpm`). Extra arguments go to nextest.
test *args:
    cargo nextest run --workspace --all-features --profile ci {{args}}
    cargo nextest run -p pinc --no-default-features --lib --profile ci {{args}}

# The stack tests in an application's debug build: every crate at opt-level 0 (`--cargo-profile` is cargo's profile,
# nextest's own `--profile` is its configuration).
unoptimised *args:
    cargo nextest run --cargo-profile unoptimised -p pinc-tests --test relay_stack {{args}}

# The core's own tests with its tables at the sizes of a small device (`pinc-core`, `sizes`), in a build directory of
# their own: the sizes are the compiler's environment, and a build with them is another build.
sizes *args:
    PINC_EVENT_BASE=128 PINC_LEDGER_ENTRIES=32 PINC_SUBS_SEEN=32 PINC_PEER_RTTS=16 PINC_PREKEY_PEERS=16 \
    PINC_REJOIN_ADDRS=16 PINC_MAX_DATAGRAM=1500 cargo nextest run -p pinc-core --target-dir target/sizes {{args}}

# The distributed harness's own tests (the orchestration logic; no root, no Docker).
test-distributed *args:
    cargo nextest run {{dist}} {{args}}

# The distributed harness end to end on containers of this machine (needs Docker and sudo): a two-node scenario, and
# hole punching through port-restricted and symmetric home routers. One run at a time: each takes the CPUs it plans.
e2e:
    cargo nextest run {{dist}} --run-ignored only --test-threads 1 -E 'binary(e2e)'

# The distributed harness: `just distributed run distributed/scenarios/wan.toml`, `just distributed clean`. A
# measurement wants an otherwise idle machine. Results go to distributed/results/.
distributed *args:
    RUSTFLAGS="{{native}}" cargo run -q --release --manifest-path distributed/Cargo.toml --target-dir {{measure_target}} -- {{args}}

# Every test without the hwenc feature, for machines without `swtpm`.
test-default *args:
    cargo nextest run --workspace --profile ci {{args}}

# Documentation examples.
doctest:
    cargo test --workspace --doc --all-features -q

# Lean proofs, TLC model checking, trace validation and model-based tests of the Rust code. The models with a file under
# proofs/tla/quick/ are checked over the smaller bounds of that file, so this takes minutes.
proofs:
    scripts/proofs.sh

# The same with every model over its full bounds (the ones docs/proofs/properties.md states). Hours of processor time.
proofs-deep:
    scripts/proofs.sh deep

# Record the trace tests under fresh seeds and replay them in the Lean model until a mismatch: `just trace-soak -n 20`.
trace-soak *args:
    scripts/trace-soak.sh {{args}}

# Coverage of the library crates under the trace tests only, and the modelled functions' uncovered lines; BRANCH=1 adds branches (nightly).
trace-cov:
    scripts/trace-cov.sh

# Only the Lean proofs.
lean:
    cd proofs/lean && lake build

# Micro benchmarks. Extra arguments go to criterion, e.g. `just bench -- verif`.
bench *args:
    cargo bench {{benches}} {{args}}

# Install the pinned TLA+ tools the proofs use (checksums verified) and a `tlc` wrapper in ~/.local/bin.
# vertexia: the 1.8.0 jar comes from upstream's pre-release tag, whose file is replaced with each new build, so its
# checksum fails after the next one: re-pin the name and checksum then; a mirror of the pinned jar would end that.
tla-tools:
    mkdir -p "{{tla_home}}" "$HOME/.local/bin"
    just _fetch "{{tla_home}}/tla2tools.jar" https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar 936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88
    just _fetch "{{tla_home}}/tla2tools-2026.11.19.jar" https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar fdffef247f563ef6edbfd44958d2a82db79e7564e07cb673262d896353fa6713
    just _fetch "{{tla_home}}/CommunityModules-deps-202611060952.jar" https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps.jar a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb
    printf '#!/usr/bin/env bash\nexec java -XX:+UseParallelGC -cp "%s/tla2tools.jar" tlc2.TLC "$@"\n' "{{tla_home}}" > "$HOME/.local/bin/tlc"
    chmod +x "$HOME/.local/bin/tlc"

_fetch path url sha:
    [ -f "{{path}}" ] || curl -fsSL -o "{{path}}" "{{url}}"
    if command -v sha256sum >/dev/null; then sum="sha256sum"; else sum="shasum -a 256"; fi; \
    echo "{{sha}}  {{path}}" | $sum -c --quiet || { echo "{{path}} does not match its pinned checksum; delete it and run just tla-tools again" >&2; exit 1; }
