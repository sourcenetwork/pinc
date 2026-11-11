# VINC tasks. `just` lists them; `just gate` runs everything a change must pass; CI runs the same recipes.

set shell := ["bash", "-euo", "pipefail", "-c"]

tla_home := env_var_or_default("TLA_HOME", env_var("HOME") / ".local/share/tla")
no_std_targets := "thumbv7em-none-eabihf wasm32-unknown-unknown"
# The benchmarks and the distributed harness are workspaces of their own (the libraries they measure VINC against,
# their runtime and their C code stay out of the library's graph). They build into one directory beside the library's,
# so the library's build output, which `pure` scans, never holds the comparators' C code.
target := env_var_or_default("CARGO_TARGET_DIR", justfile_directory() / "target")
harness_target := target + "-harness"
benches := "--manifest-path benches/Cargo.toml --target-dir " + harness_target
dist := "--manifest-path distributed/Cargo.toml --target-dir " + harness_target

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
gate: checks test test-distributed doctest proofs
    @echo "gate: ok"

# Every static check: dependency rules, format, lints, docs, no_std builds, pure Rust.
checks: deps hygiene fmt-check clippy build doc no-std pure

# Dependency rules: declared only at the root, one version, unsafe forbidden, no async runtime, no C.
deps:
    python3 scripts/deps.py

# Public-repository hygiene: no internal project names and no em-dash or en-dash in any tracked file.
hygiene:
    #!/usr/bin/env bash
    set -euo pipefail
    names='finalist|grader|vinc_experiments|eurekagent|roster_settle|kindling|scramdb'
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
    RUSTDOCFLAGS="-D warnings" cargo doc {{dist}} --no-deps

# Build every no_std crate for a microcontroller and for wasm.
no-std:
    for c in $(cargo metadata --no-deps --format-version 1 | python3 -c 'import json,sys; print(" ".join(p["name"] for p in json.load(sys.stdin)["packages"] if "no_std" in (p.get("keywords") or [])))'); do \
        for t in {{no_std_targets}}; do cargo build -q -p "$c" --no-default-features --target "$t"; done; \
    done

# Fail if any build script of the library's workspace compiled C (run after a build; checks cargo's real target
# directory). The comparators' C code builds in the benchmarks' own workspace and directory, never here.
pure:
    dir=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])'); \
    [ -d "$dir" ] || { echo "pure: no build output in $dir; build first" >&2; exit 1; }; \
    ! find "$dir" -path '*/build/*' \( -name '*.o' -o -name '*.a' -o -name '*.so' -o -name '*.obj' \) | grep . \
        || { echo "a build script compiled C (listed above); VINC is pure Rust" >&2; exit 1; }

# Measure VINC against iroh and rust-libp2p on this machine (loopback, then netem-shaped); writes benches/results/.
# Run it on the benchmark host with nothing else running: VINC_JOB_EXCLUSIVE=1 vinc-job just compare. Needs sudo and tc.
compare *args:
    python3 benches/compare.py --target-dir {{harness_target}} {{args}}

# Every test, hwenc included (the TPM tests need `swtpm`). Extra arguments go to nextest.
test *args:
    cargo nextest run --workspace --all-features --profile ci {{args}}

# The distributed harness's own tests (the orchestration logic; no root, no Docker).
test-distributed *args:
    cargo nextest run {{dist}} {{args}}

# The distributed harness end to end: a two-node scenario on containers of this machine (needs Docker and sudo).
e2e:
    cargo nextest run {{dist}} --run-ignored only

# The distributed harness: `just distributed run distributed/scenarios/wan.toml`, `just distributed clean`. A
# measurement wants an otherwise idle machine. Results go to distributed/results/.
distributed *args:
    cargo run -q --release {{dist}} -- {{args}}

# Every test without the hwenc feature, for machines without `swtpm`.
test-default *args:
    cargo nextest run --workspace --profile ci {{args}}

# Documentation examples.
doctest:
    cargo test --workspace --doc --all-features -q

# Lean proofs, TLC model checking and trace validation of the Rust code.
proofs:
    scripts/proofs.sh

# Only the Lean proofs.
lean:
    cd proofs/lean && lake build

# Micro benchmarks. Extra arguments go to criterion, e.g. `just bench -- verif`.
bench *args:
    cargo bench {{benches}} {{args}}

# Install the pinned TLA+ tools the proofs use (checksums verified) and a `tlc` wrapper in ~/.local/bin.
tla-tools:
    mkdir -p "{{tla_home}}" "$HOME/.local/bin"
    just _fetch "{{tla_home}}/tla2tools.jar" https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar 936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88
    just _fetch "{{tla_home}}/tla2tools-2026.11.06.jar" https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar e1f11b75c4b5bc4478ba0ac5cb6ae28e40a01b0016bc33e0aa97da22dfdbcd7f
    just _fetch "{{tla_home}}/CommunityModules-deps-202611060952.jar" https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps.jar a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb
    printf '#!/usr/bin/env bash\nexec java -XX:+UseParallelGC -cp "%s/tla2tools.jar" tlc2.TLC "$@"\n' "{{tla_home}}" > "$HOME/.local/bin/tlc"
    chmod +x "$HOME/.local/bin/tlc"

_fetch path url sha:
    [ -f "{{path}}" ] || curl -fsSL -o "{{path}}" "{{url}}"
    if command -v sha256sum >/dev/null; then sum="sha256sum"; else sum="shasum -a 256"; fi; \
    echo "{{sha}}  {{path}}" | $sum -c --quiet || { echo "{{path}} does not match its pinned checksum; delete it and run just tla-tools again" >&2; exit 1; }
