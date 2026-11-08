# VINC tasks. `just` lists them; `just gate` runs everything a change must pass; CI runs the same recipes.

set shell := ["bash", "-euo", "pipefail", "-c"]

tla_home := env_var_or_default("TLA_HOME", env_var("HOME") / ".local/share/tla")
no_std_targets := "thumbv7em-none-eabihf wasm32-unknown-unknown"

# List the recipes.
default:
    @just --list

# Everything a change must pass before it is pushed.
gate: checks test doctest proofs
    @echo "gate: ok"

# Every static check: dependency rules, format, lints, docs, no_std builds, pure Rust.
checks: deps fmt-check clippy doc no-std pure

# Dependency rules: declared only at the root, one version, unsafe forbidden, no async runtime, no C.
deps:
    python3 scripts/deps.py

# Format every crate.
fmt:
    cargo fmt --all

# Fail if any file is not formatted.
fmt-check:
    cargo fmt --all --check

# Lints on every target and feature, warnings as errors.
clippy:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

# Build the docs, warnings as errors.
doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --all-features

# Build every no_std crate for a microcontroller and for wasm.
no-std:
    for c in $(cargo metadata --no-deps --format-version 1 | python3 -c 'import json,sys; print(" ".join(p["name"] for p in json.load(sys.stdin)["packages"] if "no_std" in (p.get("keywords") or [])))'); do \
        for t in {{no_std_targets}}; do cargo build -q -p "$c" --no-default-features --target "$t"; done; \
    done

# Fail if any build script compiled C (run after a build; checks cargo's real target directory).
pure:
    dir=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])'); \
    [ -d "$dir" ] || { echo "pure: no build output in $dir; build first" >&2; exit 1; }; \
    ! find "$dir" -path '*/build/*' \( -name '*.o' -o -name '*.a' -o -name '*.so' -o -name '*.obj' \) | grep . \
        || { echo "a build script compiled C (listed above); VINC is pure Rust" >&2; exit 1; }

# Every test, hwenc included (the TPM tests need `swtpm`). Extra arguments go to nextest.
test *args:
    cargo nextest run --workspace --all-features --profile ci {{args}}

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
    cargo bench -p vinc-benches {{args}}

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
    echo "{{sha}}  {{path}}" | sha256sum -c --quiet || { echo "{{path}} does not match its pinned checksum; delete it and run just tla-tools again" >&2; exit 1; }
