#!/usr/bin/env bash
# The gate: every check must pass before a push. The steps live in the justfile (`just gate`); CI runs the same recipes.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v just >/dev/null || { echo "gate: just is not installed; install it (https://just.systems) and run again" >&2; exit 1; }
exec just gate
