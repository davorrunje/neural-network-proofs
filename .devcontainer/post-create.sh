#!/usr/bin/env bash
set -euo pipefail

# elan was installed by on-create.sh; put it on PATH for this script.
. "$HOME/.elan/env"

# Download the prebuilt Mathlib cache (fast) instead of compiling it from
# source (~1hr), then build the project. elan resolves the Lean version from
# ./lean-toolchain on first invocation.
lake exe cache get
lake build

echo "Lean + Mathlib build complete."
