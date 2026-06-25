#!/usr/bin/env bash
set -euo pipefail

# elan was installed by on-create.sh; put it on PATH for this script.
. "$HOME/.elan/env"

# Download the prebuilt Mathlib cache (fast) instead of compiling it from
# source (~1hr), then build the project. elan resolves the Lean version from
# ./lean-toolchain on first invocation.
lake exe cache get
lake build

# ~/.claude is a host bind mount (see devcontainer.json) so Claude Code session
# history, memory, login/auth, and installed plugins persist across container
# rebuilds. Ensure it is writable by the vscode user regardless of host ownership.
sudo chown -R vscode:vscode "$HOME/.claude" 2>/dev/null || true

echo "Lean + Mathlib build complete."
