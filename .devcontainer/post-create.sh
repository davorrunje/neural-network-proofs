#!/usr/bin/env bash
set -euo pipefail

# elan was installed by on-create.sh; put it on PATH for this script.
. "$HOME/.elan/env"

# Download the prebuilt Mathlib cache (fast) instead of compiling it from
# source (~1hr), then build the project. elan resolves the Lean version from
# ./lean-toolchain on first invocation.
lake exe cache get
lake build

# ~/.claude is a container-private named volume (see devcontainer.json) so Claude
# Code session history, memory, login/auth, and installed plugins persist across
# rebuilds. Docker initialises named volumes root-owned, so claim the mount point
# for the vscode user before anything writes to it — idempotent: only acts when
# the dir exists and is not yet writable. Without this the first `claude plugin …`
# call below fails with "Permission denied".
if [ -d "$HOME/.claude" ] && [ ! -w "$HOME/.claude" ]; then
  sudo chown "$(id -u):$(id -g)" "$HOME/.claude" || true
fi

# Auto-install the Claude Code plugins this repo declares
# (.devcontainer/claude-plugins.txt) — notably superpowers and its brainstorming
# skill. Best-effort: the script always exits 0 and never fails the build.
echo ">>> provisioning Claude Code plugins"
bash .devcontainer/provision-claude-plugins.sh

echo "Lean + Mathlib build complete."
