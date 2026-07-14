#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COMMON="$REPO_ROOT/.devcontainer/leanstral-common"
: "${LEANSTRAL_QUANT:?LEANSTRAL_QUANT must be set by the flavor}"

# Claim the ~/.claude config volume for the runtime user (see script header).
bash "$COMMON/fix-claude-volume-perms.sh"

git config --global commit.gpgsign false
git config --global tag.gpgsign false

bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache

command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh
"$HOME/.local/bin/uv" tool install mistral-vibe
# Note: `hf` (huggingface CLI) is baked into Dockerfile.local (Task 4), so no
# install needed here; fetch-weights.sh below relies on it.

# vibe reads $VIBE_HOME/config.toml (default ~/.vibe/config.toml), NOT the repo's
# ./.vibe/config.toml — the latter is only merged as a project layer when vibe runs from
# the repo root. Write the local config to the global path so plain `vibe` works from any
# directory with no Mistral fallback (the generated config has only the local provider);
# also keep the repo copy for project-root runs.
VIBE_HOME_DIR="${VIBE_HOME:-$HOME/.vibe}"
mkdir -p "$VIBE_HOME_DIR"
bash "$COMMON/gen-vibe-config.sh" local "$VIBE_HOME_DIR/config.toml"
bash "$COMMON/gen-vibe-config.sh" local "$REPO_ROOT/.vibe/config.toml"

# Install the custom `lean-local` agent into $VIBE_HOME so `vibe --agent lean-local`
# (and plain `vibe`, via default_agent) runs against the local server. vibe's builtin
# `lean` agent hardwires the Mistral-cloud endpoint and cannot be used locally.
VIBE_AGENTS_DIR="$VIBE_HOME_DIR/agents"
mkdir -p "$VIBE_AGENTS_DIR"
sed "s/__LLAMA_PORT__/${LLAMA_PORT:-8080}/g" \
  "$COMMON/lean-local.agent.toml" > "$VIBE_AGENTS_DIR/lean-local.toml"

# The host bind-mount dir may be auto-created root-owned by dockerd; claim it
# for the vscode user so fetch-weights.sh can write the (large) GGUF files.
MODELS_DIR="${LEANSTRAL_MODELS_DIR:-/models/leanstral}"
if [ -d "$MODELS_DIR" ] && [ ! -w "$MODELS_DIR" ]; then
  sudo chown "$(id -u):$(id -g)" "$MODELS_DIR" || true
fi

# Fetch (or convert) the GGUF for this flavor's quant into the bind mount.
bash "$COMMON/fetch-weights.sh" "$LEANSTRAL_QUANT"

# Ensure the local server is (re)started on every interactive shell, not just on
# a full devcontainer attach: postStartCommand does not fire on a plain
# `docker start`, so relying on it alone leaves vibe pointed at a dead endpoint
# after such a restart. ensure-llama-server.sh is idempotent and non-blocking, so
# this is a cheap no-op once the server is up. Marker-guarded to stay idempotent
# across repeated onCreate runs.
BASHRC="$HOME/.bashrc"
MARKER="# >>> leanstral ensure-llama-server >>>"
if ! grep -qF "$MARKER" "$BASHRC" 2>/dev/null; then
  {
    echo ""
    echo "$MARKER"
    echo "[ -x \"$COMMON/ensure-llama-server.sh\" ] && \\"
    echo "  bash \"$COMMON/ensure-llama-server.sh\" >/dev/null 2>&1 || true"
    echo "# <<< leanstral ensure-llama-server <<<"
  } >> "$BASHRC"
fi

echo "Leanstral local ($LEANSTRAL_QUANT) provisioned. Server auto-starts on"
echo "attach and on every new shell (idempotent)."
