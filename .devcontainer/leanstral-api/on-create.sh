#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COMMON="$REPO_ROOT/.devcontainer/leanstral-common"

git config --global commit.gpgsign false
git config --global tag.gpgsign false

# Lean toolchain (shared bootstrap; skip cache+build here, mirror base container).
bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache

# uv + Mistral Vibe.
command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh
"$HOME/.local/bin/uv" tool install mistral-vibe

# Vibe config → repo-local .vibe/config.toml (api backend).
bash "$COMMON/gen-vibe-config.sh" api "$REPO_ROOT/.vibe/config.toml"

echo "Leanstral API flavor ready. Set MISTRAL_API_KEY, then: vibe --agent lean"
