#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COMMON="$REPO_ROOT/.devcontainer/leanstral-common"
: "${LEANSTRAL_QUANT:?LEANSTRAL_QUANT must be set by the flavor}"

git config --global commit.gpgsign false
git config --global tag.gpgsign false

bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache

command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh
"$HOME/.local/bin/uv" tool install mistral-vibe
# Note: `hf` (huggingface CLI) is baked into Dockerfile.local (Task 4), so no
# install needed here; fetch-weights.sh below relies on it.

bash "$COMMON/gen-vibe-config.sh" local "$REPO_ROOT/.vibe/config.toml"

# Fetch (or convert) the GGUF for this flavor's quant into the bind mount.
bash "$COMMON/fetch-weights.sh" "$LEANSTRAL_QUANT"

echo "Leanstral local ($LEANSTRAL_QUANT) provisioned. Server starts on attach."
