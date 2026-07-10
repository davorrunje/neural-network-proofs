#!/usr/bin/env bash
set -euo pipefail

# Ensure system dependencies are present (base image runs as the `vscode`
# user with passwordless sudo).
if ! command -v curl >/dev/null 2>&1 || ! command -v git >/dev/null 2>&1; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends curl git
fi

# This project does not sign commits. Turn signing off explicitly so git never
# tries to invoke gpg. (gpg itself is removed from the image at build time by
# the local ./features/no-gpg feature, which is what stops VS Code from
# forwarding the host gpg-agent and crashing on connect; this is the git-level
# backstop.)
git config --global commit.gpgsign false
git config --global tag.gpgsign false

# Install elan (Lean's toolchain manager) if not already present.
# --default-toolchain none: the project's lean-toolchain file decides the
# Lean version, so we do not install a default here.
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
fi

# Install uv (Astral) if not already present. uv provides `uvx`, used to run
# the lean-lsp-mcp server configured in .mcp.json.
if ! command -v uv >/dev/null 2>&1 && [ ! -x "$HOME/.local/bin/uv" ]; then
  curl -LsSf https://astral.sh/uv/install.sh | sh
fi

# Make elan and uv available in future interactive and login shells.
for profile in "$HOME/.profile" "$HOME/.bashrc"; do
  if ! grep -q '.elan/env' "$profile" 2>/dev/null; then
    echo '. "$HOME/.elan/env"' >> "$profile"
  fi
  if ! grep -q '.local/bin' "$profile" 2>/dev/null; then
    echo 'export PATH="$HOME/.local/bin:$PATH"' >> "$profile"
  fi
done

echo "elan installed:"
. "$HOME/.elan/env"
elan --version
echo "uv installed:"
export PATH="$HOME/.local/bin:$PATH"
uv --version
