#!/usr/bin/env bash
set -euo pipefail

# This project does not sign commits. Turn signing off explicitly so git never
# tries to invoke gpg. (gpg itself is removed from the image at build time by
# the local ./features/no-gpg feature, which is what stops VS Code from
# forwarding the host gpg-agent and crashing on connect; this is the git-level
# backstop.)
git config --global commit.gpgsign false
git config --global tag.gpgsign false

# Install the full dev toolchain via the portable bootstrap so the devcontainer,
# Codespaces, and a host machine set up identically (scripts/setup-dev.sh).
# Skip the Mathlib cache + build here; post-create.sh runs those, preserving the
# onCreate (install) / postCreate (cache + build + plugins) split.
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache
