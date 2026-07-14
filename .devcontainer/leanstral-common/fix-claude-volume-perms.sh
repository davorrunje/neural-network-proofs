#!/usr/bin/env bash
# ~/.claude is a named Docker volume (neural-network-proofs-claude-config) shared
# across the Leanstral flavors and persisted across rebuilds. A named volume can
# carry an owner UID that differs from the container's runtime user - e.g. seeded
# as root, or by a differently-numbered user on another machine - which makes
# Claude Code fail to create ~/.claude/session-env (EACCES). Claim it for the
# current user on every create so ownership is correct regardless of how the
# volume was seeded. Dockerfile.local also pins vscode to UID 1000 to remove the
# mismatch at the source; this is the cross-machine safety net.
set -euo pipefail
CLAUDE_DIR="${HOME}/.claude"
[ -d "$CLAUDE_DIR" ] || exit 0
if [ "$(stat -c '%u' "$CLAUDE_DIR")" != "$(id -u)" ]; then
  echo "Claiming $CLAUDE_DIR for $(id -un) ($(id -u):$(id -g))"
  sudo chown -R "$(id -u):$(id -g)" "$CLAUDE_DIR"
fi
