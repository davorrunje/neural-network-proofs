#!/usr/bin/env bash
set -euo pipefail

# The host's SSH agent (e.g. Secretive on macOS) is forwarded into the container
# by the VS Code Dev Containers extension, so the signing key is available for
# signing operations here. The ~/.gitconfig copied in from the host, however,
# points user.signingkey at a host path (/Users/<you>/.ssh/...) that does not
# exist in the container. We materialise a public-key file from the forwarded
# agent and repoint user.signingkey at it so `git commit -S` works in-container.
#
# This runs as postStartCommand (every start) because the container home is not
# persisted across rebuilds and the host gitconfig may be re-copied on start.

# No forwarded agent / no keys: leave signing config untouched (e.g. headless
# runs with no agent). Commits then simply won't be signed.
if ! ssh-add -L >/dev/null 2>&1; then
  echo "setup-git-signing: no SSH agent keys available; leaving signing config unchanged."
  exit 0
fi

agent_keys="$(ssh-add -L)"
signers="$HOME/.ssh/allowed_signers"
chosen=""

# Prefer the agent key whose key data is listed in allowed_signers (the key git
# is configured to trust), so the right one is picked when the agent holds many.
if [ -f "$signers" ]; then
  while IFS= read -r key; do
    keydata="$(printf '%s' "$key" | awk '{print $2}')"
    if [ -n "$keydata" ] && grep -qF "$keydata" "$signers"; then
      chosen="$key"
      break
    fi
  done <<< "$agent_keys"
fi

# Fall back to the first agent key.
if [ -z "$chosen" ]; then
  chosen="$(printf '%s\n' "$agent_keys" | head -1)"
fi

mkdir -p "$HOME/.ssh"
printf '%s\n' "$chosen" > "$HOME/.ssh/signing_key.pub"
chmod 644 "$HOME/.ssh/signing_key.pub"

git config --global gpg.format ssh
git config --global user.signingkey "$HOME/.ssh/signing_key.pub"

echo "setup-git-signing: signing with $(printf '%s' "$chosen" | awk '{print $1, $3}')."
