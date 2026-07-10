#!/usr/bin/env bash
# Local dev container feature. Runs as root at image-build time, ordered AFTER
# the node/github-cli/claude-code features (see installsAfter in
# devcontainer-feature.json) — those need `gpg` during their own build
# (github-cli does `gpg --recv-keys`), so gpg must still be present then.
#
# Why: the base image ships gpg. Whenever a `gpg` binary exists in the
# container, VS Code forwards the host gpg-agent and copies the host GnuPG
# keyring in on every connect. On a host whose keyring is empty or keybox-only
# (no legacy pubring.gpg) that copy crashes: "Aborted (core dumped)", exit 134,
# surfaced as a "container startup failed" popup. This project does not sign
# commits, so we simply drop gpg from the finished image — the same reason the
# sibling mononet dev container (no gpg installed) never hits this.
#
# apt is unaffected: it verifies package signatures with the separate `gpgv`.
set -e
export DEBIAN_FRONTEND=noninteractive

# Remove per-package with `|| true` so a name absent on some base-image revision
# does not abort the rest (apt aborts the whole command on an unknown package).
for pkg in gnupg gnupg2 gpg gpg-agent gpgsm dirmngr; do
  apt-get remove -y --purge "$pkg" >/dev/null 2>&1 || true
done
apt-get autoremove -y >/dev/null 2>&1 || true
rm -rf /var/lib/apt/lists/*

if command -v gpg >/dev/null 2>&1; then
  echo "no-gpg: WARNING: gpg is still on PATH ($(command -v gpg)); VS Code may still attempt GPG forwarding." >&2
else
  echo "no-gpg: gpg removed; VS Code GPG-agent forwarding will be skipped."
fi
