#!/usr/bin/env bash
# Idempotently ensure llama-server is running for the local Leanstral backend.
#
# Safe to call repeatedly AND concurrently (flock + process guard), and
# non-blocking (backgrounds the actual launch and returns immediately). Called
# both from the devcontainer postStartCommand and from every interactive shell
# (~/.bashrc), so the server comes up no matter how the container was
# (re)started — postStartCommand does NOT fire on a plain `docker start` — and
# self-heals if the server ever dies.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
port="${LLAMA_PORT:-8080}"

# Only this flavor runs a local server; the API flavor talks to a remote endpoint.
[ "${LEANSTRAL_BACKEND:-local}" = "local" ] || exit 0

# Serialize concurrent callers (several terminals opening at once) so we never
# launch two servers during the model-load window — that would clash on the port
# and double the VRAM footprint. Non-blocking: if someone else holds the lock,
# they are already handling startup, so just return.
exec 9>/tmp/llama-ensure.lock
flock -n 9 || exit 0

# Already loading or serving? (`llama-server` is the binary's process name; the
# *.sh helpers show up as `bash`, so `-x` won't false-match them.) The load takes
# ~a minute, during which the process is up but /health is not yet ok — the
# pgrep guard covers that window; the health check covers a running-but-idle server.
pgrep -x llama-server >/dev/null 2>&1 && exit 0
curl -sf -m 2 "http://127.0.0.1:${port}/health" >/dev/null 2>&1 && exit 0

# Launch in the background. start-llama-server.sh does its own foreground
# health-wait (up to ~6 min), so detach it and return right away.
nohup bash "$HERE/start-llama-server.sh" >/tmp/llama-start.log 2>&1 &
