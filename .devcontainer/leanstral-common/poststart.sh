#!/usr/bin/env bash
# Devcontainer postStartCommand: bring the model server up (idempotently,
# non-blocking) so container attach isn't blocked by the health-wait. The real
# work — and the concurrency/idempotency guards — live in ensure-llama-server.sh,
# which is also invoked from ~/.bashrc so the server survives restart paths that
# don't re-run this hook (e.g. a plain `docker start`).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec bash "$HERE/ensure-llama-server.sh"
