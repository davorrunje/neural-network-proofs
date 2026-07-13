#!/usr/bin/env bash
# Launch the model server in the background so container attach isn't blocked
# by start-llama-server.sh's foreground health-wait. Log to /tmp/llama-start.log.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
nohup bash "$HERE/start-llama-server.sh" >/tmp/llama-start.log 2>&1 &
