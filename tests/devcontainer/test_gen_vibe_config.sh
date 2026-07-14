#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="$HERE/../../.devcontainer/leanstral-common/gen-vibe-config.sh"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fail=0
has() { grep -qF "$2" "$1" || { echo "FAIL missing in $3: $2"; fail=1; }; }

bash "$SCRIPT" local "$TMP/local.toml"
has "$TMP/local.toml" 'api_base = "http://127.0.0.1:8080/v1"' local
has "$TMP/local.toml" 'name = "leanstral-1.5"' local
has "$TMP/local.toml" 'enable_telemetry = false' local
has "$TMP/local.toml" 'enable_auto_update = false' local
has "$TMP/local.toml" 'args = ["lean-lsp-mcp"]' local
has "$TMP/local.toml" 'default_agent = "lean"' local

bash "$SCRIPT" api "$TMP/api.toml"
has "$TMP/api.toml" 'api_base = "https://api.mistral.ai/v1"' api
has "$TMP/api.toml" 'name = "leanstral-1-5"' api
has "$TMP/api.toml" 'args = ["lean-lsp-mcp"]' api

if bash "$SCRIPT" bogus "$TMP/x.toml" 2>/dev/null; then
  echo "FAIL bogus backend accepted"; fail=1
fi

[ "$fail" -eq 0 ] && echo "PASS test_gen_vibe_config" \
  || { echo "test_gen_vibe_config FAILED"; exit 1; }
