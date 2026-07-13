#!/usr/bin/env bash
# Backend-aware verification ladder (design spec §6). Run inside the container.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/common.sh"
backend="${LEANSTRAL_BACKEND:?set LEANSTRAL_BACKEND=local|api}"
port="${LLAMA_PORT:-8080}"
case "$backend" in local|api) ;; *) log "invalid backend: $backend"; exit 2 ;; esac

check() { log "CHECK: $1"; }

if [ "$backend" = "local" ]; then
  check "GPUs visible"; nvidia-smi -L
  check "llama-server healthy"
  curl -sf "http://127.0.0.1:${port}/health" >/dev/null
  check "chat completion returns tokens"
  curl -sf "http://127.0.0.1:${port}/v1/chat/completions" \
    -H 'Content-Type: application/json' \
    -d '{"model":"leanstral-1.5","messages":[{"role":"user","content":"2+2?"}]}' \
    | grep -q '"choices"'
else
  check "MISTRAL_API_KEY set"; [ -n "${MISTRAL_API_KEY:-}" ]
  check "Mistral endpoint reachable"
  curl -sf https://api.mistral.ai/v1/models \
    -H "Authorization: Bearer ${MISTRAL_API_KEY}" | grep -q '"data"'
fi

check "lean-lsp-mcp launches"
timeout 60 uvx lean-lsp-mcp --help >/dev/null 2>&1 \
  || { log "note: --help may not exist; confirming import"; \
       timeout 60 uvx --from lean-lsp-mcp python -c "import lean_lsp_mcp" ; }

check "repo sorry-free gate"
# Standalone pipeline (not left of &&) so pipefail+set -e abort on a broken
# gate or a failing `lake env lean`; the success log runs only if grep matched.
( . "$HOME/.elan/env" && lake env lean scripts/check_sorry_free.lean ) \
  | grep -q "propext"
log "axioms clean"

log "ALL CHECKS PASSED ($backend)"
