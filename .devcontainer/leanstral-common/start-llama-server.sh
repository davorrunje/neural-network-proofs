#!/usr/bin/env bash
# Launch llama-server for the selected quant and wait until healthy.
# Backgrounds the server; intended to be called from postStartCommand.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/common.sh"

quant="${LEANSTRAL_QUANT:?LEANSTRAL_QUANT must be set (q4_k_m|q5_k_m|q8_0)}"
fname="$(leanstral_gguf_filename "$quant")"
model="$LEANSTRAL_MODELS_DIR/$fname"
port="${LLAMA_PORT:-8080}"
bin="${LLAMA_CPP_DIR:-/opt/llama.cpp}/build/bin/llama-server"

# The GGUF's embedded chat template raises a Jinja exception on valid tool-calling
# agent histories (its alternating-roles guard miscounts across tool call/result
# turns), which breaks Vibe with a 500. Override it with a patched copy that drops
# that guard (render logic unchanged). Fall back to the embedded template if the
# file is somehow missing.
tmpl="$HERE/leanstral-chat-template.jinja"
tmpl_args=()
[ -f "$tmpl" ] && tmpl_args=(--chat-template-file "$tmpl")

[ -f "$model" ] || { log "ERROR: weights missing: $model (run fetch-weights.sh)"; exit 1; }

# Already up? (idempotent across container restarts)
if curl -sf "http://127.0.0.1:${port}/health" >/dev/null 2>&1; then
  log "llama-server already healthy on :$port"; exit 0
fi

log "starting llama-server: $fname (tensor-split=${LLAMA_TENSOR_SPLIT:-0.42,0.58},"
log "  n-cpu-moe=${LLAMA_N_CPU_MOE:-24}, ctx=${LLAMA_CTX:-131072})"
nohup "$bin" \
  --model "$model" \
  --alias leanstral-1.5 \
  --host 127.0.0.1 --port "$port" \
  --n-gpu-layers 999 \
  --split-mode layer \
  --tensor-split "${LLAMA_TENSOR_SPLIT:-0.42,0.58}" \
  --n-cpu-moe "${LLAMA_N_CPU_MOE:-24}" \
  --ctx-size "${LLAMA_CTX:-131072}" \
  --jinja \
  "${tmpl_args[@]}" \
  >/tmp/llama-server.log 2>&1 &

log "waiting for /health ..."
for i in $(seq 1 180); do
  if curl -sf "http://127.0.0.1:${port}/health" >/dev/null 2>&1; then
    log "llama-server healthy on :$port"; exit 0
  fi
  sleep 2
done
log "ERROR: llama-server did not become healthy; see /tmp/llama-server.log"
tail -n 40 /tmp/llama-server.log >&2 || true
exit 1
