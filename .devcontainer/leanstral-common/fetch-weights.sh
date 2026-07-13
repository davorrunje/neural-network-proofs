#!/usr/bin/env bash
# Ensure the GGUF for <quant> exists in $LEANSTRAL_MODELS_DIR.
#   q4_k_m -> direct HF download of the community Q4_K_M GGUF.
#   q5_k_m/q8_0 -> download BF16 repo once, convert to F16 GGUF, then quantize.
# Idempotent; set LEANSTRAL_FETCH_DRYRUN=1 to print the plan without acting.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/common.sh"

Q4_REPO="Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF"
BF16_REPO="sahilchachra/Leanstral-1.5-119B-A6B-BF16"
LLAMA_DIR="${LLAMA_CPP_DIR:-/opt/llama.cpp}"

quant="${1:?usage: fetch-weights.sh <q4_k_m|q5_k_m|q8_0>}"
fname="$(leanstral_gguf_filename "$quant")"    # exits 2 on unknown quant
target="$LEANSTRAL_MODELS_DIR/$fname"
dry="${LEANSTRAL_FETCH_DRYRUN:-0}"

run() { if [ "$dry" = "1" ]; then log "[dry-run] $*"; else log "$*"; "$@"; fi; }

mkdir -p "$LEANSTRAL_MODELS_DIR"
if [ -f "$target" ]; then
  log "weights already present: $target"
  exit 0
fi

hf_token_args=()
[ -n "${HF_TOKEN:-}" ] && hf_token_args=(--token "$HF_TOKEN")

if [ "$quant" = "q4_k_m" ]; then
  log "fetching Q4_K_M (~65GB) from $Q4_REPO"
  run hf download "$Q4_REPO" "$fname" \
    --local-dir "$LEANSTRAL_MODELS_DIR" "${hf_token_args[@]}"
else
  bf16_dir="$LEANSTRAL_MODELS_DIR/bf16-src"
  f16_gguf="$LEANSTRAL_MODELS_DIR/Leanstral-1.5-119B-A6B-F16.gguf"
  qtype="$([ "$quant" = "q5_k_m" ] && echo Q5_K_M || echo Q8_0)"
  log "converting $quant: BF16 base (~238GB) -> F16 GGUF -> llama-quantize $qtype"
  run hf download "$BF16_REPO" --local-dir "$bf16_dir" "${hf_token_args[@]}"
  run python3 "$LLAMA_DIR/convert_hf_to_gguf.py" "$bf16_dir" \
    --outfile "$f16_gguf" --outtype f16
  run "$LLAMA_DIR/build/bin/llama-quantize" "$f16_gguf" "$target" "$qtype"
fi

if [ "$dry" != "1" ]; then
  [ -f "$target" ] || { log "ERROR: expected $target after fetch"; exit 1; }
  log "weights ready: $target"
fi
