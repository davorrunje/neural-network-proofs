#!/usr/bin/env bash
# Shared helpers for the Leanstral dev container flavors. Source, don't exec.

: "${LEANSTRAL_MODELS_DIR:=/models/leanstral}"

log() { printf '>>> %s\n' "$*" >&2; }

# Map a quant id to its canonical GGUF filename inside LEANSTRAL_MODELS_DIR.
leanstral_gguf_filename() {
  case "$1" in
    q4_k_m) echo "Leanstral-1.5-119B-A6B-Q4_K_M.gguf" ;;
    q5_k_m) echo "Leanstral-1.5-119B-A6B-Q5_K_M.gguf" ;;
    q8_0)   echo "Leanstral-1.5-119B-A6B-Q8_0.gguf" ;;
    *) log "unknown quant: $1 (want q4_k_m|q5_k_m|q8_0)"; return 2 ;;
  esac
}
