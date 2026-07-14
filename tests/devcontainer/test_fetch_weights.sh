#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="$HERE/../../.devcontainer/leanstral-common/fetch-weights.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export LEANSTRAL_MODELS_DIR="$TMP"
fail=0

# 1) already-present short-circuits (no network, no dry-run needed)
touch "$TMP/Leanstral-1.5-119B-A6B-Q4_K_M.gguf"
if ! out="$(bash "$SCRIPT" q4_k_m 2>&1)"; then
  echo "FAIL present: nonzero exit"; fail=1
fi
echo "$out" | grep -qi "already present" || { echo "FAIL present: $out"; fail=1; }

# 2) dry-run for a missing q4 prints the HF download plan, creates nothing
rm -f "$TMP"/*.gguf
out="$(LEANSTRAL_FETCH_DRYRUN=1 bash "$SCRIPT" q4_k_m 2>&1)"
echo "$out" | grep -q "Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF" \
  || { echo "FAIL dryrun-q4: $out"; fail=1; }
[ -e "$TMP"/*.gguf ] 2>/dev/null && { echo "FAIL dryrun-q4 created file"; fail=1; }

# 3) dry-run for q5 mentions BF16 download + convert + quantize
out="$(LEANSTRAL_FETCH_DRYRUN=1 bash "$SCRIPT" q5_k_m 2>&1)"
echo "$out" | grep -q "sahilchachra/Leanstral-1.5-119B-A6B-BF16" \
  || { echo "FAIL dryrun-q5 bf16: $out"; fail=1; }
echo "$out" | grep -qi "llama-quantize" || { echo "FAIL dryrun-q5 quant: $out"; fail=1; }

# 4) unknown quant exits 2
set +e
bash "$SCRIPT" bogus >/dev/null 2>&1; [ "$?" -eq 2 ] \
  || { echo "FAIL unknown-quant exit code"; fail=1; }
set -e

[ "$fail" -eq 0 ] && echo "PASS test_fetch_weights" \
  || { echo "test_fetch_weights FAILED"; exit 1; }
