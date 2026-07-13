#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/../../.devcontainer/leanstral-common/common.sh"

fail=0
assert_eq() { # $1 actual $2 expected $3 label
  if [ "$1" != "$2" ]; then echo "FAIL $3: got '$1' want '$2'"; fail=1; fi
}

assert_eq "$(leanstral_gguf_filename q4_k_m)" \
  "Leanstral-1.5-119B-A6B-Q4_K_M.gguf" q4
assert_eq "$(leanstral_gguf_filename q5_k_m)" \
  "Leanstral-1.5-119B-A6B-Q5_K_M.gguf" q5
assert_eq "$(leanstral_gguf_filename q8_0)" \
  "Leanstral-1.5-119B-A6B-Q8_0.gguf" q8

if leanstral_gguf_filename bogus 2>/dev/null; then
  echo "FAIL unknown-quant: expected nonzero exit"; fail=1
fi

[ "$fail" -eq 0 ] && echo "PASS test_common" || { echo "test_common FAILED"; exit 1; }
