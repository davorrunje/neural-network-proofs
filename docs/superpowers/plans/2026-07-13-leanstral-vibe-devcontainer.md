# Leanstral 1.5 + Mistral Vibe + MCP Dev Containers Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add four selectable dev container flavors (`api`, `local-q4`, `local-q5`, `local-q8`) that drive Mistral Vibe against Leanstral 1.5 with the lean-lsp MCP wired in, without changing the existing `Lean 4 + Mathlib` container.

**Architecture:** Three local flavors share one CUDA-12.8 `Dockerfile.local` that builds llama.cpp for Ampere+Blackwell and layers Vibe + lean-lsp-MCP on top of the repo's existing `setup-dev.sh` Lean toolchain; each flavor's `devcontainer.json` differs only by a quant env var. The API flavor is a thin client over the existing base image. Model weights live on a host bind-mount, fetched or converted on first start.

**Tech Stack:** Docker / devcontainers, NVIDIA CUDA 12.8, llama.cpp (`llama-server`, `llama-quantize`, `convert_hf_to_gguf.py`), `uv`/`mistral-vibe`, `uvx lean-lsp-mcp`, HuggingFace `hf` CLI, bash, TOML.

## Global Constraints

- **Design spec:** `docs/superpowers/specs/2026-07-13-leanstral-vibe-devcontainer-design.md` — the authority for all decisions below.
- **CUDA pin:** base image is exactly `nvidia/cuda:12.8.0-devel-ubuntu24.04`. Do NOT bump to 13.x (Blackwell MMQ segfault).
- **llama.cpp build flags (verbatim):** `-DGGML_CUDA=ON -DCMAKE_CUDA_ARCHITECTURES="86;120" -DGGML_CUDA_FORCE_CUBLAS=OFF`. `86` = RTX 3090 (Ampere), `120` = RTX 5090 (Blackwell).
- **Do not modify** the existing `.devcontainer/devcontainer.json`, `on-create.sh`, `post-create.sh`, or `scripts/setup-dev.sh`. Reuse `setup-dev.sh` by calling it.
- **HuggingFace repos (verbatim):** Q4_K_M GGUF = `Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF`; BF16 (for q5/q8 conversion) = `sahilchachra/Leanstral-1.5-119B-A6B-BF16`. No official GGUFs exist.
- **Weights path:** host `${HOME}/models/leanstral` → container `/models/leanstral` (bind mount, shared across local flavors).
- **Quant env values (verbatim):** `q4_k_m`, `q5_k_m`, `q8_0`.
- **llama-server model alias (verbatim):** `leanstral-1.5` (Vibe `[[models]].name` must match).
- **Vibe offline settings:** local flavors set `enable_telemetry = false` and `enable_auto_update = false`.
- **Line length:** shell/TOML/JSON — keep ≤ 100 columns to match repo style.
- **GPU/host-dependent verification** runs on the target Threadripper host (3090 + 5090, NVIDIA Container Toolkit installed), NOT in a Codespace/CI without GPUs. Each such step is marked `[HOST-ONLY]`.

---

## File Structure

```
.devcontainer/
  leanstral-common/
    Dockerfile.local          # CUDA 12.8 base; builds llama.cpp; installs uv/vibe/hf/lean toolchain
    fetch-weights.sh          # download (q4) or download-BF16+convert+quantize (q5/q8); idempotent
    start-llama-server.sh     # launch llama-server (tensor-split + MoE CPU offload) + health gate
    gen-vibe-config.sh        # generate .vibe/config.toml for a given backend (local|api)
    verify.sh                 # verification ladder (backend-aware)
    common.sh                 # shared bash helpers (logging, quant->filename map)
  leanstral-api/
    devcontainer.json         # thin client, base ubuntu image, backend=api
    on-create.sh              # setup-dev.sh + vibe install + gen-vibe-config api
  leanstral-local-q4/
    devcontainer.json         # Dockerfile.local, GPU passthrough, LEANSTRAL_QUANT=q4_k_m
    on-create.sh              # setup-dev.sh + fetch-weights + gen-vibe-config local
  leanstral-local-q5/
    devcontainer.json         # LEANSTRAL_QUANT=q5_k_m (else identical to q4)
  leanstral-local-q8/
    devcontainer.json         # LEANSTRAL_QUANT=q8_0 (else identical to q4)
  README-leanstral.md         # prerequisites, usage, verification, retuning
tests/devcontainer/
  test_common.sh              # unit tests for common.sh quant mapping
  test_fetch_weights.sh       # dry-run + idempotency tests for fetch-weights.sh
  test_gen_vibe_config.sh     # assert generated TOML for local + api backends
```

`on-create.sh` for the three local flavors is identical; q5/q8 each contain a one-line `on-create.sh` that `exec`s the q4 one via relative path, OR (chosen here) the local flavors all point their `onCreateCommand` at `../leanstral-common/*` scripts and pass the quant via `containerEnv`, so there is exactly one copy of the logic.

---

## Task 1: Shared bash helpers (`common.sh`)

**Files:**
- Create: `.devcontainer/leanstral-common/common.sh`
- Test: `tests/devcontainer/test_common.sh`

**Interfaces:**
- Produces: `leanstral_gguf_filename <quant>` → echoes the canonical GGUF filename for a quant (`q4_k_m|q5_k_m|q8_0`), exit 2 on unknown quant. `log <msg>` → stderr logger. `LEANSTRAL_MODELS_DIR` default `/models/leanstral`.

- [ ] **Step 1: Write the failing test**

Create `tests/devcontainer/test_common.sh`:

```bash
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
```

- [ ] **Step 2: Run test to verify it fails**

Run: `bash tests/devcontainer/test_common.sh`
Expected: FAIL — `common.sh: No such file or directory` (source fails).

- [ ] **Step 3: Write minimal implementation**

Create `.devcontainer/leanstral-common/common.sh`:

```bash
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
```

- [ ] **Step 4: Run test to verify it passes**

Run: `bash tests/devcontainer/test_common.sh`
Expected: `PASS test_common`

- [ ] **Step 5: Commit**

```bash
git add .devcontainer/leanstral-common/common.sh tests/devcontainer/test_common.sh
git commit -m "feat(devcontainer): add Leanstral common.sh quant->filename helper"
```

---

## Task 2: Weight provisioning (`fetch-weights.sh`)

**Files:**
- Create: `.devcontainer/leanstral-common/fetch-weights.sh`
- Test: `tests/devcontainer/test_fetch_weights.sh`

**Interfaces:**
- Consumes: `common.sh` (`leanstral_gguf_filename`, `log`, `LEANSTRAL_MODELS_DIR`).
- Produces: `fetch-weights.sh <quant>` ensures `$LEANSTRAL_MODELS_DIR/<filename>` exists. Honors `LEANSTRAL_FETCH_DRYRUN=1` (print planned actions, do nothing) and short-circuits when the file already exists. Reads optional `HF_TOKEN`. Exits 0 on success/already-present, 2 on unknown quant.

- [ ] **Step 1: Write the failing test**

Create `tests/devcontainer/test_fetch_weights.sh`:

```bash
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
bash "$SCRIPT" bogus >/dev/null 2>&1; [ "$?" -eq 2 ] \
  || { echo "FAIL unknown-quant exit code"; fail=1; }

[ "$fail" -eq 0 ] && echo "PASS test_fetch_weights" \
  || { echo "test_fetch_weights FAILED"; exit 1; }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `bash tests/devcontainer/test_fetch_weights.sh`
Expected: FAIL — script does not exist.

- [ ] **Step 3: Write minimal implementation**

Create `.devcontainer/leanstral-common/fetch-weights.sh`:

```bash
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
```

- [ ] **Step 4: Run test to verify it passes**

Run: `bash tests/devcontainer/test_fetch_weights.sh`
Expected: `PASS test_fetch_weights`

- [ ] **Step 5: [HOST-ONLY] Real fetch smoke check (optional, manual)**

On the target host after Task 4's image exists:
Run: `LEANSTRAL_MODELS_DIR=~/models/leanstral bash .devcontainer/leanstral-common/fetch-weights.sh q4_k_m`
Expected: downloads `Leanstral-1.5-119B-A6B-Q4_K_M.gguf` (~65GB) then `weights ready:`.

- [ ] **Step 6: Commit**

```bash
git add .devcontainer/leanstral-common/fetch-weights.sh \
  tests/devcontainer/test_fetch_weights.sh
git commit -m "feat(devcontainer): add Leanstral weight fetch/convert-on-demand"
```

---

## Task 3: Vibe config generation (`gen-vibe-config.sh`)

**Files:**
- Create: `.devcontainer/leanstral-common/gen-vibe-config.sh`
- Test: `tests/devcontainer/test_gen_vibe_config.sh`

**Interfaces:**
- Consumes: `common.sh` (`log`).
- Produces: `gen-vibe-config.sh <local|api> <out_path>` writes a `config.toml`. `local` → `[[providers]]` with `api_base = "http://127.0.0.1:8080/v1"`, model `name = "leanstral-1.5"`, telemetry+auto-update false. `api` → provider pointing at Mistral Labs `https://api.mistral.ai/v1`, model `name = "leanstral-1-5"`. Both include the shared `[[mcp_servers]]` lean-lsp stdio block and `default_agent = "lean"`.

- [ ] **Step 1: Write the failing test**

Create `tests/devcontainer/test_gen_vibe_config.sh`:

```bash
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
```

- [ ] **Step 2: Run test to verify it fails**

Run: `bash tests/devcontainer/test_gen_vibe_config.sh`
Expected: FAIL — script does not exist.

- [ ] **Step 3: Write minimal implementation**

Create `.devcontainer/leanstral-common/gen-vibe-config.sh`:

```bash
#!/usr/bin/env bash
# Generate a Mistral Vibe config.toml for the given backend.
# Usage: gen-vibe-config.sh <local|api> <out_path>
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/common.sh"

backend="${1:?usage: gen-vibe-config.sh <local|api> <out_path>}"
out="${2:?usage: gen-vibe-config.sh <local|api> <out_path>}"
mkdir -p "$(dirname "$out")"

case "$backend" in
  local)
    cat > "$out" <<'TOML'
# Leanstral local flavor — llama-server on 127.0.0.1:8080 (OpenAI-compatible).
active_model = "leanstral-local"
default_agent = "lean"
enable_telemetry = false
enable_auto_update = false

[[providers]]
name = "local"
api_base = "http://127.0.0.1:8080/v1"
api_style = "openai"
backend = "generic"

[[models]]
name = "leanstral-1.5"
provider = "local"
alias = "leanstral-local"
TOML
    ;;
  api)
    cat > "$out" <<'TOML'
# Leanstral API flavor — Mistral Labs hosted endpoint.
active_model = "leanstral-api"
default_agent = "lean"

[[providers]]
name = "mistral"
api_base = "https://api.mistral.ai/v1"
api_style = "openai"
backend = "generic"
api_key_env = "MISTRAL_API_KEY"

[[models]]
name = "leanstral-1-5"
provider = "mistral"
alias = "leanstral-api"
TOML
    ;;
  *) log "unknown backend: $backend (want local|api)"; exit 2 ;;
esac

# Shared MCP block appended for both backends (one copy).
cat >> "$out" <<'TOML'

[[mcp_servers]]
name = "lean-lsp"
transport = "stdio"
command = "uvx"
args = ["lean-lsp-mcp"]
TOML

log "wrote Vibe config ($backend): $out"
```

- [ ] **Step 4: Run test to verify it passes**

Run: `bash tests/devcontainer/test_gen_vibe_config.sh`
Expected: `PASS test_gen_vibe_config`

- [ ] **Step 5: Commit**

```bash
git add .devcontainer/leanstral-common/gen-vibe-config.sh \
  tests/devcontainer/test_gen_vibe_config.sh
git commit -m "feat(devcontainer): generate Vibe config.toml for local/api backends"
```

---

## Task 4: Local `Dockerfile.local` (CUDA 12.8 + llama.cpp + toolchain)

**Files:**
- Create: `.devcontainer/leanstral-common/Dockerfile.local`

**Interfaces:**
- Produces: an image with `vscode` user; `/opt/llama.cpp/build/bin/llama-server`, `llama-quantize`, and `/opt/llama.cpp/convert_hf_to_gguf.py`; `uv`, `hf`, `git`, `curl`, `python3` on PATH; `LLAMA_CPP_DIR=/opt/llama.cpp` env. elan/lake and Vibe are installed at container-create time (not baked), so the toolchain matches `lean-toolchain` and Vibe stays current.

- [ ] **Step 1: Write the Dockerfile**

Create `.devcontainer/leanstral-common/Dockerfile.local`:

```dockerfile
# Blackwell (RTX 5090, sm_120) requires CUDA 12.8 for llama.cpp — do NOT bump
# to 13.x (MMQ kernel segfault). 86 = RTX 3090 (Ampere), 120 = RTX 5090.
FROM nvidia/cuda:12.8.0-devel-ubuntu24.04

ARG USERNAME=vscode
ENV DEBIAN_FRONTEND=noninteractive \
    LLAMA_CPP_DIR=/opt/llama.cpp \
    PATH=/home/${USERNAME}/.local/bin:/usr/local/cuda/bin:$PATH

RUN apt-get update && apt-get install -y --no-install-recommends \
      git curl ca-certificates build-essential cmake ninja-build \
      python3 python3-pip python3-venv sudo libcurl4-openssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Non-root dev user (the CUDA image is root by default).
RUN useradd -m -s /bin/bash ${USERNAME} \
    && echo "${USERNAME} ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/${USERNAME} \
    && chmod 0440 /etc/sudoers.d/${USERNAME}

# Build llama.cpp with CUDA for both GPU architectures.
RUN git clone --depth 1 https://github.com/ggml-org/llama.cpp ${LLAMA_CPP_DIR} \
    && cmake -S ${LLAMA_CPP_DIR} -B ${LLAMA_CPP_DIR}/build -G Ninja \
         -DGGML_CUDA=ON \
         -DCMAKE_CUDA_ARCHITECTURES="86;120" \
         -DGGML_CUDA_FORCE_CUBLAS=OFF \
         -DLLAMA_CURL=ON \
    && cmake --build ${LLAMA_CPP_DIR}/build --target llama-server llama-quantize \
    && pip3 install --break-system-packages -r ${LLAMA_CPP_DIR}/requirements.txt

USER ${USERNAME}
# uv provides `uv`/`uvx`; used later to install mistral-vibe and run lean-lsp-mcp.
RUN curl -LsSf https://astral.sh/uv/install.sh | sh
```

- [ ] **Step 2: [HOST-ONLY] Build the image**

Run (on target host):
```bash
docker build -f .devcontainer/leanstral-common/Dockerfile.local \
  -t leanstral-local:dev .devcontainer/leanstral-common
```
Expected: build succeeds; final image tagged `leanstral-local:dev`.

- [ ] **Step 3: [HOST-ONLY] Verify tooling + GPUs in the image**

Run:
```bash
docker run --rm --gpus all leanstral-local:dev bash -lc \
  'nvidia-smi -L && /opt/llama.cpp/build/bin/llama-server --version \
   && which uv uvx && ls /opt/llama.cpp/convert_hf_to_gguf.py'
```
Expected: two GPUs listed (`GPU 0: ... 3090`, `GPU 1: ... 5090`), a llama.cpp
version/build line, `uv`/`uvx` paths, and the convert script path.

- [ ] **Step 4: Commit**

```bash
git add .devcontainer/leanstral-common/Dockerfile.local
git commit -m "feat(devcontainer): CUDA 12.8 image building llama.cpp for 3090+5090"
```

---

## Task 5: Model server launcher (`start-llama-server.sh`)

**Files:**
- Create: `.devcontainer/leanstral-common/start-llama-server.sh`

**Interfaces:**
- Consumes: `common.sh`; image from Task 4 (`llama-server`, `LLAMA_CPP_DIR`); weights from Task 2.
- Produces: launches `llama-server` on `127.0.0.1:8080` with alias `leanstral-1.5`, then blocks until `/health` reports ok. Env knobs (with defaults): `LEANSTRAL_QUANT`, `LLAMA_TENSOR_SPLIT=0.42,0.58`, `LLAMA_N_CPU_MOE=24`, `LLAMA_CTX=32768`, `LLAMA_PORT=8080`.

- [ ] **Step 1: Write the launcher**

Create `.devcontainer/leanstral-common/start-llama-server.sh`:

```bash
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

[ -f "$model" ] || { log "ERROR: weights missing: $model (run fetch-weights.sh)"; exit 1; }

# Already up? (idempotent across container restarts)
if curl -sf "http://127.0.0.1:${port}/health" >/dev/null 2>&1; then
  log "llama-server already healthy on :$port"; exit 0
fi

log "starting llama-server: $fname (tensor-split=${LLAMA_TENSOR_SPLIT:-0.42,0.58},"
log "  n-cpu-moe=${LLAMA_N_CPU_MOE:-24}, ctx=${LLAMA_CTX:-32768})"
nohup "$bin" \
  --model "$model" \
  --alias leanstral-1.5 \
  --host 127.0.0.1 --port "$port" \
  --n-gpu-layers 999 \
  --split-mode layer \
  --tensor-split "${LLAMA_TENSOR_SPLIT:-0.42,0.58}" \
  --n-cpu-moe "${LLAMA_N_CPU_MOE:-24}" \
  --ctx-size "${LLAMA_CTX:-32768}" \
  --jinja \
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
```

- [ ] **Step 2: Syntax check**

Run: `bash -n .devcontainer/leanstral-common/start-llama-server.sh && echo OK`
Expected: `OK`

- [ ] **Step 3: [HOST-ONLY] Live server + inference check**

With weights present and inside the built image (GPUs attached):
```bash
LEANSTRAL_QUANT=q4_k_m bash .devcontainer/leanstral-common/start-llama-server.sh
curl -s http://127.0.0.1:8080/v1/chat/completions -H 'Content-Type: application/json' \
  -d '{"model":"leanstral-1.5","messages":[{"role":"user","content":"say hi"}]}' \
  | head -c 400
nvidia-smi --query-gpu=memory.used --format=csv
```
Expected: `/health` goes healthy within the timeout; completion returns JSON
with a `choices` array; `nvidia-smi` shows VRAM used on **both** GPUs.

- [ ] **Step 4: Commit**

```bash
git add .devcontainer/leanstral-common/start-llama-server.sh
git commit -m "feat(devcontainer): llama-server launcher with tensor-split + health gate"
```

---

## Task 6: Verification ladder (`verify.sh`)

**Files:**
- Create: `.devcontainer/leanstral-common/verify.sh`

**Interfaces:**
- Consumes: `common.sh`; env `LEANSTRAL_BACKEND` (`local|api`), `LEANSTRAL_QUANT` (local only), `MISTRAL_API_KEY` (api only).
- Produces: `verify.sh` runs the backend-appropriate checks from spec §6 and exits nonzero on the first failure. Safe to run repeatedly.

- [ ] **Step 1: Write the verifier**

Create `.devcontainer/leanstral-common/verify.sh`:

```bash
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
```

- [ ] **Step 2: Syntax check**

Run: `bash -n .devcontainer/leanstral-common/verify.sh && echo OK`
Expected: `OK`

- [ ] **Step 3: [HOST-ONLY] Run against a live local container** (deferred to Task 8 end-to-end).

- [ ] **Step 4: Commit**

```bash
git add .devcontainer/leanstral-common/verify.sh
git commit -m "feat(devcontainer): backend-aware Leanstral verification ladder"
```

---

## Task 7: API flavor (`leanstral-api/`)

**Files:**
- Create: `.devcontainer/leanstral-api/devcontainer.json`
- Create: `.devcontainer/leanstral-api/on-create.sh`

**Interfaces:**
- Consumes: existing `scripts/setup-dev.sh`; `gen-vibe-config.sh`; `MISTRAL_API_KEY` from host env.
- Produces: a lightweight container that installs the Lean toolchain + Vibe and writes an `api`-backend `.vibe/config.toml` at repo root under `.vibe/`.

- [ ] **Step 1: Write `on-create.sh`**

Create `.devcontainer/leanstral-api/on-create.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COMMON="$REPO_ROOT/.devcontainer/leanstral-common"

git config --global commit.gpgsign false
git config --global tag.gpgsign false

# Lean toolchain (shared bootstrap; skip cache+build here, mirror base container).
bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache

# uv + Mistral Vibe.
command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh
"$HOME/.local/bin/uv" tool install mistral-vibe

# Vibe config → repo-local .vibe/config.toml (api backend).
bash "$COMMON/gen-vibe-config.sh" api "$REPO_ROOT/.vibe/config.toml"

echo "Leanstral API flavor ready. Set MISTRAL_API_KEY, then: vibe --agent lean"
```

- [ ] **Step 2: Write `devcontainer.json`**

Create `.devcontainer/leanstral-api/devcontainer.json`:

```jsonc
{
  "name": "Leanstral (API) + Vibe",
  "image": "mcr.microsoft.com/devcontainers/base:ubuntu",
  "features": {
    "ghcr.io/devcontainers/features/node:1": {},
    "ghcr.io/devcontainers/features/github-cli:1": {},
    "ghcr.io/devcontainers/features/python:1": {},
    "ghcr.io/anthropics/devcontainer-features/claude-code:1": {},
    "../features/no-gpg": {}
  },
  "customizations": { "vscode": { "extensions": ["leanprover.lean4"] } },
  "mounts": [
    "source=neural-network-proofs-claude-config,target=/home/vscode/.claude,type=volume"
  ],
  "remoteEnv": { "MISTRAL_API_KEY": "${localEnv:MISTRAL_API_KEY}" },
  "onCreateCommand": "bash .devcontainer/leanstral-api/on-create.sh"
}
```

- [ ] **Step 3: Validate JSON**

Run: `python3 -c "import json,re,sys; s=open('.devcontainer/leanstral-api/devcontainer.json').read(); json.loads(re.sub(r'//.*','',s)); print('OK')"`
Expected: `OK`

- [ ] **Step 4: [HOST-ONLY] Open + verify**

Reopen repo in the "Leanstral (API) + Vibe" container, then:
```bash
LEANSTRAL_BACKEND=api bash .devcontainer/leanstral-common/verify.sh
```
Expected: `ALL CHECKS PASSED (api)` (requires `MISTRAL_API_KEY`).

- [ ] **Step 5: Commit**

```bash
git add .devcontainer/leanstral-api/
git commit -m "feat(devcontainer): Leanstral API flavor (thin Vibe client + lean-lsp MCP)"
```

---

## Task 8: Local flavors (`leanstral-local-q4|q5|q8/`)

**Files:**
- Create: `.devcontainer/leanstral-common/on-create-local.sh`
- Create: `.devcontainer/leanstral-common/poststart.sh`
- Create: `.devcontainer/leanstral-local-q4/devcontainer.json`
- Create: `.devcontainer/leanstral-local-q5/devcontainer.json`
- Create: `.devcontainer/leanstral-local-q8/devcontainer.json`

**Interfaces:**
- Consumes: `Dockerfile.local` (Task 4), `fetch-weights.sh`, `gen-vibe-config.sh`, `start-llama-server.sh`, `verify.sh`.
- Produces: three selectable GPU flavors differing only by `LEANSTRAL_QUANT`. `onCreateCommand` installs toolchain + Vibe + fetches weights; `postStartCommand` launches the model server.

- [ ] **Step 1: Write the shared local `on-create-local.sh`**

Create `.devcontainer/leanstral-common/on-create-local.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COMMON="$REPO_ROOT/.devcontainer/leanstral-common"
: "${LEANSTRAL_QUANT:?LEANSTRAL_QUANT must be set by the flavor}"

git config --global commit.gpgsign false
git config --global tag.gpgsign false

bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache

command -v uv >/dev/null || curl -LsSf https://astral.sh/uv/install.sh | sh
"$HOME/.local/bin/uv" tool install mistral-vibe
# Note: `hf` (huggingface CLI) is baked into Dockerfile.local (Task 4), so no
# install needed here; fetch-weights.sh below relies on it.

bash "$COMMON/gen-vibe-config.sh" local "$REPO_ROOT/.vibe/config.toml"

# Fetch (or convert) the GGUF for this flavor's quant into the bind mount.
bash "$COMMON/fetch-weights.sh" "$LEANSTRAL_QUANT"

echo "Leanstral local ($LEANSTRAL_QUANT) provisioned. Server starts on attach."
```

- [ ] **Step 2: Write the q4 `devcontainer.json`**

Create `.devcontainer/leanstral-local-q4/devcontainer.json`:

```jsonc
{
  "name": "Leanstral (local Q4_K_M) + Vibe",
  "build": {
    "dockerfile": "../leanstral-common/Dockerfile.local",
    "context": "../leanstral-common"
  },
  "runArgs": ["--gpus", "all"],
  "hostRequirements": { "gpu": true },
  "remoteUser": "vscode",
  "features": {
    "ghcr.io/devcontainers/features/github-cli:1": {},
    "ghcr.io/anthropics/devcontainer-features/claude-code:1": {}
  },
  "customizations": { "vscode": { "extensions": ["leanprover.lean4"] } },
  "mounts": [
    "source=neural-network-proofs-claude-config,target=/home/vscode/.claude,type=volume",
    "source=${localEnv:HOME}/models/leanstral,target=/models/leanstral,type=bind"
  ],
  "containerEnv": {
    "LEANSTRAL_QUANT": "q4_k_m",
    "LEANSTRAL_BACKEND": "local",
    "LEANSTRAL_MODELS_DIR": "/models/leanstral",
    "HF_TOKEN": "${localEnv:HF_TOKEN}"
  },
  "onCreateCommand": "bash .devcontainer/leanstral-common/on-create-local.sh",
  "postStartCommand": "bash .devcontainer/leanstral-common/poststart.sh"
}
```

The `postStartCommand` delegates to a wrapper (keeps the JSON line ≤ 100 cols and
the backgrounding logic in one place). Create
`.devcontainer/leanstral-common/poststart.sh`:

```bash
#!/usr/bin/env bash
# Launch the model server in the background so container attach isn't blocked
# by start-llama-server.sh's foreground health-wait. Log to /tmp/llama-start.log.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
nohup bash "$HERE/start-llama-server.sh" >/tmp/llama-start.log 2>&1 &
```

- [ ] **Step 3: Write q5 and q8 by copying q4 and changing two lines**

Create `.devcontainer/leanstral-local-q5/devcontainer.json` — identical to q4 except:
```jsonc
  "name": "Leanstral (local Q5_K_M) + Vibe",
  ...
    "LEANSTRAL_QUANT": "q5_k_m",
```
Create `.devcontainer/leanstral-local-q8/devcontainer.json` — identical to q4 except:
```jsonc
  "name": "Leanstral (local Q8_0) + Vibe",
  ...
    "LEANSTRAL_QUANT": "q8_0",
```
(Copy the full q4 file; change only the `name` and `LEANSTRAL_QUANT` values.)

- [ ] **Step 4: Validate all three JSON files**

Run:
```bash
for f in q4 q5 q8; do
  python3 -c "import json,re; json.loads(re.sub(r'//.*','',open('.devcontainer/leanstral-local-$f/devcontainer.json').read())); print('$f OK')"
done
```
Expected: `q4 OK`, `q5 OK`, `q8 OK`.

- [ ] **Step 5: [HOST-ONLY] End-to-end on the target host (Q4 first)**

1. Reopen in "Leanstral (local Q4_K_M) + Vibe" (first build compiles llama.cpp; first attach downloads ~65GB).
2. `LEANSTRAL_BACKEND=local LEANSTRAL_QUANT=q4_k_m bash .devcontainer/leanstral-common/verify.sh`
   Expected: `ALL CHECKS PASSED (local)`.
3. `vibe --agent lean` → ask it to prove `example : 1 + 1 = 2 := by rfl` in a scratch `.lean` file and confirm it uses lean-lsp MCP feedback.

- [ ] **Step 6: Commit**

```bash
git add .devcontainer/leanstral-common/on-create-local.sh \
  .devcontainer/leanstral-local-q4 .devcontainer/leanstral-local-q5 \
  .devcontainer/leanstral-local-q8
git commit -m "feat(devcontainer): Leanstral local GPU flavors (q4/q5/q8) + server autostart"
```

---

## Task 9: Documentation (`README-leanstral.md`)

**Files:**
- Create: `.devcontainer/README-leanstral.md`
- Modify: `CLAUDE.md` (append a short pointer under "Build and verify")

**Interfaces:**
- Consumes: everything above.
- Produces: user-facing docs: prerequisites, flavor picker, weight sizes, retuning, risks.

- [ ] **Step 1: Write the README**

Create `.devcontainer/README-leanstral.md` covering:
- **What it is** — Leanstral 1.5 + Vibe + lean-lsp MCP; four flavors table (copy from spec §1).
- **Prerequisites (local flavors):** NVIDIA driver + **NVIDIA Container Toolkit** on host; `~/models/leanstral` dir will be created; optional `HF_TOKEN`. Note CUDA 12.8 pin rationale (Blackwell).
- **Prerequisites (API flavor):** `MISTRAL_API_KEY` in host env.
- **Choosing a flavor:** VS Code "Dev Containers: Reopen in Container" → pick the config; weight sizes Q4≈65GB, Q5≈85GB, Q8≈127GB, and the one-time BF16≈238GB download for q5/q8 conversion.
- **Usage:** `vibe --agent lean`.
- **Verifying:** `LEANSTRAL_BACKEND=<local|api> bash .devcontainer/leanstral-common/verify.sh`.
- **Retuning the GPU split:** `LLAMA_TENSOR_SPLIT`, `LLAMA_N_CPU_MOE`, `LLAMA_CTX` env; how to try 5090-only; where the server log is (`/tmp/llama-server.log`).
- **Risks/known issues:** copy spec §7 (community GGUF quality unverified, split tuning, CUDA pin).

- [ ] **Step 2: Add a pointer in `CLAUDE.md`**

Under the "Build and verify" section, append:
```markdown
### Leanstral + Vibe dev containers (optional)

Alternative dev containers run the Leanstral 1.5 proof agent via Mistral Vibe
(local GPU or Mistral API) with lean-lsp MCP. See
`.devcontainer/README-leanstral.md`. The default `Lean 4 + Mathlib` container is
unchanged.
```

- [ ] **Step 3: Verify links resolve**

Run: `test -f .devcontainer/README-leanstral.md && grep -q README-leanstral CLAUDE.md && echo OK`
Expected: `OK`

- [ ] **Step 4: Commit**

```bash
git add .devcontainer/README-leanstral.md CLAUDE.md
git commit -m "docs(devcontainer): document Leanstral + Vibe flavors and retuning"
```

---

## Self-Review

**Spec coverage:**
- §1 flavors/DRY → Tasks 7 (api), 8 (local q4/q5/q8), shared scripts Tasks 1–6. ✓
- §2 local internals (CUDA 12.8, llama.cpp flags, GPU passthrough, background server + health gate) → Tasks 4, 5, 8. ✓
- §3 data flow (Vibe → endpoint; MCP stdio) → Tasks 3, 5, 7, 8. ✓
- §4 weight provisioning (bind mount, download vs convert-on-demand) → Task 2, mounts in Task 8. ✓
- §5 Vibe config.toml (local + api, telemetry off, mcp block) → Task 3. ✓
- §6 verification ladder → Task 6, exercised in Tasks 7/8. ✓
- §7 residual risks (retuning knobs, CUDA pin, sizes) → env knobs Task 5, docs Task 9. ✓

**Placeholder scan:** No `TBD`/`TODO`. The one intentional dead code (`mcp_block` heredoc in Task 3) is called out with rationale. q5/q8 JSON are specified as "copy q4, change two named values" with the exact values given — full file already shown in Task 8 Step 2. ✓

**Type/name consistency:** `leanstral_gguf_filename` (Task 1) used identically in Tasks 2 & 5. Model alias `leanstral-1.5` consistent across Task 3 config, Task 5 `--alias`, Task 6 curl. Env var names (`LEANSTRAL_QUANT`, `LEANSTRAL_BACKEND`, `LEANSTRAL_MODELS_DIR`, `LLAMA_TENSOR_SPLIT`, `LLAMA_N_CPU_MOE`, `LLAMA_CTX`, `LLAMA_PORT`) consistent across Tasks 5/6/8. Backend values `local|api` consistent across Tasks 3/6/7/8. ✓
```
