# Design: Leanstral 1.5 + Mistral Vibe + MCP dev containers

**Date:** 2026-07-13
**Status:** Approved (brainstorm) — ready for implementation plan
**Author:** Davor Runje (with Claude Code)

## Goal

Add new dev container flavors to this repository that let a developer drive
**Mistral Vibe** (`vibe --agent lean`) against the **Leanstral 1.5** Lean-4 proof
agent, with the **lean-lsp MCP** wired in for real Lean compiler feedback. Two
families are shipped: one that runs Leanstral **locally** on the host GPUs, and
one that uses the **free Mistral Labs API**. Nothing about the existing
`Lean 4 + Mathlib` dev container changes.

## Background / research summary

- **Leanstral 1.5** (`mistralai/Leanstral-1.5-119B-A6B`, Apache-2.0, released
  2026-06-30): a Lean-4 proof-agent MoE, **119B total / 6.5B active** params,
  256k context. Available three ways: free via Mistral Labs API
  (`leanstral-1-5`), downloadable weights on HuggingFace, and inside Mistral
  Vibe. Trained on a Lean-compiler feedback loop (submit proof → read compiler
  output → revise).
- **Mistral Vibe**: terminal coding agent (`uv tool install mistral-vibe`,
  `vibe --agent lean`). Points at **any OpenAI-compatible endpoint** via
  `[[providers]]` / `[[models]]` in `config.toml`; supports **MCP** over
  stdio/http; telemetry and auto-update can be disabled for offline use.
- **lean-lsp MCP** (`uvx lean-lsp-mcp`): Mistral explicitly recommends wiring it
  into Vibe. This repo already uses a `lean-lsp` MCP server with Claude Code.
- **Target hardware**: 32-core Threadripper, 256 GB RAM, NVIDIA RTX 3090 (24 GB,
  Ampere `sm_86`) + RTX 5090 (32 GB, Blackwell `sm_120`) = 56 GB VRAM.

### Two hard external constraints (verified during research)

1. **Blackwell requires CUDA 12.8 for llama.cpp.** The 5090 (`sm_120`) must be
   built with **CUDA 12.8** specifically — CUDA 13.1 segfaults in the Blackwell
   MMQ kernel and older toolkits lack `sm_120`. Build with
   `CMAKE_CUDA_ARCHITECTURES="86;120"` and `GGML_CUDA_FORCE_CUBLAS=OFF`. The
   known MXFP4/`sm_120` breakage does not apply here (we use K-quants).
2. **No official Leanstral GGUFs exist.** Mistral has not shipped GGUFs. Only
   community artifacts exist today:
   - `Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF` — Q4_K_M only.
   - `sahilchachra/Leanstral-1.5-119B-A6B-BF16` — dequantized BF16 (native
     format is consolidated FP8).
   Therefore Q5_K_M / Q8_0 must be produced locally by converting the BF16 repo
   and running `llama-quantize` (convert-on-demand; see §4).

### Sources

- https://docs.mistral.ai/models/model-cards/leanstral-1-5
- https://mistral.ai/news/leanstral-1-5/
- https://www.marktechpost.com/2026/07/03/mistral-ai-releases-leanstral-1-5-an-apache-2-0-lean-4-code-agent-model-solving-587-of-672-putnambench-problems/
- https://github.com/mistralai/mistral-vibe
- https://docs.mistral.ai/vibe/code/cli/offline-models
- https://dev.to/chung_duy_51a346946b27a3d/running-mistral-vibe-with-local-llms-a-complete-guide-1mde
- https://zenn.dev/toki_mwc/articles/rtx5090-blackwell-cuda-toolkit-trap-llama-cpp?locale=en
- https://github.com/ggml-org/llama.cpp/issues/19662
- https://huggingface.co/Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF
- https://huggingface.co/mistralai/Leanstral-1.5-119B-A6B/discussions/1
- https://huggingface.co/sahilchachra/Leanstral-1.5-119B-A6B-BF16

## 1. Architecture & flavors

Four selectable dev container configs under `.devcontainer/`, all reusing the
repo's existing `scripts/setup-dev.sh` (elan/lake Lean toolchain) and the
`~/.claude` named volume, then layering a **Vibe + lean-lsp-MCP** stack on top.

| Flavor   | Folder                            | Model backend                              |
|----------|-----------------------------------|--------------------------------------------|
| API      | `.devcontainer/leanstral-api/`    | Mistral Labs `leanstral-1-5` (`MISTRAL_API_KEY`) |
| Local Q4 | `.devcontainer/leanstral-local-q4/` | llama-server, Q4_K_M                     |
| Local Q5 | `.devcontainer/leanstral-local-q5/` | llama-server, Q5_K_M                     |
| Local Q8 | `.devcontainer/leanstral-local-q8/` | llama-server, Q8_0                       |

**DRY strategy.** The three local flavors share **one** `Dockerfile.local`, one
entrypoint, and one set of provisioning scripts; each `devcontainer.json`
differs only by a `LEANSTRAL_QUANT` build-arg / env (`q4_k_m`, `q5_k_m`,
`q8_0`). The API flavor reuses the existing lightweight base image (no CUDA).
Shared scripts live in a common location (e.g. `.devcontainer/leanstral-common/`)
and are referenced by each flavor to avoid duplication.

The existing `.devcontainer/devcontainer.json` (`Lean 4 + Mathlib`) is left
exactly as-is and remains the default.

## 2. Local container internals (all-in-one, GPU passthrough)

Single container `FROM nvidia/cuda:12.8.0-devel-ubuntu24.04` running everything:

- **llama.cpp build**: compile with `-DGGML_CUDA=ON`,
  `-DCMAKE_CUDA_ARCHITECTURES="86;120"`, `-DGGML_CUDA_FORCE_CUBLAS=OFF`.
  Produces `llama-server`, `llama-quantize`, and the GGUF conversion tooling.
- **Runtime layer**: elan/lake via `setup-dev.sh`; `uv tool install
  mistral-vibe`; `uvx`-runnable `lean-lsp-mcp`; HuggingFace `hf` CLI for weight
  download; Claude Code retained, unchanged.
- **GPU passthrough**: `devcontainer.json` gets
  `"runArgs": ["--gpus","all"]` and `"hostRequirements": {"gpu": true}`. The
  host must have the NVIDIA Container Toolkit installed — documented as a
  prerequisite.
- **Model server as a background service**: `postStartCommand` launches
  `llama-server` on `127.0.0.1:8080` (OpenAI-compatible, `--alias
  leanstral-1.5`), with `--n-gpu-layers 999 --split-mode layer` and a
  `--tensor-split` tuned to place hot layers across the 3090 + 5090 and offload
  the remaining MoE experts to system RAM. A health-check gate blocks until
  `/health` is green before Vibe is usable.

## 3. Data flow

```
You ──▶ vibe --agent lean ──▶ OpenAI-compatible chat  ──▶ llama-server (local flavors)
             │                                          └▶ Mistral Labs API (api flavor)
             └──▶ MCP (stdio) ──▶ lean-lsp-mcp ──▶ lake / Lean LSP over your repo
```

Vibe drives the agent loop; each turn it may call lean-lsp MCP tools (goal
state, diagnostics, build) for real Lean compiler feedback, then revise — the
loop Leanstral was trained for. The model endpoint is the only thing that
differs between flavors. Claude Code and its own lean-lsp MCP continue to
coexist untouched.

## 4. Weight provisioning (host bind-mount, download/convert on first start)

- All local flavors bind-mount a host dir into the container:
  `"mounts": ["source=${localEnv:HOME}/models/leanstral,target=/models/leanstral,type=bind"]`.
- The local `on-create.sh` runs `fetch-weights.sh <quant>`:
  1. If the target GGUF is already present in `/models/leanstral/` → done
     (survives rebuilds; shared across flavors).
  2. Else if quant is **Q4_K_M** → `hf download
     Abiray/Leanstral-1.5-119B-A6B-Q4KM-GGUF` (fast direct path).
  3. Else (**Q5_K_M / Q8_0**) → download `sahilchachra/…-BF16` once, run
     `convert_hf_to_gguf.py` to an F16 GGUF, then `llama-quantize` to the target
     quant. Result cached in the mount.
- Script logs expected sizes up front, is idempotent and resumable. Reads
  `HF_TOKEN` from env if a repo requires auth.

**Approximate footprints** (planning figures, to confirm at build time):
Q4_K_M ≈ 65 GB, Q5_K_M ≈ 85 GB, Q8_0 ≈ 127 GB; BF16 base for conversion
≈ 238 GB (one-time, only for q5/q8).

## 5. Vibe wiring (`config.toml`)

A project-level `.vibe/config.toml` is generated per flavor, plus a shared
`lean` agent profile.

Local flavors:

```toml
[[providers]]
name = "local"
api_base = "http://127.0.0.1:8080/v1"
api_style = "openai"
backend = "generic"

[[models]]
name = "leanstral-1.5"      # matches llama-server --alias
provider = "local"
alias = "leanstral-local"

active_model = "leanstral-local"
enable_telemetry = false
enable_auto_update = false

[[mcp_servers]]              # shared by all flavors
name = "lean-lsp"
transport = "stdio"
command = "uvx"
args = ["lean-lsp-mcp"]
```

API flavor: swap the provider/model block for Mistral's hosted endpoint
(`leanstral-1-5`, auth via `MISTRAL_API_KEY`), keep the same `[[mcp_servers]]`
block, and leave telemetry at its default. Launch with `vibe --agent lean`.

## 6. Testing / verification

Documented, runnable verification ladder:

1. `nvidia-smi` inside the container sees both GPUs (local flavors).
2. `llama-server` `/health` is green; a one-shot `curl
   /v1/chat/completions` returns tokens; `nvidia-smi` shows VRAM split across
   both cards.
3. `uvx lean-lsp-mcp` starts and reports the repo's Lean toolchain.
4. End-to-end: `vibe --agent lean` proves a trivial lemma in a scratch file
   using the MCP feedback loop.
5. The repo's own gate still passes:
   `lake env lean scripts/check_sorry_free.lean`.

For the API flavor, step 1–2 are replaced by a connectivity check against the
Labs endpoint with `MISTRAL_API_KEY`.

## 7. Residual risks

- **Heterogeneous-GPU tuning**: `--tensor-split` across a 24 GB Ampere and a
  32 GB Blackwell card needs hand-tuning; the 3090 is the likely bottleneck.
  A 5090-heavy split or 5090-only configuration may perform better; ship a
  sensible default and document how to retune.
- **Community GGUF quality is unverified** against the FP8 original; the
  convert-on-demand path depends on `convert_hf_to_gguf.py` supporting the
  Leanstral architecture. Validate quality with a small proof suite.
- **CUDA 12.8 pin must not drift** — bumping the base image to 13.x reintroduces
  the Blackwell MMQ segfault. Pin explicitly and comment why.
- **Large first-run download** for q5/q8 (BF16 base ≈ 238 GB). Documented in the
  flavor README so it is not a surprise.
- **NVIDIA Container Toolkit** must be installed on the host; the local flavors
  fail fast with a clear message if GPUs are not visible.

## Out of scope

- Serving to multiple concurrent users / batched throughput (vLLM/SGLang were
  considered and rejected for the heterogeneous-GPU + MoE-offload profile).
- Sidecar/host-served topologies (all-in-one with GPU passthrough was chosen).
- Producing and publishing official GGUF quants upstream.
- Any change to the existing `Lean 4 + Mathlib` dev container or repo proofs.
