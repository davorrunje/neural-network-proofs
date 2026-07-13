# Leanstral + Vibe dev containers

Optional dev container flavors that run **Leanstral 1.5** — a Lean-4 proof-agent
model — through **Mistral Vibe** (`vibe --agent lean`), wired to the **lean-lsp
MCP** server for real Lean compiler feedback (goal state, diagnostics, build).
Vibe drives the agent loop; each turn it can call lean-lsp MCP tools against
this repo's own Lean toolchain, read the result, and revise — the loop
Leanstral was trained on.

Two families are shipped: one runs Leanstral **locally** on host GPUs via
`llama-server`, one uses the **free Mistral Labs API**. The default
`Lean 4 + Mathlib` container (`.devcontainer/devcontainer.json`) is unchanged
and remains the default — these are additional, opt-in flavors.

## The four flavors

Folders below are relative to `.devcontainer/`.

| Flavor   | Folder                          | Model backend                                  |
|----------|----------------------------------|------------------------------------------------|
| API      | `leanstral-api/`                | Mistral Labs `leanstral-1-5` (`MISTRAL_API_KEY`) |
| Local Q4 | `leanstral-local-q4/`           | `llama-server`, Q4_K_M                          |
| Local Q5 | `leanstral-local-q5/`           | `llama-server`, Q5_K_M                          |
| Local Q8 | `leanstral-local-q8/`           | `llama-server`, Q8_0                            |

The three local flavors share one `Dockerfile.local`, one entrypoint, and one
set of provisioning scripts under `.devcontainer/leanstral-common/`; each
flavor's `devcontainer.json` only differs by `LEANSTRAL_QUANT`
(`q4_k_m` / `q5_k_m` / `q8_0`). The API flavor reuses the existing lightweight
base image (no CUDA, no GPU passthrough).

## Prerequisites — local flavors (Q4/Q5/Q8)

- An **NVIDIA driver** and the **NVIDIA Container Toolkit** installed on the
  host, so Docker can pass GPUs through (`"runArgs": ["--gpus", "all"]`,
  `"hostRequirements": {"gpu": true}` in each local `devcontainer.json`). If
  the toolkit is missing, the container will fail to see any GPU.
- A host directory `~/models/leanstral` — bind-mounted into the container at
  `/models/leanstral` and shared across all three local flavors, so a weight
  file downloaded/converted once is reused by the others and survives
  rebuilds. **Create it before the first build** (`mkdir -p ~/models/leanstral`);
  Docker will not auto-create a bind-mount source and the container fails to
  start with `bind source path does not exist` if it is missing.
- Optionally, an **`HF_TOKEN`** in your host environment if a HuggingFace repo
  you pull from requires auth; it is passed through as `HF_TOKEN` in
  `containerEnv`.
- **Why CUDA 12.8 is pinned**: the local image is
  `FROM nvidia/cuda:12.8.0-devel-ubuntu24.04` (see
  `.devcontainer/leanstral-common/Dockerfile.local`). An RTX 5090 (Blackwell,
  `sm_120`) needs llama.cpp built with CUDA 12.8 specifically — CUDA 13.x
  segfaults in the Blackwell MMQ kernel, and older toolkits don't support
  `sm_120` at all. llama.cpp is built with
  `CMAKE_CUDA_ARCHITECTURES="86;120"` (86 = RTX 3090/Ampere, 120 = RTX
  5090/Blackwell) and `GGML_CUDA_FORCE_CUBLAS=OFF`. Do not bump the base image
  past 12.8.x.

## Prerequisites — API flavor

- A **`MISTRAL_API_KEY`** in your host environment (used for the free Mistral
  Labs `leanstral-1-5` endpoint). It is passed through via `remoteEnv` in
  `.devcontainer/leanstral-api/devcontainer.json`.

## Choosing a flavor

In VS Code, run **"Dev Containers: Reopen in Container"** and pick the config
you want (`Leanstral (API) + Vibe`, `Leanstral (local Q4_K_M) + Vibe`, etc.).

For the local flavors, weigh disk space and quality against download time:

- **Q4_K_M ≈ 72 GB** — downloaded directly from the community GGUF repo
  (fastest to provision).
- **Q5_K_M ≈ 85 GB** and **Q8_0 ≈ 127 GB** — no official GGUF exists at these
  quants, so the container downloads the **BF16 base once (≈ 238 GB,
  one-time)**, converts it to F16 GGUF, then runs `llama-quantize` to produce
  the target quant. This conversion happens on first container creation
  (`on-create-local.sh` → `fetch-weights.sh`) and can take a while; the result
  is cached in `~/models/leanstral` so subsequent rebuilds skip it.

All of the above are approximate planning figures — confirm actual sizes at
download/build time.

## Usage

Once the container is up (weights fetched, `llama-server` healthy for local
flavors), run:

```bash
vibe                     # local flavors: uses the `lean-local` agent by default
# or explicitly:
vibe --agent lean-local  # local (Q4/Q5/Q8) — runs against llama-server
vibe --agent lean        # API flavor only — Mistral-cloud leanstral endpoint
```

This launches Mistral Vibe with the `lean-lsp` MCP server (`uvx lean-lsp-mcp`)
wired in, pointed at the flavor's model endpoint.

**Why the local flavors use a custom `lean-local` agent, not the builtin `lean`.**
Vibe ships a builtin `lean` agent, but its profile *hardwires* `active_model` to a
Mistral-cloud provider (`https://api.mistral.ai/v1` + `MISTRAL_API_KEY`) — an agent
override that wins over any config, so `vibe --agent lean` always demands a cloud key
and cannot target the local server. The local flavors therefore install a custom
`lean-local` agent (`$VIBE_HOME/agents/lean-local.toml`, from
`leanstral-common/lean-local.agent.toml`, written by `on-create-local.sh`) that reuses
the same Lean system prompt but points at `llama-server`, and set it as
`default_agent`. Note also that vibe reads its config from `$VIBE_HOME/config.toml`
(default `~/.vibe/config.toml`); the generated `.vibe/config.toml` in the repo is a
project-level layer merged on top when you run vibe from the repo root.

## Verifying

Run the backend-aware verification ladder from inside the container:

```bash
LEANSTRAL_BACKEND=<local|api> bash .devcontainer/leanstral-common/verify.sh
```

(`LEANSTRAL_BACKEND` is already set for you in each flavor's `containerEnv`,
so you can usually just run `bash .devcontainer/leanstral-common/verify.sh`.)
For `local` this checks: both GPUs visible (`nvidia-smi -L`), `llama-server`
`/health` is green, a chat completion returns tokens. For `api` it checks
`MISTRAL_API_KEY` is set and the Mistral endpoint is reachable. Both backends
then check that `uvx lean-lsp-mcp` launches and that this repo's own
sorry-free gate (`lake env lean scripts/check_sorry_free.lean`) still passes.

## Retuning the GPU split (local flavors)

`llama-server` is started by `.devcontainer/leanstral-common/start-llama-server.sh`
(invoked in the background from `postStartCommand`), reading these env vars
(defaults shown):

- `LLAMA_TENSOR_SPLIT` (default `0.42,0.58`) — fraction of layers placed on
  each GPU, in the order `nvidia-smi -L` reports them. The default is a
  starting point for a 24 GB RTX 3090 + 32 GB RTX 5090; the 3090 is the likely
  bottleneck, so a 5090-heavier split (or effectively 5090-only, e.g.
  `LLAMA_TENSOR_SPLIT=0,1` if the 5090 is device 1) may perform better on your
  hardware. Check `nvidia-smi -L` first to confirm which index is which card.
- `LLAMA_N_CPU_MOE` (default `24`) — number of MoE expert layers offloaded to
  system RAM instead of GPU.
- `LLAMA_CTX` (default `32768`) — context size (`--ctx-size`).
- `LLAMA_PORT` (default `8080`) — the port `llama-server` listens on
  (`127.0.0.1:<port>`, OpenAI-compatible, `--alias leanstral-1.5`).

Set the env var(s) you want to change (e.g. in `containerEnv` in the flavor's
`devcontainer.json`, or by exporting before restart) and restart the
container, or re-run `bash .devcontainer/leanstral-common/start-llama-server.sh`
manually. The server log is at **`/tmp/llama-server.log`** — check it if
`/health` never turns green or the split is misbehaving (the background
launcher also writes `/tmp/llama-start.log`).

## Risks / known issues

- **Heterogeneous-GPU tuning**: splitting layers across a 24 GB Ampere card
  and a 32 GB Blackwell card needs hand-tuning; the 3090 is the likely
  bottleneck. A 5090-heavy split or 5090-only configuration may perform
  better — a sensible default is shipped, retune as above.
- **Community GGUF quality is unverified** against the original FP8 weights.
  The convert-on-demand path (Q5/Q8) also depends on `convert_hf_to_gguf.py`
  correctly supporting the Leanstral architecture. Validate quality with a
  small proof suite before relying on it.
- **The CUDA 12.8 pin must not drift** — bumping the base image to 13.x
  reintroduces the Blackwell MMQ kernel segfault. It is pinned explicitly and
  commented in `Dockerfile.local`; leave it alone.
- **Large first-run download** for Q5/Q8: the BF16 base is ≈ 238 GB, on top of
  the target quant's own footprint. Budget disk space and time accordingly.
- **NVIDIA Container Toolkit must be installed on the host** for the local
  flavors — GPUs must be visible inside the container or the health-check gate
  in `start-llama-server.sh` will fail.
