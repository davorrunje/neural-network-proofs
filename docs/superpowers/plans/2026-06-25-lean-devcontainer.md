# Lean Dev Container Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

> **Repo rename note (2026-07-10):** This document predates the rename
> `lean-playground` → `neural-network-proofs` (Lake package `lean_playground` →
> `neural_network_proofs`, lib `LeanPlayground` → `NeuralNetworkProofs`). The old
> names below are kept as a historic record; use the current names for live work.

**Goal:** Provide a VS Code dev container that gives a working Lean 4 + Mathlib environment with editor support, plus Claude Code and the `lean-lsp-mcp` server for proof assistance, requiring nothing installed on the host except Docker.

**Architecture:** A stock `mcr.microsoft.com/devcontainers/base:ubuntu` image is referenced directly from `devcontainer.json`. Dev container features add Node.js and the Claude Code CLI. An `onCreateCommand` script installs `elan` (Lean's toolchain manager) and `uv` (for `uvx`); a `postCreateCommand` script downloads the prebuilt Mathlib cache and builds the project. A committed `.mcp.json` registers `lean-lsp-mcp` so Claude can query Lean goal states and search Mathlib. The repo root is a real Lake project whose Lean version is pinned to match the committed Mathlib revision. The version-pinned project files are generated once during implementation by running the canonical Mathlib scaffolding commands inside a throwaway Docker container, then committed.

**Tech Stack:** Docker, VS Code Dev Containers, Lean 4, elan, Lake, Mathlib4, Node.js, Claude Code CLI, uv/uvx, lean-lsp-mcp.

## Global Constraints

- No Lean/elan/Mathlib install on the host machine — only Docker is assumed. Scaffolding and verification run inside throwaway Docker containers.
- Base image: `mcr.microsoft.com/devcontainers/base:ubuntu` (the same image for the dev container and the scaffolding container).
- Lean version is never hardcoded: it is pinned via the `lean-toolchain` file produced by Mathlib's scaffolding, and must match the Mathlib revision in `lake-manifest.json`.
- All shell scripts start with `#!/usr/bin/env bash` and `set -euo pipefail`.
- Build artifacts (`.lake/`) are never committed.
- No secrets in the repo: Claude Code authenticates by interactive login inside the container; no API keys or mounted host credentials.
- Commit messages end with the Co-Authored-By trailer:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`

---

### Task 1: Dev container definition

Creates the dev container configuration, its two setup scripts, and the MCP config for Claude. Verified by JSON and shell-syntax checks (no Lean build yet — that is Task 2).

**Files:**
- Create: `.devcontainer/devcontainer.json`
- Create: `.devcontainer/on-create.sh`
- Create: `.devcontainer/post-create.sh`
- Create: `.mcp.json`
- Modify: `.gitignore` (already contains `.lake/` — confirm only)

**Interfaces:**
- Consumes: nothing.
- Produces: `.devcontainer/on-create.sh` (installs elan and uv, idempotent, leaves both on PATH for future shells via `~/.profile` and `~/.bashrc`); `.devcontainer/post-create.sh` (runs `lake exe cache get && lake build` in a shell where elan is on PATH); `.mcp.json` (registers the `lean-lsp` MCP server run via `uvx lean-lsp-mcp`). Task 2's project files are consumed by `post-create.sh` at container-create time.

- [ ] **Step 1: Write `.devcontainer/devcontainer.json`**

Plain JSON (no comments) so it can be validated with `json.tool`. The `node` feature provides Node.js/npm; the `claude-code` feature installs the `claude` CLI on top of it:

```json
{
  "name": "Lean 4 + Mathlib",
  "image": "mcr.microsoft.com/devcontainers/base:ubuntu",
  "features": {
    "ghcr.io/devcontainers/features/node:1": {},
    "ghcr.io/anthropics/devcontainer-features/claude-code:1": {}
  },
  "customizations": {
    "vscode": {
      "extensions": [
        "leanprover.lean4"
      ]
    }
  },
  "onCreateCommand": "bash .devcontainer/on-create.sh",
  "postCreateCommand": "bash .devcontainer/post-create.sh"
}
```

- [ ] **Step 2: Write `.devcontainer/on-create.sh`**

```bash
#!/usr/bin/env bash
set -euo pipefail

# Ensure system dependencies are present (base image runs as the `vscode`
# user with passwordless sudo).
if ! command -v curl >/dev/null 2>&1 || ! command -v git >/dev/null 2>&1; then
  sudo apt-get update
  sudo apt-get install -y --no-install-recommends curl git
fi

# Install elan (Lean's toolchain manager) if not already present.
# --default-toolchain none: the project's lean-toolchain file decides the
# Lean version, so we do not install a default here.
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
fi

# Install uv (Astral) if not already present. uv provides `uvx`, used to run
# the lean-lsp-mcp server configured in .mcp.json.
if ! command -v uv >/dev/null 2>&1 && [ ! -x "$HOME/.local/bin/uv" ]; then
  curl -LsSf https://astral.sh/uv/install.sh | sh
fi

# Make elan and uv available in future interactive and login shells.
for profile in "$HOME/.profile" "$HOME/.bashrc"; do
  if ! grep -q '.elan/env' "$profile" 2>/dev/null; then
    echo '. "$HOME/.elan/env"' >> "$profile"
  fi
  if ! grep -q '.local/bin' "$profile" 2>/dev/null; then
    echo 'export PATH="$HOME/.local/bin:$PATH"' >> "$profile"
  fi
done

echo "elan installed:"
. "$HOME/.elan/env"
elan --version
echo "uv installed:"
export PATH="$HOME/.local/bin:$PATH"
uv --version
```

- [ ] **Step 3: Write `.devcontainer/post-create.sh`**

```bash
#!/usr/bin/env bash
set -euo pipefail

# elan was installed by on-create.sh; put it on PATH for this script.
. "$HOME/.elan/env"

# Download the prebuilt Mathlib cache (fast) instead of compiling it from
# source (~1hr), then build the project. elan resolves the Lean version from
# ./lean-toolchain on first invocation.
lake exe cache get
lake build

echo "Lean + Mathlib build complete."
```

- [ ] **Step 4: Write `.mcp.json`**

Project-scoped MCP config that Claude Code reads automatically when run from the repo root. `uvx` fetches and runs `lean-lsp-mcp` on first use (uv is installed by `on-create.sh`):

```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "uvx",
      "args": ["lean-lsp-mcp"]
    }
  }
}
```

- [ ] **Step 5: Confirm `.gitignore` ignores build artifacts**

Run: `cat .gitignore`
Expected: contains a line `.lake/`. If missing, add it.

- [ ] **Step 6: Validate the files**

Run:
```bash
python3 -m json.tool .devcontainer/devcontainer.json >/dev/null && echo "devcontainer JSON OK"
python3 -m json.tool .mcp.json >/dev/null && echo "mcp JSON OK"
bash -n .devcontainer/on-create.sh && echo "on-create.sh syntax OK"
bash -n .devcontainer/post-create.sh && echo "post-create.sh syntax OK"
```
Expected: `devcontainer JSON OK`, `mcp JSON OK`, `on-create.sh syntax OK`, `post-create.sh syntax OK` (no errors).

- [ ] **Step 7: Commit**

```bash
chmod +x .devcontainer/on-create.sh .devcontainer/post-create.sh
git add .devcontainer/ .mcp.json .gitignore
git commit -m "Add dev container definition, setup scripts, and MCP config

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Scaffold the Lean + Mathlib project

Generates the version-pinned Lake project at the repo root using Mathlib's canonical scaffolding commands inside a throwaway Docker container, adds a small worked example that imports Mathlib, and verifies the whole thing builds end-to-end. The single container run is the real end-to-end test of the environment.

**Files (all generated at the repo root by the scaffold; commit the non-artifact ones):**
- Create: `lakefile.toml`
- Create: `lean-toolchain`
- Create: `lake-manifest.json`
- Create: the generated library source files (exact layout confirmed in Step 2, e.g. `LeanPlayground.lean` and `LeanPlayground/Basic.lean`)
- Modify: `.gitignore` (the `math` template may regenerate it — keep `.lake/` ignored)

**Interfaces:**
- Consumes: nothing from Task 1 at scaffold time (the scaffold container is independent of the dev container).
- Produces: a buildable Lake package importable via `import Mathlib`, with `lean-toolchain` and `lake-manifest.json` pinned to matching versions. `post-create.sh` (Task 1) consumes these at dev-container creation.

- [ ] **Step 1: Scaffold, add the sample, and build — all in one throwaway container**

Run from the repo root. This runs as root inside the container (no sudo), installs elan, scaffolds the project with the Lean toolchain pinned to Mathlib's, downloads the Mathlib cache, builds the bare scaffold, writes a worked example, and rebuilds to verify the example:

```bash
docker run --rm -v "$PWD":/work -w /work \
  mcr.microsoft.com/devcontainers/base:ubuntu bash -lc '
    set -euo pipefail
    apt-get update && apt-get install -y --no-install-recommends curl git
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    . "$HOME/.elan/env"
    git config --global --add safe.directory /work

    # Create the Lake project in the current directory, with the Lean
    # toolchain pinned to the one Mathlib currently uses (the +...:lean-toolchain
    # form), and Mathlib added as a dependency (the "math" template).
    lake +leanprover-community/mathlib4:lean-toolchain init lean_playground math

    # Belt-and-suspenders: ensure lean-toolchain exactly matches Mathlib master.
    curl -sSfL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

    # Resolve dependencies (writes lake-manifest.json), fetch prebuilt cache,
    # and verify the bare scaffold builds.
    lake update
    lake exe cache get
    lake build

    # Add a small worked example that uses Mathlib, then rebuild to verify it.
    LIBFILE=$(find . -path ./.lake -prune -o -name "Basic.lean" -print | head -n1)
    if [ -z "$LIBFILE" ]; then LIBFILE=$(find . -path ./.lake -prune -o -name "LeanPlayground.lean" -print | head -n1); fi
    cat > "$LIBFILE" <<"LEAN"
import Mathlib

/-- A tiny worked example: the sum of two even naturals is even. -/
theorem LeanPlayground.add_even {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  hm.add hn

#eval "Lean + Mathlib are working!"
LEAN

    lake build
    echo "SCAFFOLD + SAMPLE BUILD OK -> wrote sample to $LIBFILE"
  '
```

Expected: the run ends with `SCAFFOLD + SAMPLE BUILD OK -> wrote sample to ./...`. Note the printed path of the sample file.

- [ ] **Step 2: Inspect the generated layout**

Run:
```bash
find . -name '*.lean' -not -path './.lake/*'
cat lean-toolchain
ls lakefile.toml lake-manifest.json
```
Expected: at least one `.lean` source file at the repo root (the sample written in Step 1), a `lean-toolchain` containing a `leanprover/lean4:...` line, and both `lakefile.toml` and `lake-manifest.json` present. Record the actual `.lean` file path(s) for the commit step.

- [ ] **Step 3: Re-confirm `.gitignore`**

Run: `grep -q '\.lake/' .gitignore && echo "lake ignored" || echo '.lake/' >> .gitignore`
Expected: `lake ignored` (or the line is appended). The `.lake/` directory must not be committed.

- [ ] **Step 4: Verify `.lake/` is not staged**

Run:
```bash
git add -A
git status --short
```
Expected: the staged list includes `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, and the generated `.lean` file(s), and does NOT include anything under `.lake/`. If `.lake/` appears, fix `.gitignore` and `git rm -r --cached .lake` before continuing.

- [ ] **Step 5: Commit**

```bash
git commit -m "Scaffold Lean + Mathlib project with worked example

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: README

Adds usage instructions. No Lean build is required — the environment was already verified end-to-end in Task 2.

**Files:**
- Create: `README.md`

**Interfaces:**
- Consumes: the file paths and behavior established in Tasks 1 and 2.
- Produces: nothing consumed by later tasks (final task).

- [ ] **Step 1: Write `README.md`**

```markdown
# lean-playground

A playground for learning Lean 4, with [Mathlib](https://github.com/leanprover-community/mathlib4)
available. Everything runs inside a VS Code dev container, so the only thing you
need on your host machine is Docker (and VS Code with the Dev Containers
extension).

## Getting started

1. Open this folder in VS Code.
2. When prompted, choose **Reopen in Container** (or run the
   *Dev Containers: Reopen in Container* command).
3. Wait for the first build to finish. On the first run the container installs
   the Lean toolchain (`elan`) and downloads the prebuilt Mathlib cache (a few
   hundred MB). This is slow once and fast on every subsequent start.
4. Open the sample Lean file. The Lean infoview should appear and report no
   errors, confirming the worked example type-checks.

## Using Claude for proofs

The container ships with the Claude Code CLI and the
[`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) server already wired up
via `.mcp.json`. To use it:

1. In the container terminal, run `claude` and complete the interactive login
   the first time.
2. Ask Claude for help with a proof. Through `lean-lsp-mcp` it can see live goal
   states and diagnostics and search Mathlib (LeanSearch, Loogle, Lean State
   Search, Lean Hammer) rather than guessing lemma names.

No API key or host credentials are stored in the repo; authentication happens
through the interactive login.

## What's inside

- **`.devcontainer/`** — dev container definition and setup scripts
  (`on-create.sh` installs elan and uv; `post-create.sh` runs
  `lake exe cache get` and `lake build`). The Node.js and Claude Code CLI come
  from dev container features.
- **`.mcp.json`** — registers the `lean-lsp-mcp` MCP server (run via `uvx`).
- **`lean-toolchain`** — pins the Lean version (matched to the committed
  Mathlib revision).
- **`lakefile.toml`** / **`lake-manifest.json`** — the Lake package definition
  and its pinned dependency revisions.
- A sample `.lean` source file with a small Mathlib-backed proof.

## Working in the project

- Build everything: `lake build`
- Refresh the Mathlib cache after changing the Mathlib revision:
  `lake exe cache get`
- Update dependencies: `lake update` (then re-run `lake exe cache get`).
```

- [ ] **Step 2: Commit**

```bash
git add README.md
git commit -m "Add README with dev container usage instructions

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Notes on verification

The dev container itself is exercised most directly by opening the repo in VS Code and choosing *Reopen in Container*. That path is not scriptable here. What the plan verifies automatically:

- **elan install + PATH wiring** — the elan-install logic in `on-create.sh` is essentially what runs inside the Task 2 scaffold container, which succeeds end-to-end.
- **`lake exe cache get && lake build`** — exactly the Task 2 build that is confirmed to pass.
- **JSON/shell validity** of `devcontainer.json`, `.mcp.json`, and both scripts — Task 1 Step 6.

What relies on upstream tooling rather than being built here (and so is confirmed by the first real *Reopen in Container*, not by this plan):

- **Node + Claude Code features** — installed by the official `ghcr.io/devcontainers/features/node` and `ghcr.io/anthropics/devcontainer-features/claude-code` features.
- **uv install** — the official Astral installer; standard and idempotent.
- **lean-lsp-mcp** — fetched by `uvx` on first Claude use; requires a built project, which `post-create.sh` guarantees.

A green Task 2 means the Lean half of `onCreateCommand`/`postCreateCommand` will succeed for the committed project files; the Claude/MCP half is a thin layer over maintained, declarative installers.

**Optional manual smoke test** (after first *Reopen in Container*): in the container terminal run `elan --version`, `uv --version`, `claude --version`, and `lake build`; then run `claude`, log in, and ask it to inspect the sample file's goal state to confirm `lean-lsp-mcp` is reachable.
