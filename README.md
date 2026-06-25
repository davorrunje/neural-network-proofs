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

Claude Code session history and memory persist across container rebuilds: the
container's `~/.claude/projects` directory is bind-mounted to
`~/.claude-devcontainer/lean-playground/projects` on your host (see the `mounts`
entry in `.devcontainer/devcontainer.json`). Login/auth state is *not* persisted,
so you re-run the interactive login after a rebuild.

## What's inside

- **`.devcontainer/`** — dev container definition and setup scripts
  (`on-create.sh` installs elan and uv; `post-create.sh` runs
  `lake exe cache get` and `lake build`). The Node.js, GitHub CLI (`gh`), and
  Claude Code CLI come from dev container features.
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
