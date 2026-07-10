# Neural Network Proofs

`NeuralNetworkProofs` is a Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **universal approximation theorems (UATs) for neural networks**, all `sorry`-free
(see [Formalized results](#formalized-results-neuralnetworkproofs) below).

The fastest path is a self-contained VS Code **dev container** or a **GitHub Codespace** — you
need only Docker and the Dev Containers extension (the Lean toolchain, Mathlib cache, and Claude
Code CLI are provisioned automatically). You can also set up a local machine directly with
`scripts/setup-dev.sh`; see [CONTRIBUTING.md](CONTRIBUTING.md).

## Formalized results: `NeuralNetworkProofs`

`NeuralNetworkProofs` formalizes universal approximation theorems for neural networks, all
`sorry`-free. Three developments are complete:

- **Cybenko (1989)** — a single-hidden-layer network with a continuous sigmoidal activation is dense
  in `C(K, ℝ)`.
  Headline: `UniversalApproximation.Cybenko.universal_approximation`.
- **Leshno–Lin–Pinkus–Schocken (1993)** — an `M`-class activation densely approximates iff it is not
  (a.e.) a polynomial.
  Headline: `UniversalApproximation.Leshno.leshno_dense_iff`.
- **Monotone networks** — universal approximation under monotonicity constraints, on a shared
  activation-generic core:
  - *Mikulincer–Reichman (2022):* a depth-4 monotone threshold network exactly interpolates, and
    uniformly approximates, any monotone function.
    Headlines: `…Monotone.monotone_interpolation`, `…Monotone.monotone_approximation`.
  - *Sartor et al. (2025):* monotone networks with **one-sided-saturating** activations — a finite
    limit on just *one* side (Def 3.3), which crucially admits **unbounded** activations such as
    ReLU (the paper's *"beyond bounded activations"*: saturating on one side is enough, boundedness
    is not required). Results: Theorem 3.5 (`…Monotone.saturating_interpolation`), the
    point-reflection / weight-sign equivalence (Props 3.8 & 3.10), and non-positive-weight
    universality (Prop 3.11, `…Monotone.nonpos_weight_universal`).

**Correctness gate.** Every headline is machine-checked to depend only on the axioms
`[propext, Classical.choice, Quot.sound]` — no `sorry`/`sorryAx`, no extra axioms (see
[Working in the project](#working-in-the-project)).

## Getting started

The fastest path is a ready-made container; you can also set up a local machine. Full instructions
are in [CONTRIBUTING.md](CONTRIBUTING.md).

- **Dev Container / Codespaces:** open the repo in VS Code and **Reopen in Container**, or create a
  GitHub Codespace. Setup runs automatically (Lean toolchain, `uv`, `graphviz`, blueprint tooling,
  Mathlib cache, first build).
- **Local host:** clone, then run `scripts/setup-dev.sh` (Linux/macOS/WSL) or
  `scripts\setup-dev.ps1` (native Windows).

When the build finishes, open any file under `NeuralNetworkProofs/`; the Lean infoview should load
and report no errors.

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

Claude Code state persists across container rebuilds: the container's entire
`~/.claude` directory lives on a container-private Docker **named volume**
(`neural-network-proofs-claude-config`, see the `mounts` entry in
`.devcontainer/devcontainer.json`). This covers session history, memory,
**login/auth, and installed plugins**, so you do not re-authenticate or reinstall
plugins after a rebuild. The volume is isolated from your host filesystem. To
reset it, run these on your host (not the container terminal) with the dev
container stopped — Docker will not remove a volume that is still in use:
`docker volume ls | grep neural-network-proofs-claude-config`, then
`docker volume rm <name>`.

The [`superpowers`](https://github.com/obra/superpowers) plugin (its
`brainstorming` skill and more) is declared in `.claude/settings.json` and
**auto-installed on build**: `post-create.sh` runs
`.devcontainer/provision-claude-plugins.sh`, which installs everything listed in
`.devcontainer/claude-plugins.txt` from the `superpowers-dev` marketplace. This
is best-effort — if the `claude` CLI is not logged in or offline, the build still
succeeds and you can rerun the script by hand.

## What's inside

- **`.devcontainer/`** — dev container definition and setup scripts. `on-create.sh` delegates the
  toolchain install to `scripts/setup-dev.sh` (elan, uv, graphviz, the blueprint preview
  toolchain); `post-create.sh` runs `lake exe cache get`, `lake build`, and the Claude-plugin
  provisioning. The Node.js, GitHub CLI (`gh`), and Claude Code CLI come from dev container
  features.
- **`.mcp.json`** — registers the `lean-lsp-mcp` MCP server (run via `uvx`).
- **`lean-toolchain`** — pins the Lean version (matched to the committed
  Mathlib revision).
- **`lakefile.toml`** / **`lake-manifest.json`** — the Lake package definition
  and its pinned dependency revisions.
- **`NeuralNetworkProofs/`** — the formalization library (the *Formalized results* above).
  `NeuralNetworkProofs.lean` is the root module and re-exports every development, so a plain
  `lake build` verifies all headlines. Mathlib-upstream candidates live under
  `NeuralNetworkProofs/ForMathlib/`.
- **`scripts/check_sorry_free.lean`** — the correctness gate (see below).
- **`CLAUDE.md`** — contributor guide (layout, conventions, build/verify workflow).

## Working in the project

- Build everything (verifies all headlines): `lake build`
- **Sorry-free check** — the real correctness gate (a `sorry` is only a *warning*, so a green build
  alone does not prove the development is admit-free):
  ```bash
  lake env lean scripts/check_sorry_free.lean
  ```
  Each headline should report exactly `[propext, Classical.choice, Quot.sound]`; any `sorryAx` means
  an admitted proof has been (re)introduced. CI runs this gate and fails on `sorryAx`.
- Refresh the Mathlib cache after changing the Mathlib revision:
  `lake exe cache get`
- Update dependencies: `lake update` (then re-run `lake exe cache get`).

## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for how to set up a development
environment (container or host), preview the blueprint locally, and the conventions we follow (no
`sorry`, axiom-clean headlines, minimal imports, ≤100-codepoint lines). `CLAUDE.md` is the full
contributor guide.
