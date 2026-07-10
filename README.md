# Neural Network Proofs

`NeuralNetworkProofs` is a Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **universal approximation theorems (UATs) for neural networks**, all `sorry`-free
(see [Formalized results](#formalized-results-neuralnetworkproofs) below).

The project is developed in a self-contained VS Code **dev container**: the only thing you need on
your host machine is Docker (and VS Code with the Dev Containers extension) — the Lean toolchain,
Mathlib cache, and Claude Code CLI are all provisioned automatically.

## Formalized results: `NeuralNetworkProofs`

`NeuralNetworkProofs` formalizes universal approximation theorems for neural networks, all
`sorry`-free. Four developments are complete:

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
- **Runje et al. (2026)** — universal approximation for **partially monotone** networks: a
  non-monotone feature block is embedded by an unconstrained single-hidden-layer network (Leshno
  UAP), clamped into `[0,1]`, concatenated with the monotone block, and fed to a monotone network
  (the Mikulincer–Reichman / Sartor line above). Soundness
  (`…Runje.PartMonoNet.monotone_snd`, monotone in the monotone block) and the uniform-approximation
  headline (`…Runje.partial_monotone_approximation`).

**Correctness gate.** Every headline is machine-checked to depend only on the axioms
`[propext, Classical.choice, Quot.sound]` — no `sorry`/`sorryAx`, no extra axioms (see
[Working in the project](#working-in-the-project)).

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

- **`.devcontainer/`** — dev container definition and setup scripts
  (`on-create.sh` installs elan and uv; `post-create.sh` runs `lake exe cache get`
  and `lake build`). The Node.js, GitHub CLI (`gh`), and Claude Code CLI come from
  dev container features.
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

Contributions are welcome. A few conventions keep the development consistent and machine-verifiable:

- **No `sorry`/`admit`.** These are machine-checked proofs; a genuine research blocker is reported
  honestly (open an issue), never hidden behind `sorry` or worked around by weakening a theorem
  statement.
- **Keep every headline axiom-clean.** Before opening a PR, run the sorry-free gate above and
  confirm each headline reports exactly `[propext, Classical.choice, Quot.sound]`. CI runs this gate
  and fails on `sorryAx`.
- **Prefer minimal, precise imports** over blanket `import Mathlib` — it makes `lake build` much
  slower. Import only the specific Mathlib modules a file needs.
- **Line length ≤ 100 codepoints**; docstrings on public declarations.
- **`ForMathlib/` is upstream-facing** — keep those files self-contained (Mathlib-only dependencies
  where possible), each with an `Intended Mathlib home:` header.

Make sure `lake build` is green and the sorry-free gate passes before submitting a PR. `CLAUDE.md`
is the full contributor guide (module layout, namespaces, conventions, build workflow).
