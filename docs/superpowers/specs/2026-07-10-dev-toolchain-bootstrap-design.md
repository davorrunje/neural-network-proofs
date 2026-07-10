# Dev-toolchain bootstrap — design

**Goal:** A single, reusable setup script that installs everything needed to develop this repo
**and** build/preview the blueprint website locally — runnable at devcontainer build/startup time
and directly on a host machine (Linux, macOS, WSL, GitHub Codespaces, and native Windows).

**Why a spec:** getting a working local blueprint preview is not trivial. The Python toolchain has
a real version trap (below), the `plastex` subprocess must be on `PATH`, and the same setup must
work across the devcontainer and several host platforms. This captures the validated recipe so it
is reproducible rather than rediscovered.

**Approach (chosen: A):** one portable **bash** bootstrap (`scripts/setup-dev.sh`) for
Linux/macOS/WSL/Codespaces, plus a **PowerShell** companion (`scripts/setup-dev.ps1`) for native
Windows. The devcontainer's `on-create`/`post-create` delegate to the bash script, so the container
and a host machine run the same logic — one source of truth.

## Scope

A **full dev-environment bootstrap**, delivered as its own spec/plan/PR, merged before the website
work (which then assumes the tooling exists). The script installs:

- **elan** (Lean toolchain manager) if missing — `--default-toolchain none`; the repo's
  `lean-toolchain` picks the version.
- **uv** (Python env manager) if missing.
- **graphviz** + dev headers + a C toolchain + `pkg-config` (to build `pygraphviz`).
- the **blueprint Python toolchain** into a repo-local `uv` venv (the validated recipe below).
- optionally **LaTeX** (only with `--pdf`), for `leanblueprint pdf`.
- the **Mathlib cache** (`lake exe cache get`) and a project **build** (`lake build`), each
  skippable by flag.

The PR also documents the setup for contributors (`CONTRIBUTING.md`, `README.md`, `CLAUDE.md`) —
see the Documentation section.

## The validated Python recipe (the crux)

Installing `leanblueprint` naively does **not** yield a working web/graph build. The validated,
reproducible combination is:

- `leanblueprint==0.0.20` (PyPI) — pulls `plastexdepgraph==0.0.5`.
- **plasTeX from git master**, pinned to a specific commit (validated here: `4fe23e2`,
  `git+https://github.com/plastex/plastex.git@4fe23e2…`), installed **after** leanblueprint to
  override its plasTeX. The plan carries the full hash.

Rationale, confirmed empirically in this environment:

- PyPI `plastex==3.1` crashes the dependency-graph builder
  (`TypeError: unhashable type: 'theorem'`).
- `plastex==3.0` is too old — plasTeX falls back to default renderers for `theorem`/`\lean`/
  `\leanok`/`\uses`, losing the blueprint styling and producing **no** dependency graph.
- plasTeX **git master** builds both `web/index.html` and `web/dep_graph_document.html` with the
  blueprint renderers and no warnings.

Two further findings baked into the design:

- The tools must live in a **venv whose `bin` is on `PATH`** (exposed via symlinks into
  `~/.local/bin`). `leanblueprint` shells out to `plastex` by name; a bare `uv tool install
  leanblueprint` exposes only `leanblueprint`, so `plastex` is "not found". A shared venv fixes it.
- **No LaTeX is required** for the web preview. The `pdflatex`/`dvisvgm` "vector imager" warnings
  are benign — they only matter for tikz/vector images, which the blueprint does not use.

## What the bootstrap does (bash, ordered, idempotent)

Each step is a no-op if already satisfied; the whole script is safe to re-run.

1. Detect OS + package manager (apt on Debian/Ubuntu, Homebrew on macOS) and whether this is WSL
   or Codespaces (both behave as Linux).
2. Ensure `git` and `curl`.
3. Install system deps: apt → `graphviz libgraphviz-dev pkg-config build-essential python3-dev`;
   brew → `graphviz`. On a Linux without apt (dnf/pacman), print the exact package list to install
   and continue rather than failing silently.
4. Install **elan** if missing; put it on `PATH`.
5. Install **uv** if missing; put it on `PATH`.
6. Create a repo-local **`.venv/`** via `uv venv`; `uv pip install leanblueprint`, then override
   plasTeX with the pinned git commit; symlink `leanblueprint` and `plastex` into `~/.local/bin`.
7. `lake exe cache get` (unless `--no-cache`); `lake build` (unless `--no-build`).
8. Idempotently wire `~/.local/bin`, elan, and uv onto `PATH` in the shell profiles (bash + zsh),
   guarded so re-runs don't duplicate lines.
9. Print a summary and the local-preview commands.

## Cross-platform handling

- **Linux/macOS/WSL/Codespaces:** the bash script (apt or brew). WSL and Codespaces are Linux.
- **Native Windows:** `scripts/setup-dev.ps1` — winget (or scoop) for Git, Graphviz, elan, and uv;
  the same `uv` venv recipe; symlinks/`PATH` via the user environment. WSL remains the recommended,
  tested Windows route; the `.ps1` is a best-effort convenience.
- **`--pdf`:** apt → a texlive subset + `latexmk`; macOS → BasicTeX (+ `tlmgr`); Windows → MiKTeX.

## Devcontainer + Codespaces wiring

- `.devcontainer/on-create.sh` → `bash scripts/setup-dev.sh --no-build` (fast: toolchain +
  graphviz + venv + Mathlib cache; defers the long build so container creation stays quick).
- `.devcontainer/post-create.sh` → `lake build` plus the existing `~/.claude` ownership fix
  (devcontainer-specific; stays out of the portable script).
- GitHub Codespaces builds the same `devcontainer.json`, so it is covered with no extra work.

## Flags & UX

- `--pdf` — also install a LaTeX distribution.
- `--no-build` — skip `lake build`.
- `--no-cache` — skip `lake exe cache get`.
- Non-interactive by default (safe for CI/Codespaces); re-runnable; prints a clear final summary.

## Documentation

The script is only useful if contributors can find it. This PR documents both the devcontainer and
the host path:

- **`CONTRIBUTING.md` (new):** the contributor dev-setup home, with two clearly separated paths.
  - *Devcontainer / Codespaces:* open in a Dev Container (VS Code "Reopen in Container") or a
    Codespace; setup runs automatically via the lifecycle hooks; nothing else to install.
  - *Host machine:* clone, then run `scripts/setup-dev.sh` (Linux/macOS/WSL) or
    `scripts/setup-dev.ps1` (native Windows), including the flags (`--pdf`, `--no-build`,
    `--no-cache`) and the prerequisites the script does not install.
  - *Local blueprint preview:* build with `leanblueprint web`, then view with `leanblueprint
    serve` (note that the real `blueprint/` content arrives with the website PR; the tooling and
    the smoke test work regardless).
  - Absorbs the contributor conventions currently inlined in `README.md` (no `sorry`, axiom-clean,
    minimal imports, ≤100 codepoints, `ForMathlib/` upstream-facing) so there is one home for
    them; points to `CLAUDE.md` for the full guide.
- **`README.md` (update):** "Getting started" gains the host option alongside the
  devcontainer/Codespaces path and a pointer to `CONTRIBUTING.md`; fix the stale
  "open the sample Lean file" step; the "Contributing" section links to `CONTRIBUTING.md` instead
  of duplicating the conventions.
- **`CLAUDE.md` (update, "other docs appropriately"):** the Build section gains a short pointer to
  `scripts/setup-dev.sh` and the local-preview commands, kept minimal.

## Verification / success criteria

- After a run (and a clean re-run), `elan`/`lake`, `uv`, `dot`, `leanblueprint`, and `plastex` are
  all on `PATH` (version checks pass).
- **Smoke test:** scaffold a throwaway blueprint inside the repo (which provides the Lean-project
  marker), run `leanblueprint web`, assert both `web/index.html` and `web/dep_graph_document.html`
  are produced, then clean up. This is the acceptance gate that the recipe works end-to-end.
- Re-running the script makes no duplicate `PATH` entries and does not error.
- The devcontainer (and Codespaces) come up with the full toolchain available.
- `CONTRIBUTING.md` exists and documents both paths; `README.md` points to it with no stale steps;
  every command shown in the docs matches the script's actual flags and behavior.

## Out of scope

- The website itself (blueprint content, doc-gen4, landing page, Pages workflow) — its own spec
  and plan, which depend on this bootstrap.
- Any change to the Lean proofs, theorem statements, or `lean-toolchain`.
- Auto-installing on dnf/pacman Linux or non-standard shells beyond a clear manual-steps message.

## Risks

- **Native-Windows `.ps1` is unverified here** — no Windows to test against; it is best-effort and
  should be confirmed by a Windows user. WSL is the tested Windows path.
- **The plasTeX git-commit pin tracks an unreleased fix** — reproducible, but should be bumped to a
  fixed PyPI release when one lands.
- **The `--pdf` TeX package set may need per-platform tuning** — LaTeX is not exercised by the
  default path or the website, so this is lower-risk.
