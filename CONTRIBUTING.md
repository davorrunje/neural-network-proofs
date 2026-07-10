# Contributing

Thanks for contributing! This guide covers setting up a development environment and the
conventions we follow.

## Development environment

Work either in a ready-made container or on your own machine. Both use the same setup script
(`scripts/setup-dev.sh`), so the installed toolchain is identical.

### Option A — Dev Container or GitHub Codespaces (recommended)

- **VS Code:** open the repo and choose **Reopen in Container** (Dev Containers extension), or run
  *Dev Containers: Reopen in Container*.
- **Codespaces:** on GitHub, **Code → Codespaces → Create codespace**.

The container runs setup automatically on first create: it installs the Lean toolchain (`elan`),
`uv`, `graphviz`, and the blueprint preview toolchain, then downloads the Mathlib cache and builds
the project. The first build is slow once and fast afterwards.

### Option B — Local host machine

Prerequisites: `git` and `curl` (macOS also needs the Xcode Command Line Tools). Then:

    git clone https://github.com/davorrunje/neural-network-proofs.git
    cd neural-network-proofs
    scripts/setup-dev.sh          # Linux, macOS, or WSL

On native Windows (PowerShell) use the companion script (best-effort; WSL is the tested route):

    scripts\setup-dev.ps1

The script installs elan, uv, graphviz, and the blueprint toolchain, then fetches the Mathlib
cache and builds. Flags:

- `--pdf` — also install LaTeX (only for the blueprint PDF; the web preview needs no LaTeX).
- `--no-build` — skip `lake build`.
- `--no-cache` — skip the Mathlib cache download.

Open a new shell afterwards (or `source ~/.profile`) so `lake`, `uv`, and `leanblueprint` are on
your `PATH`.

## Building and verifying

    lake build                                   # build everything
    lake env lean scripts/check_sorry_free.lean  # sorry-free axiom gate

Before opening a PR, make sure `lake build` is green and every headline reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Previewing the blueprint locally

Once the blueprint exists, build and preview it with:

    leanblueprint web      # HTML + dependency graph -> blueprint/web/
    leanblueprint serve    # serve the compiled blueprint at a local URL

The web build uses MathJax and needs no LaTeX; any `pdflatex`/`dvisvgm` warnings are harmless.

## Conventions

- **No `sorry`/`admit`.** These are machine-checked proofs; report a genuine research blocker
  honestly (open an issue), never hidden behind `sorry` or by weakening a theorem statement.
- **Keep every headline axiom-clean** — run the sorry-free gate before a PR; CI fails on `sorryAx`.
- **Prefer minimal, precise imports** over blanket `import Mathlib` (it makes `lake build` much
  slower); import only the specific Mathlib modules a file needs.
- **Line length ≤ 100 codepoints**; docstrings on public declarations.
- **`ForMathlib/` is upstream-facing** — keep those files self-contained (Mathlib-only
  dependencies where possible), each with an `Intended Mathlib home:` header.

`CLAUDE.md` is the full contributor guide (module layout, namespaces, build workflow, gotchas).
