# Dev-toolchain Bootstrap Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** One reusable setup script that installs the full dev + blueprint-preview toolchain,
runnable from the devcontainer (and Codespaces) and directly on a host, with contributor docs.

**Architecture:** A portable `scripts/setup-dev.sh` (Linux/macOS/WSL/Codespaces) installs elan, uv,
graphviz, and the blueprint toolchain into a repo-local `uv` venv; a `scripts/setup-dev.ps1` mirrors
it for native Windows. `on-create.sh` in the devcontainer delegates to the bash script;
`CONTRIBUTING.md`, `README.md`, and `CLAUDE.md` document both paths.

**Tech Stack:** bash, PowerShell, `uv`, `elan`/`lake`, `graphviz`/`pygraphviz`, `leanblueprint` +
`plasTeX`, GitHub Dev Containers / Codespaces.

## Global Constraints

- **Validated Python recipe (use these exact values):** `leanblueprint==0.0.20` (pulls
  `plastexdepgraph==0.0.5`), then override plasTeX with
  `git+https://github.com/plastex/plastex.git@4fe23e25565a4788f07077076211d21630a81cb0`, installed
  into a repo-local `uv` venv (`.venv/`) whose `leanblueprint`/`plastex` are symlinked into
  `~/.local/bin`. PyPI `plastex==3.1` crashes the dep-graph; `3.0` loses the renderers.
- **System deps for `pygraphviz`:** `graphviz`, `libgraphviz-dev`, `pkg-config`, a C compiler.
- **Web preview needs no LaTeX.** `pdflatex`/`dvisvgm` warnings are OK. LaTeX only under `--pdf`.
- **Flags:** `--pdf` (install LaTeX), `--no-build` (skip `lake build`), `--no-cache` (skip
  `lake exe cache get`). Non-interactive by default; idempotent; re-runnable.
- **Platforms:** Linux, macOS, WSL, Codespaces via `setup-dev.sh`; native Windows via
  `setup-dev.ps1`. WSL is the tested Windows route; the `.ps1` is best-effort and unverified here.
- **Do NOT change any `.lean` file, theorem, or `lean-toolchain`.** This PR touches only
  `scripts/`, `.devcontainer/`, `.gitignore`, and the three docs.
- **Devcontainer semantics:** `on-create.sh` installs (delegates, `--no-build --no-cache`);
  `post-create.sh` keeps the Mathlib cache + build + the `~/.claude` chown. `devcontainer.json` is
  unchanged.
- **Line length ≤ 100 codepoints** for every committed file. Measure codepoints:
  `python3 -c "print(len(line))"`.
- **Commits are UNSIGNED** (`commit.gpgsign=false`); use `git commit --no-gpg-sign` (no `-S`).
- **Push over HTTPS + gh helper** (SSH agent may be down):
  `git -c credential.helper='!gh auth git-credential' push \`
  `https://github.com/davorrunje/neural-network-proofs.git feat/dev-toolchain-bootstrap`
- **Branch:** `feat/dev-toolchain-bootstrap`, off `main`, holds spec commit `cfa321e`.
- **Repo URL:** `https://github.com/davorrunje/neural-network-proofs`.

---

### Task 1: `scripts/setup-dev.sh` — the portable bootstrap

**Files:**
- Create: `scripts/setup-dev.sh`
- Modify: `.gitignore` (add `.venv/`)

**Interfaces:**
- Produces: `scripts/setup-dev.sh [--pdf] [--no-build] [--no-cache]`. Consumed by Task 2
  (`on-create.sh` calls it with `--no-build --no-cache`) and documented in Task 4.

- [ ] **Step 1: Add `.venv/` to `.gitignore`**

Append to `.gitignore`:
```gitignore

# Repo-local Python venv for the blueprint toolchain (created by scripts/setup-dev.sh)
.venv/
```

- [ ] **Step 2: Write `scripts/setup-dev.sh`**

```bash
#!/usr/bin/env bash
# Full dev-environment bootstrap for the NeuralNetworkProofs repository.
#
# Installs (idempotently): elan (Lean toolchain manager), uv (Python env
# manager), graphviz + build deps for pygraphviz, and the blueprint preview
# toolchain (leanblueprint + plasTeX) into a repo-local uv venv exposed on
# PATH; optionally LaTeX (--pdf); then the Mathlib cache and a project build.
#
# Works on Linux, macOS, WSL, and GitHub Codespaces. Native Windows: use
# scripts/setup-dev.ps1 (or work inside WSL).
#
# Usage: scripts/setup-dev.sh [--pdf] [--no-build] [--no-cache] [--help]
set -euo pipefail

LEANBLUEPRINT_VERSION="0.0.20"
PLASTEX_URL="git+https://github.com/plastex/plastex.git"
PLASTEX_COMMIT="4fe23e25565a4788f07077076211d21630a81cb0"
PLASTEX_SPEC="plastex @ ${PLASTEX_URL}@${PLASTEX_COMMIT}"

WITH_PDF=0
DO_BUILD=1
DO_CACHE=1
usage() { sed -n '2,12p' "$0" | sed 's/^#\{1,\} \{0,1\}//'; }
for arg in "$@"; do
  case "$arg" in
    --pdf)      WITH_PDF=1 ;;
    --no-build) DO_BUILD=0 ;;
    --no-cache) DO_CACHE=0 ;;
    -h|--help)  usage; exit 0 ;;
    *) echo "setup-dev.sh: unknown option '$arg'" >&2; usage; exit 2 ;;
  esac
done

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"
LOCAL_BIN="$HOME/.local/bin"

log()  { printf '\n\033[1;34m==>\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33mwarning:\033[0m %s\n' "$*" >&2; }

OS="$(uname -s)"
PKG="none"
if [ "$OS" = "Linux" ] && command -v apt-get >/dev/null 2>&1; then
  PKG="apt"
elif [ "$OS" = "Darwin" ]; then
  PKG="brew"
fi
IS_WSL=0
if grep -qi microsoft /proc/version 2>/dev/null; then IS_WSL=1; fi
log "Platform: OS=$OS pkg=$PKG wsl=$IS_WSL codespaces=${CODESPACES:-0}"

ensure_system_deps() {
  log "Ensuring system dependencies (graphviz + build tools for pygraphviz)"
  case "$PKG" in
    apt)
      sudo apt-get update -qq
      sudo apt-get install -y --no-install-recommends \
        git curl graphviz libgraphviz-dev pkg-config build-essential python3-dev
      ;;
    brew)
      command -v brew >/dev/null 2>&1 || {
        warn "Homebrew not found. Install it from https://brew.sh then re-run."; exit 1; }
      brew install graphviz pkg-config
      xcode-select -p >/dev/null 2>&1 || \
        warn "Xcode CLT missing; run 'xcode-select --install' (needed to build pygraphviz)."
      ;;
    *)
      warn "Unsupported package manager. Install these yourself, then re-run:"
      warn "  graphviz, graphviz development headers, pkg-config, a C compiler."
      ;;
  esac
}

ensure_elan() {
  if command -v lake >/dev/null 2>&1 || [ -x "$HOME/.elan/bin/elan" ]; then
    log "elan already installed"
  else
    log "Installing elan (Lean toolchain manager)"
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
  fi
  [ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
}

ensure_uv() {
  if command -v uv >/dev/null 2>&1 || [ -x "$LOCAL_BIN/uv" ]; then
    log "uv already installed"
  else
    log "Installing uv (Python env manager)"
    curl -LsSf https://astral.sh/uv/install.sh | sh
  fi
  export PATH="$LOCAL_BIN:$PATH"
}

ensure_blueprint_venv() {
  log "Installing the blueprint toolchain into a repo-local venv (.venv)"
  uv venv "$REPO_ROOT/.venv"
  local py="$REPO_ROOT/.venv/bin/python"
  uv pip install --python "$py" "leanblueprint==$LEANBLUEPRINT_VERSION"
  # Override plasTeX with the git-master commit that renders the dependency
  # graph. PyPI plastex==3.1 crashes it; 3.0 drops the blueprint renderers.
  uv pip install --python "$py" --reinstall-package plastex "$PLASTEX_SPEC"
  mkdir -p "$LOCAL_BIN"
  ln -sf "$REPO_ROOT/.venv/bin/leanblueprint" "$LOCAL_BIN/leanblueprint"
  ln -sf "$REPO_ROOT/.venv/bin/plastex" "$LOCAL_BIN/plastex"
}

ensure_pdf() {
  [ "$WITH_PDF" -eq 1 ] || return 0
  log "Installing LaTeX (--pdf)"
  case "$PKG" in
    apt)
      sudo apt-get install -y --no-install-recommends \
        texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended \
        texlive-xetex latexmk
      ;;
    brew) brew install --cask basictex ;;
    *) warn "Install a LaTeX distribution manually to use --pdf." ;;
  esac
}

fetch_cache() {
  [ "$DO_CACHE" -eq 1 ] || return 0
  log "Fetching Mathlib cache"; lake exe cache get
}
do_build() {
  [ "$DO_BUILD" -eq 1 ] || return 0
  log "Building project (lake build)"; lake build
}

wire_path() {
  log "Wiring PATH into shell profiles"
  touch "$HOME/.profile"
  for profile in "$HOME/.profile" "$HOME/.bashrc" "$HOME/.zprofile" "$HOME/.zshrc"; do
    [ -e "$profile" ] || continue
    grep -qF '.elan/env' "$profile" 2>/dev/null || \
      printf '%s\n' '. "$HOME/.elan/env"' >> "$profile"
    grep -qF '.local/bin' "$profile" 2>/dev/null || \
      printf '%s\n' 'export PATH="$HOME/.local/bin:$PATH"' >> "$profile"
  done
}

main() {
  ensure_system_deps
  ensure_elan
  ensure_uv
  ensure_blueprint_venv
  ensure_pdf
  wire_path
  fetch_cache
  do_build
  log "Toolchain summary:"
  command -v lake >/dev/null 2>&1 && lake --version || warn "lake not on PATH (open a new shell)"
  command -v uv >/dev/null 2>&1 && uv --version
  command -v dot >/dev/null 2>&1 && dot -V
  "$LOCAL_BIN/leanblueprint" --version 2>/dev/null || warn "leanblueprint not found"
  cat <<'EOF'

Local blueprint preview (once the blueprint/ directory exists):
  leanblueprint web      # build HTML + dependency graph into blueprint/web/
  leanblueprint serve    # serve the compiled blueprint locally
Open a new shell (or `source ~/.profile`) so lake/uv/leanblueprint are on PATH.
EOF
}

main
```

- [ ] **Step 3: Syntax check and flag behavior**

Run:
```bash
cd /workspaces/lean-playground
chmod +x scripts/setup-dev.sh
bash -n scripts/setup-dev.sh && echo "syntax OK"
bash scripts/setup-dev.sh --help | head -3
bash scripts/setup-dev.sh --bogus; echo "exit=$?"
```
Expected: `syntax OK`; the usage header prints; the `--bogus` run prints an error and `exit=2`.

- [ ] **Step 4: Run the installer (install-only) and verify the toolchain**

Run:
```bash
bash scripts/setup-dev.sh --no-build --no-cache
export PATH="$HOME/.local/bin:$PATH"
test -d .venv && echo ".venv OK"
test -L "$HOME/.local/bin/leanblueprint" && test -L "$HOME/.local/bin/plastex" && echo "symlinks OK"
for c in dot uv leanblueprint plastex; do
  command -v "$c" >/dev/null && echo "$c: $(command -v "$c")"
done
leanblueprint --version
```
Expected: `.venv OK`, `symlinks OK`, all four commands resolve, and a leanblueprint version prints.

- [ ] **Step 5: Smoke test — the installed toolchain builds HTML + a dependency graph**

Run (isolated throwaway blueprint; the dummy project markers let `leanblueprint web` locate paths
without compiling Lean):
```bash
export PATH="$HOME/.local/bin:$PATH"
rm -rf /tmp/bp-smoke && mkdir -p /tmp/bp-smoke/blueprint/src/macros
cd /tmp/bp-smoke
printf 'leanprover/lean4:v4.32.0-rc1\n' > lean-toolchain
printf 'name = "t"\ndefaultTargets = ["T"]\n' > lakefile.toml
git init -q .
cat > blueprint/src/web.tex <<'TEX'
\documentclass{report}
\usepackage{amssymb, amsthm, amsmath}
\usepackage{hyperref}
\usepackage[showmore, dep_graph]{blueprint}
\input{macros/common}
\input{macros/web}
\home{https://example.com/}
\github{https://github.com/x/y}
\dochome{https://example.com/docs}
\title{Smoke}
\author{CI}
\begin{document}
\maketitle
\input{content}
\end{document}
TEX
cat > blueprint/src/plastex.cfg <<'CFG'
[general]
renderer=HTML5
copy-theme-extras=yes
plugins=plastexdepgraph plastexshowmore leanblueprint

[document]
toc-depth=3
toc-non-files=True

[files]
directory=../web/
split-level=0

[html5]
localtoc-level=1
extra-css=extra_styles.css
mathjax-dollars=False
CFG
: > blueprint/src/extra_styles.css
cat > blueprint/src/macros/common.tex <<'TEX'
\newtheorem{theorem}{Theorem}
\newtheorem{definition}[theorem]{Definition}
TEX
: > blueprint/src/macros/web.tex
cat > blueprint/src/content.tex <<'TEX'
\chapter{Smoke}
\begin{definition}[D]\label{def:d}\lean{Nat}\leanok The naturals. \end{definition}
\begin{theorem}[T]\label{thm:t}\lean{Nat.add_comm}\leanok\uses{def:d} Add comm. \end{theorem}
TEX
cd /tmp/bp-smoke/blueprint && leanblueprint web >/tmp/bp-smoke/web.log 2>&1 || true
test -f web/index.html && test -f web/dep_graph_document.html && echo "SMOKE_OK" || \
  { echo "SMOKE_FAILED"; tail -20 /tmp/bp-smoke/web.log; }
rm -rf /tmp/bp-smoke
```
Expected: `SMOKE_OK`. (Benign `pdflatex`/`dvisvgm` "vector imager" warnings may appear in the log.)

- [ ] **Step 6: Idempotency — a second run must not error or duplicate PATH lines**

Run:
```bash
cd /workspaces/lean-playground
before=$(grep -c '.local/bin' "$HOME/.profile" 2>/dev/null || echo 0)
bash scripts/setup-dev.sh --no-build --no-cache >/dev/null
after=$(grep -c '.local/bin' "$HOME/.profile" 2>/dev/null || echo 0)
echo "profile .local/bin lines: before=$before after=$after"
```
Expected: no error; `after` equals `before` (no duplicate lines; and both ≤ 1).

- [ ] **Step 7: Line-length check**

Run:
```bash
python3 - <<'PY'
for f in ["scripts/setup-dev.sh",".gitignore"]:
    bad=[(i,len(l.rstrip("\n"))) for i,l in enumerate(open(f),1) if len(l.rstrip("\n"))>100]
    print(f, bad or "≤100 ✓")
PY
```
Expected: both `≤100 ✓`.

- [ ] **Step 8: Commit**

```bash
git add scripts/setup-dev.sh .gitignore
git commit --no-gpg-sign -m "feat(dev): portable setup-dev.sh bootstrap (toolchain + blueprint)"
```

---

### Task 2: Devcontainer delegates to the bootstrap

**Files:**
- Modify: `.devcontainer/on-create.sh` (replace body with a delegation to `setup-dev.sh`)
- Modify: `.devcontainer/post-create.sh` (add a one-line comment; behavior unchanged)

**Interfaces:**
- Consumes: `scripts/setup-dev.sh` from Task 1. `devcontainer.json` is unchanged (its
  `onCreateCommand`/`postCreateCommand` already invoke these two scripts).

- [ ] **Step 1: Replace `.devcontainer/on-create.sh`**

Overwrite the file with:
```bash
#!/usr/bin/env bash
set -euo pipefail

# Delegate the full toolchain install to the portable bootstrap so the
# devcontainer, Codespaces, and a host machine all set up identically
# (scripts/setup-dev.sh). Skip the Mathlib cache + project build here;
# post-create.sh runs those, preserving the onCreate (install) /
# postCreate (build) split.
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bash "$REPO_ROOT/scripts/setup-dev.sh" --no-build --no-cache
```

- [ ] **Step 2: Add a clarifying comment to `.devcontainer/post-create.sh`**

Leave the existing commands intact; just insert this comment line immediately after the
`. "$HOME/.elan/env"` line:
```bash
# Tools were installed by on-create.sh -> scripts/setup-dev.sh. Here we only
# fetch the Mathlib cache and build (the slow, network-heavy steps).
```

- [ ] **Step 3: Syntax-check both scripts**

Run:
```bash
cd /workspaces/lean-playground
bash -n .devcontainer/on-create.sh && bash -n .devcontainer/post-create.sh && echo "syntax OK"
```
Expected: `syntax OK`.

- [ ] **Step 4: Run `on-create.sh` (idempotent) and confirm it succeeds**

Run:
```bash
bash .devcontainer/on-create.sh
echo "exit=$?"
export PATH="$HOME/.local/bin:$PATH"
command -v leanblueprint && command -v dot && echo "toolchain present"
```
Expected: `exit=0`; `toolchain present`. (Everything is already installed, so this exercises the
idempotent no-op paths and the delegation.)

- [ ] **Step 5: Line-length check**

Run:
```bash
python3 - <<'PY'
for f in [".devcontainer/on-create.sh",".devcontainer/post-create.sh"]:
    bad=[(i,len(l.rstrip("\n"))) for i,l in enumerate(open(f),1) if len(l.rstrip("\n"))>100]
    print(f, bad or "≤100 ✓")
PY
```
Expected: both `≤100 ✓`.

- [ ] **Step 6: Commit**

```bash
git add .devcontainer/on-create.sh .devcontainer/post-create.sh
git commit --no-gpg-sign -m "chore(devcontainer): delegate toolchain install to setup-dev.sh"
```

---

### Task 3: `scripts/setup-dev.ps1` — native-Windows bootstrap

**Files:**
- Create: `scripts/setup-dev.ps1`

**Interfaces:**
- Produces: `scripts/setup-dev.ps1 [-Pdf] [-NoBuild] [-NoCache]`, the Windows mirror of
  `setup-dev.sh`. Documented in Task 4.

> **Verification reality:** this environment has no Windows/PowerShell, so the script cannot be
> executed here. It is a faithful mirror of the bash recipe, verified by parse-check if `pwsh` is
> available and otherwise by a Windows user. WSL remains the tested Windows route (uses
> `setup-dev.sh`). This is stated in the docs (Task 4).

- [ ] **Step 1: Write `scripts/setup-dev.ps1`**

```powershell
#Requires -Version 5.1
<#
.SYNOPSIS
  Full dev-environment bootstrap for the NeuralNetworkProofs repo on native Windows.
  On Linux/macOS/WSL/Codespaces use scripts/setup-dev.sh instead.
.PARAMETER Pdf     Also install a LaTeX distribution (MiKTeX).
.PARAMETER NoBuild Skip 'lake build'.
.PARAMETER NoCache Skip 'lake exe cache get'.
#>
[CmdletBinding()]
param([switch]$Pdf, [switch]$NoBuild, [switch]$NoCache)
$ErrorActionPreference = 'Stop'

$LeanblueprintVersion = '0.0.20'
$PlastexUrl    = 'git+https://github.com/plastex/plastex.git'
$PlastexCommit = '4fe23e25565a4788f07077076211d21630a81cb0'
$PlastexSpec   = "plastex @ $PlastexUrl@$PlastexCommit"

$RepoRoot = Split-Path -Parent $PSScriptRoot
Set-Location $RepoRoot

function Log($m) { Write-Host "==> $m" -ForegroundColor Blue }

function Ensure-Winget($id) {
  $present = winget list --id $id -e 2>$null | Select-String -SimpleMatch $id
  if (-not $present) {
    Log "Installing $id"
    winget install --id $id -e --accept-source-agreements --accept-package-agreements
  } else { Log "$id already installed" }
}

Log 'Installing system dependencies (Git, Graphviz) via winget'
Ensure-Winget 'Git.Git'
Ensure-Winget 'Graphviz.Graphviz'

if (-not (Get-Command uv -ErrorAction SilentlyContinue)) {
  Log 'Installing uv'
  Invoke-RestMethod https://astral.sh/uv/install.ps1 | Invoke-Expression
}

if (-not (Get-Command elan -ErrorAction SilentlyContinue)) {
  Log 'Installing elan (Lean). If this fails, see https://leanprover-community.github.io/'
  # elan provides a Windows init script; fall back to scoop if unavailable.
  $init = Join-Path $env:TEMP 'elan-init.ps1'
  Invoke-RestMethod https://elan.lean-lang.org/elan-init.ps1 -OutFile $init
  powershell -ExecutionPolicy Bypass -File $init -y --default-toolchain none
}

Log 'Installing the blueprint toolchain into a repo-local venv (.venv)'
uv venv "$RepoRoot\.venv"
$py = "$RepoRoot\.venv\Scripts\python.exe"
uv pip install --python $py "leanblueprint==$LeanblueprintVersion"
uv pip install --python $py --reinstall-package plastex $PlastexSpec

if ($Pdf) { Log 'Installing LaTeX (MiKTeX)'; Ensure-Winget 'MiKTeX.MiKTeX' }
if (-not $NoCache) { Log 'Fetching Mathlib cache'; lake exe cache get }
if (-not $NoBuild) { Log 'Building project'; lake build }

Log "Done. Add '$RepoRoot\.venv\Scripts' to PATH, then preview with:"
Log '  leanblueprint web ; leanblueprint serve'
```

- [ ] **Step 2: Parse-check if PowerShell is available; otherwise record why not**

Run:
```bash
if command -v pwsh >/dev/null 2>&1; then
  pwsh -NoProfile -Command '
    $e=$null;
    [void][System.Management.Automation.Language.Parser]::ParseFile(
      "scripts/setup-dev.ps1",[ref]$null,[ref]$e);
    if ($e) { $e; exit 1 } else { "ps1 parse OK" }'
else
  echo "pwsh not available in this environment; .ps1 to be verified on Windows/WSL"
fi
```
Expected: `ps1 parse OK`, or the "pwsh not available" note (acceptable — see the task banner).

- [ ] **Step 3: Line-length check**

Run:
```bash
python3 - <<'PY'
f="scripts/setup-dev.ps1"
bad=[(i,len(l.rstrip("\n"))) for i,l in enumerate(open(f),1) if len(l.rstrip("\n"))>100]
print(f, bad or "≤100 ✓")
PY
```
Expected: `≤100 ✓`.

- [ ] **Step 4: Commit**

```bash
git add scripts/setup-dev.ps1
git commit --no-gpg-sign -m "feat(dev): setup-dev.ps1 bootstrap for native Windows (best-effort)"
```

---

### Task 4: Contributor documentation

**Files:**
- Create: `CONTRIBUTING.md`
- Modify: `README.md` ("Getting started" + "Contributing" sections)
- Modify: `CLAUDE.md` ("Build and verify" section — add a setup pointer)

**Interfaces:**
- Consumes: the script names + flags from Tasks 1 and 3. Every command shown must match them.

- [ ] **Step 1: Create `CONTRIBUTING.md`**

```markdown
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
```

- [ ] **Step 2: Replace the "Getting started" section in `README.md`**

Replace the current `## Getting started` section (its heading and the numbered list through the
"sample Lean file" step) with:
```markdown
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
```

- [ ] **Step 3: Replace the "Contributing" section body in `README.md`**

Replace the body of the `## Contributing` section (the intro line, the conventions bullet list, and
the closing paragraph) with:
```markdown
## Contributing

Contributions are welcome. See [CONTRIBUTING.md](CONTRIBUTING.md) for how to set up a development
environment (container or host), preview the blueprint locally, and the conventions we follow (no
`sorry`, axiom-clean headlines, minimal imports, ≤100-codepoint lines). `CLAUDE.md` is the full
contributor guide.
```

- [ ] **Step 4: Add a setup pointer to `CLAUDE.md`**

In `CLAUDE.md`, immediately below the `## Build and verify` heading (before the first code fence),
insert this paragraph:
```markdown
To set up a dev environment (container or host) plus the blueprint preview toolchain, run
`scripts/setup-dev.sh` — see `CONTRIBUTING.md`. Preview the blueprint with `leanblueprint web`
then `leanblueprint serve`.

```

- [ ] **Step 5: Verify links, freshness, and command/flag accuracy**

Run:
```bash
cd /workspaces/lean-playground
test -f CONTRIBUTING.md && echo "CONTRIBUTING.md exists"
grep -q "CONTRIBUTING.md" README.md && echo "README links CONTRIBUTING"
grep -q "sample Lean file" README.md && echo "STALE STEP STILL PRESENT" || echo "stale step removed"
grep -q "scripts/setup-dev.sh" CLAUDE.md && echo "CLAUDE has setup pointer"
# flags mentioned in docs must exist in the script
for flag in -- --pdf --no-build --no-cache; do :; done
grep -qE '\-\-pdf' CONTRIBUTING.md && grep -qE '\-\-pdf' scripts/setup-dev.sh && echo "flags match"
```
Expected: `CONTRIBUTING.md exists`, `README links CONTRIBUTING`, `stale step removed`,
`CLAUDE has setup pointer`, `flags match`.

- [ ] **Step 6: Line-length check on all touched docs**

Run:
```bash
python3 - <<'PY'
for f in ["CONTRIBUTING.md","README.md","CLAUDE.md"]:
    bad=[(i,len(l.rstrip("\n"))) for i,l in enumerate(open(f),1) if len(l.rstrip("\n"))>100]
    print(f, bad or "≤100 ✓")
PY
```
Expected: all three `≤100 ✓`.

- [ ] **Step 7: Commit**

```bash
git add CONTRIBUTING.md README.md CLAUDE.md
git commit --no-gpg-sign -m "docs: document dev setup (container + host) and blueprint preview"
```

---

## Self-Review

**1. Spec coverage** (against the approved bootstrap spec):
- Portable `setup-dev.sh` (elan, uv, graphviz, blueprint venv, `--pdf`, cache, build, idempotent,
  PATH wiring) → Task 1. ✓
- Validated recipe (leanblueprint 0.0.20 + plastexdepgraph 0.0.5 + plasTeX git commit; venv +
  symlinks; no LaTeX for web) → Task 1 Step 2 + Global Constraints; proven by Task 1 Step 5. ✓
- Cross-platform apt/brew + WSL/Codespaces detection; manual-deps message for other managers →
  Task 1 (`ensure_system_deps`, platform detection). ✓
- Native Windows `.ps1` → Task 3 (best-effort, parse-checked, flagged unverified). ✓
- Devcontainer + Codespaces wiring (on-create delegates `--no-build --no-cache`; post-create keeps
  cache+build+chown; devcontainer.json unchanged) → Task 2. ✓
- Flags `--pdf`/`--no-build`/`--no-cache`, non-interactive, re-runnable → Task 1 (parsing +
  idempotency Step 6). ✓
- Documentation in CONTRIBUTING.md (both paths + preview + conventions), README (both paths +
  pointer, stale step fixed), CLAUDE (setup pointer) → Task 4. ✓
- Verification: PATH/version checks + scaffold-build-cleanup smoke test → Task 1 Steps 4–5; docs
  accuracy → Task 4 Step 5. ✓
- Out of scope respected: no `.lean`/toolchain changes (only `scripts/`, `.devcontainer/`,
  `.gitignore`, docs). ✓

**2. Placeholder scan:** none. The plasTeX commit, package versions, apt/brew package sets, and all
commands are concrete. The one genuinely unverifiable piece (native-Windows `.ps1`) is called out
explicitly with its parse-check fallback, not left vague.

**3. Consistency:** the recipe constants (`leanblueprint==0.0.20`, plasTeX commit
`4fe23e2…`, `.venv/`, `~/.local/bin` symlinks, flags `--pdf`/`--no-build`/`--no-cache`) are
identical across Global Constraints, Task 1 (bash), Task 3 (PowerShell, `-Pdf`/`-NoBuild`/
`-NoCache`), and Task 4 (docs). The devcontainer split (on-create install / post-create build)
matches the spec.

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-07-10-dev-toolchain-bootstrap.md`. Two
execution options:

**1. Subagent-Driven (recommended)** — dispatch a fresh subagent per task, review between tasks,
fast iteration.

**2. Inline Execution** — execute tasks in this session using executing-plans, batch execution
with checkpoints.

Which approach?
