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
  # A .venv carried in on the bind-mounted workspace from a previous container
  # points its python symlink at that container's uv-managed interpreter, which
  # is gone after a rebuild — leaving a dangling symlink that later `uv pip`
  # calls reject. Recreate whenever the interpreter isn't executable (covers
  # both "absent" and "stale/broken"). -x follows the symlink, so a dangling
  # link tests false.
  if [ ! -x "$REPO_ROOT/.venv/bin/python" ]; then
    rm -rf "$REPO_ROOT/.venv"
    uv venv "$REPO_ROOT/.venv"
  fi
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
