#!/usr/bin/env bash
# Generate a Mistral Vibe config.toml for the given backend.
# Usage: gen-vibe-config.sh <local|api> <out_path>
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/common.sh"

backend="${1:?usage: gen-vibe-config.sh <local|api> <out_path>}"
out="${2:?usage: gen-vibe-config.sh <local|api> <out_path>}"
mkdir -p "$(dirname "$out")"

case "$backend" in
  local)
    cat > "$out" <<'TOML'
# Leanstral local flavor — llama-server on 127.0.0.1:8080 (OpenAI-compatible).
# default_agent is the custom `lean-local` agent (installed by on-create-local.sh):
# vibe's builtin `lean` agent forces the Mistral-cloud endpoint via its profile
# overrides, so it cannot be used against the local server.
active_model = "leanstral-local"
default_agent = "lean-local"
enable_telemetry = false
enable_auto_update = false

[[providers]]
name = "local"
api_base = "http://127.0.0.1:8080/v1"
api_style = "openai"
backend = "generic"

[[models]]
name = "leanstral-1.5"
provider = "local"
alias = "leanstral-local"
TOML
    ;;
  api)
    cat > "$out" <<'TOML'
# Leanstral API flavor — Mistral Labs hosted endpoint.
active_model = "leanstral-api"
default_agent = "lean"

[[providers]]
name = "mistral"
api_base = "https://api.mistral.ai/v1"
api_style = "openai"
backend = "generic"
api_key_env = "MISTRAL_API_KEY"

[[models]]
name = "leanstral-1-5"
provider = "mistral"
alias = "leanstral-api"
TOML
    ;;
  *) log "unknown backend: $backend (want local|api)"; exit 2 ;;
esac

# Shared MCP block appended for both backends (one copy).
cat >> "$out" <<'TOML'

[[mcp_servers]]
name = "lean-lsp"
transport = "stdio"
command = "uvx"
args = ["lean-lsp-mcp"]
TOML

log "wrote Vibe config ($backend): $out"
