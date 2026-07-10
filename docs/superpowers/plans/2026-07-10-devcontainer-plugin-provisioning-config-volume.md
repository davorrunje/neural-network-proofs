# Dev Container Claude Plugin Provisioning & Config Volume — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Auto-install the Claude Code plugins this repo declares (superpowers,
whose `brainstorming` skill the project uses) on container build, and move
`~/.claude` to a container-private named volume; retire the last live
`lean-playground` reference.

**Architecture:** A checked-in manifest (`.devcontainer/claude-plugins.txt`) is
consumed by an idempotent, non-fatal provisioning script
(`.devcontainer/provision-claude-plugins.sh`) invoked from `post-create.sh` after
an ownership guard. `devcontainer.json` swaps the `~/.claude` bind mount for a
named volume. `.claude/settings.json` and `README.md` are updated to the
`superpowers-dev` marketplace and the named-volume model.

**Tech Stack:** Dev Containers (devcontainer.json), Bash, the `claude` plugin
CLI, Docker named volumes.

## Global Constraints

- **Line length ≤ 100 codepoints** (repo convention; measure codepoints, not
  bytes).
- **Provisioning and the ownership guard must be non-fatal** — a missing `claude`
  CLI, no network, not-logged-in, or an install failure must never fail the
  container build.
- **Marketplace:** `superpowers-dev`, source `https://github.com/obra/superpowers.git`
  (matches the sibling `mononet` repo). The plugin id is `superpowers@superpowers-dev`.
- **No secrets** in the repo; provisioning uses the already logged-in `claude` CLI.
- **Design source of truth:** `docs/superpowers/specs/2026-07-10-devcontainer-plugin-provisioning-config-volume-design.md`.

---

### Task 1: Plugin manifest + provisioning script

**Files:**
- Create: `.devcontainer/claude-plugins.txt`
- Create: `.devcontainer/provision-claude-plugins.sh`

**Interfaces:**
- Produces: an executable script `.devcontainer/provision-claude-plugins.sh` that
  reads `.devcontainer/claude-plugins.txt` and installs each listed plugin;
  always exits 0. Consumed by Task 2 (`post-create.sh` calls it).
- Manifest line format: `<marketplace-source>  <plugin@marketplace>`
  (whitespace-separated — tab or spaces), `#` comments and blank lines ignored.

- [ ] **Step 1: Create the manifest**

Create `.devcontainer/claude-plugins.txt` (the field separator below is
whitespace; a single space is fine — `awk` splits on any whitespace):

```
# Claude Code plugins provisioned for this repo.
#
# One plugin per line:  <marketplace-source>  <plugin@marketplace>
# - marketplace-source: URL / GitHub repo / path passed to
#   `claude plugin marketplace add`
# - plugin@marketplace:  id passed to `claude plugin install ... --scope user`
#
# Consumed by `.devcontainer/provision-claude-plugins.sh`, which runs in the
# devcontainer (via post-create) and can also be run by hand. `#` and blank
# lines are ignored.

https://github.com/obra/superpowers.git superpowers@superpowers-dev
```

- [ ] **Step 2: Create the provisioning script**

Create `.devcontainer/provision-claude-plugins.sh`:

```bash
#!/usr/bin/env bash
# Provision Claude Code plugins from the checked-in manifest
# (.devcontainer/claude-plugins.txt). Idempotent and non-fatal by design: a
# missing `claude` CLI, no network, not-logged-in, or an install failure must
# NEVER break the container build — we warn and continue (always exit 0).
#
# Runs in the devcontainer via post-create.sh; can also be run by hand.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MANIFEST="${SCRIPT_DIR}/claude-plugins.txt"

warn() { echo "provision-claude-plugins: $*" >&2; }

if ! command -v claude >/dev/null 2>&1; then
    warn "'claude' CLI not found on PATH; skipping plugin provisioning."
    exit 0
fi
if [ ! -f "${MANIFEST}" ]; then
    warn "manifest ${MANIFEST} not found; nothing to provision."
    exit 0
fi

installed="$(claude plugin list 2>/dev/null || true)"
markets="$(claude plugin marketplace list 2>/dev/null || true)"

while IFS= read -r line || [ -n "${line}" ]; do
    # strip comments / blanks
    line="${line%%#*}"
    [ -z "${line//[[:space:]]/}" ] && continue

    # two whitespace-separated fields: <source> <plugin@marketplace>
    src="$(printf '%s' "${line}" | awk '{print $1}')"
    plugin="$(printf '%s' "${line}" | awk '{print $2}')"
    if [ -z "${src}" ] || [ -z "${plugin}" ]; then
        warn "malformed line: ${line}"
        continue
    fi

    market="${plugin#*@}"    # marketplace name

    # add marketplace if not already known (match by name or source)
    if ! printf '%s' "${markets}" | grep -qiF "${market}" \
        && ! printf '%s' "${markets}" | grep -qF "${src}"; then
        echo ">>> adding marketplace ${src}"
        claude plugin marketplace add "${src}" </dev/null >/dev/null 2>&1 \
            || warn "failed to add marketplace ${src} (continuing)"
    fi

    # install plugin if not already installed (match the full id so a same-named
    # plugin from a different marketplace does not mask this one)
    if printf '%s' "${installed}" | grep -qiF "${plugin}"; then
        echo ">>> ${plugin} already installed; skipping"
    else
        echo ">>> installing ${plugin}"
        claude plugin install "${plugin}" --scope user </dev/null >/dev/null 2>&1 \
            || warn "failed to install ${plugin} (continuing)"
    fi
done < "${MANIFEST}"

echo ">>> plugin provisioning done"
exit 0
```

- [ ] **Step 3: Make the script executable**

Run: `chmod +x .devcontainer/provision-claude-plugins.sh`

- [ ] **Step 4: Syntax check**

Run: `bash -n .devcontainer/provision-claude-plugins.sh && echo SYNTAX_OK`
Expected: `SYNTAX_OK` (no other output).

- [ ] **Step 5: Test the non-fatal "no claude CLI" branch**

Run (restrict PATH so `claude` is not found, but coreutils still are):

```bash
PATH="/usr/bin:/bin" bash .devcontainer/provision-claude-plugins.sh; echo "exit=$?"
```

Expected: a line `provision-claude-plugins: 'claude' CLI not found on PATH;
skipping plugin provisioning.` on stderr, then `exit=0`.

- [ ] **Step 6: Test a real run (installs superpowers@superpowers-dev)**

Run: `bash .devcontainer/provision-claude-plugins.sh; echo "exit=$?"`
Expected: `>>> adding marketplace https://github.com/obra/superpowers.git` (first
run only), `>>> installing superpowers@superpowers-dev` (or
`>>> superpowers already installed; skipping`), `>>> plugin provisioning done`,
then `exit=0`.

- [ ] **Step 7: Test idempotency (second run skips)**

Run: `bash .devcontainer/provision-claude-plugins.sh; echo "exit=$?"`
Expected: `>>> superpowers already installed; skipping`, `>>> plugin
provisioning done`, `exit=0` (no marketplace re-add, no re-install).

- [ ] **Step 8: Confirm the resolved marketplace name**

Run: `claude plugin marketplace list`
Expected: a marketplace named `superpowers-dev` is listed (sourced from
`obra/superpowers`). If the resolved name differs, update both the manifest
(Step 1) and `settings.json` (Task 4) to the actual name before proceeding.

- [ ] **Step 9: Commit**

```bash
git add .devcontainer/claude-plugins.txt .devcontainer/provision-claude-plugins.sh
git commit -m "feat(devcontainer): add Claude plugin manifest + provisioning script"
```

---

### Task 2: Ownership guard + provisioning hook in post-create.sh

**Files:**
- Modify: `.devcontainer/post-create.sh`

**Interfaces:**
- Consumes: `.devcontainer/provision-claude-plugins.sh` (Task 1).
- The script runs during `postCreateCommand` with cwd = the workspace folder
  (`/workspaces/neural-network-proofs`), so the relative path
  `.devcontainer/provision-claude-plugins.sh` resolves (same convention as the
  existing `bash .devcontainer/post-create.sh` invocation).

- [ ] **Step 1: Replace the chown block and add the provisioning call**

In `.devcontainer/post-create.sh`, replace this block:

```bash
# ~/.claude is a host bind mount (see devcontainer.json) so Claude Code session
# history, memory, login/auth, and installed plugins persist across container
# rebuilds. Ensure it is writable by the vscode user regardless of host ownership.
sudo chown -R vscode:vscode "$HOME/.claude" 2>/dev/null || true

echo "Lean + Mathlib build complete."
```

with:

```bash
# ~/.claude is a container-private named volume (see devcontainer.json) so Claude
# Code session history, memory, login/auth, and installed plugins persist across
# rebuilds. Docker initialises named volumes root-owned, so claim the mount point
# for the vscode user before anything writes to it — idempotent: only acts when
# the dir exists and is not yet writable. Without this the first `claude plugin …`
# call below fails with "Permission denied".
if [ -d "$HOME/.claude" ] && [ ! -w "$HOME/.claude" ]; then
  sudo chown "$(id -u):$(id -g)" "$HOME/.claude"
fi

# Auto-install the Claude Code plugins this repo declares
# (.devcontainer/claude-plugins.txt) — notably superpowers and its brainstorming
# skill. Best-effort: the script always exits 0 and never fails the build.
echo ">>> provisioning Claude Code plugins"
bash .devcontainer/provision-claude-plugins.sh

echo "Lean + Mathlib build complete."
```

- [ ] **Step 2: Syntax check**

Run: `bash -n .devcontainer/post-create.sh && echo SYNTAX_OK`
Expected: `SYNTAX_OK`.

- [ ] **Step 3: Verify the provisioning call resolves from the workspace root**

Run: `cd /workspaces/neural-network-proofs && test -f .devcontainer/provision-claude-plugins.sh && echo PATH_OK`
Expected: `PATH_OK` (confirms the relative path used in post-create.sh exists
from the cwd postCreateCommand runs in).

- [ ] **Step 4: Commit**

```bash
git add .devcontainer/post-create.sh
git commit -m "feat(devcontainer): guard ~/.claude ownership + provision plugins in post-create"
```

---

### Task 3: Switch ~/.claude to a container-private named volume

**Files:**
- Modify: `.devcontainer/devcontainer.json`

- [ ] **Step 1: Remove the initializeCommand line**

In `.devcontainer/devcontainer.json`, delete this line entirely (Docker creates
the named volume automatically; the host playground dir is no longer used):

```json
  "initializeCommand": "mkdir -p ${localEnv:HOME}/.claude-devcontainer/lean-playground",
```

- [ ] **Step 2: Replace the bind mount with a named volume**

Replace the `mounts` array:

```json
  "mounts": [
    "source=${localEnv:HOME}/.claude-devcontainer/lean-playground,target=/home/vscode/.claude,type=bind,consistency=cached"
  ],
```

with:

```json
  "mounts": [
    "source=neural-network-proofs-claude-config,target=/home/vscode/.claude,type=volume"
  ],
```

- [ ] **Step 3: Validate JSON**

Run: `python3 -m json.tool .devcontainer/devcontainer.json >/dev/null && echo JSON_OK`
Expected: `JSON_OK`.

- [ ] **Step 4: Confirm the stale name is gone and the volume is present**

Run:

```bash
! grep -q 'lean-playground' .devcontainer/devcontainer.json \
  && grep -q 'neural-network-proofs-claude-config' .devcontainer/devcontainer.json \
  && echo NAMES_OK
```

Expected: `NAMES_OK`.

- [ ] **Step 5: Commit**

```bash
git add .devcontainer/devcontainer.json
git commit -m "feat(devcontainer): use a container-private named volume for ~/.claude"
```

---

### Task 4: Point settings.json at the superpowers-dev marketplace

**Files:**
- Modify: `.claude/settings.json`

- [ ] **Step 1: Update the marketplace and enabled-plugin keys**

Replace the whole contents of `.claude/settings.json` with:

```json
{
  "extraKnownMarketplaces": {
    "superpowers-dev": {
      "source": {
        "source": "github",
        "repo": "obra/superpowers"
      }
    }
  },
  "enabledPlugins": {
    "superpowers@superpowers-dev": true
  },
  "enabledMcpjsonServers": [
    "lean-lsp"
  ]
}
```

(If Task 1 Step 8 found a marketplace name other than `superpowers-dev`, use that
name for both the `extraKnownMarketplaces` key and the `enabledPlugins` key.)

- [ ] **Step 2: Validate JSON**

Run: `python3 -m json.tool .claude/settings.json >/dev/null && echo JSON_OK`
Expected: `JSON_OK`.

- [ ] **Step 3: Confirm no stale marketplace id remains**

Run:

```bash
! grep -q 'claude-plugins-official' .claude/settings.json \
  && grep -q 'superpowers@superpowers-dev' .claude/settings.json \
  && echo SETTINGS_OK
```

Expected: `SETTINGS_OK`.

- [ ] **Step 4: Commit**

```bash
git add .claude/settings.json
git commit -m "chore(devcontainer): enable superpowers via the superpowers-dev marketplace"
```

---

### Task 5: Rewrite the README Claude-state section

**Files:**
- Modify: `README.md:64-75`

- [ ] **Step 1: Replace the two Claude-state paragraphs**

In `README.md`, replace this block (currently lines 64–75):

```markdown
Claude Code state persists across container rebuilds: the container's entire
`~/.claude` directory is bind-mounted to `~/.claude-devcontainer/lean-playground`
on your host (see the `mounts` entry in `.devcontainer/devcontainer.json`). This
covers session history, memory, **login/auth, and installed plugins**, so you do
not re-authenticate or reinstall plugins after a rebuild. Note that this means
your Claude credentials live in that host folder — it is on your host disk, never
in the repo.

The [`superpowers`](https://github.com/obra/superpowers) plugin is declared in
`.claude/settings.json` (`extraKnownMarketplaces` + `enabledPlugins`), so a fresh
container is prompted to install it from the official marketplace rather than
relying on it already being present.
```

with:

```markdown
Claude Code state persists across container rebuilds: the container's entire
`~/.claude` directory lives on a container-private Docker **named volume**
(`neural-network-proofs-claude-config`, see the `mounts` entry in
`.devcontainer/devcontainer.json`). This covers session history, memory,
**login/auth, and installed plugins**, so you do not re-authenticate or reinstall
plugins after a rebuild. The volume is isolated from your host filesystem; reset
it with `docker volume ls | grep neural-network-proofs-claude-config` then
`docker volume rm <name>`.

The [`superpowers`](https://github.com/obra/superpowers) plugin (its
`brainstorming` skill and more) is declared in `.claude/settings.json` and
**auto-installed on build**: `post-create.sh` runs
`.devcontainer/provision-claude-plugins.sh`, which installs everything listed in
`.devcontainer/claude-plugins.txt` from the `superpowers-dev` marketplace. This
is best-effort — if the `claude` CLI is not logged in or offline, the build still
succeeds and you can rerun the script by hand.
```

- [ ] **Step 2: Confirm the stale name is gone and the new model is described**

Run:

```bash
! grep -q 'lean-playground' README.md \
  && grep -q 'neural-network-proofs-claude-config' README.md \
  && grep -q 'provision-claude-plugins.sh' README.md \
  && echo README_OK
```

Expected: `README_OK`.

- [ ] **Step 3: Check line length ≤ 100 codepoints for the edited block**

Run:

```bash
awk 'length($0) > 100 {print FILENAME":"NR": "length($0)}' README.md
```

Expected: no output (no line exceeds 100 codepoints). If a line is flagged,
rewrap it.

- [ ] **Step 4: Commit**

```bash
git add README.md
git commit -m "docs(readme): describe named-volume + plugin auto-provisioning; drop lean-playground"
```

---

### Task 6: Full container-rebuild verification (integration)

This task has no code — it validates the end-to-end behavior that unit steps
cannot. Run it after Tasks 1–5 are merged, from a host with Docker.

**Files:** none.

- [ ] **Step 1: Rebuild the container from scratch**

In VS Code: *Dev Containers: Rebuild Container* (or, with the CLI,
`devcontainer up --workspace-folder . --remove-existing-container`). To exercise
a truly fresh `~/.claude`, first remove the volume:
`docker volume ls | grep neural-network-proofs-claude-config` then
`docker volume rm <name>`.

- [ ] **Step 2: Verify the plugin auto-installed**

In the container terminal, run: `claude plugin list`
Expected: `superpowers@superpowers-dev` is listed — with no manual install step.
(A one-time `claude` login may be required first for the install to succeed; the
build itself does not fail without it.)

- [ ] **Step 3: Verify the brainstorming skill is available**

Start `claude`, then confirm `/superpowers:brainstorming` is offered.
Expected: the skill is present.

- [ ] **Step 4: Verify persistence across rebuild**

Rebuild again *without* removing the volume. Run `claude plugin list`.
Expected: superpowers still present (no reinstall needed); sessions retained.

- [ ] **Step 5: Verify best-effort behavior**

Confirm the container came up green even though provisioning is best-effort
(check the post-create logs show `>>> plugin provisioning done`).
Expected: container started successfully; provisioning logged, non-fatal.

- [ ] **Step 6 (optional cleanup): remove the orphaned official-marketplace plugin**

On any machine where superpowers was previously installed from the old
marketplace, remove the now-unreferenced copy:
`claude plugin uninstall superpowers@claude-plugins-official` (ignore if absent).
