# Dev Container Claude Plugin Provisioning & Config Volume — Design

**Date:** 2026-07-10
**Status:** Approved

## Goal

Make the dev container **auto-install the Claude Code plugins the project
declares**, and give `~/.claude` a **clean, container-private, persistent store**
that survives rebuilds without host-filesystem coupling. Today
`.claude/settings.json` *enables* the superpowers plugin (whose `brainstorming`
skill the project relies on — see `docs/superpowers/specs/`), but nothing in the
container ever *installs* it: `post-create.sh` only builds Lean/Mathlib and
chowns `~/.claude`. So on any fresh setup the plugin is silently missing until
installed by hand.

This ports the plugin-provisioning slice of the sibling `mononet` repo's dev
container work (mononet PR #73) and adopts its container-private
named-volume model for `~/.claude`, adapted to this project's single-flavor
container.

## Non-goals

- **No host↔container session unification / no symlinks.** Sessions are durable
  (they persist in the named volume across rebuilds) but isolated from the
  host's interactive Claude. The host-side-symlink session-sharing mechanism
  from mononet PR #73 is deliberately not ported — its only purpose is remapping
  the host session slug, and it relies on Docker following a symlinked mount
  source.
- Not ported from mononet PR #73 (multi-flavor / GPU / Python specific): `.venv`
  isolation volumes, GPU-base locale fixes.
- No secrets or host credentials committed; provisioning uses the already
  logged-in `claude` CLI inside the container.

## Baseline (what exists today)

- Single flat `.devcontainer/` (no `shared/`, no flavors): `devcontainer.json`,
  `on-create.sh`, `post-create.sh`, plus the `features/no-gpg` feature.
- `~/.claude` is a **bind mount** to a dedicated host dir:
  `source=${localEnv:HOME}/.claude-devcontainer/lean-playground` →
  `target=/home/vscode/.claude`, created by
  `initializeCommand: mkdir -p …/lean-playground`. (The `lean-playground` path
  segment is a leftover from the project's pre-rename name; the reorg-rename
  work left the workspace/mount paths on the old name as environment-level and
  out of scope. This design removes that bind mount entirely, retiring the
  stale name.)
- `post-create.sh` does `sudo chown -R vscode:vscode ~/.claude` and nothing
  provisions plugins.

## Design

### A. Plugin auto-provisioning

**A1. `.devcontainer/claude-plugins.txt`** — checked-in manifest, single source
of truth. One plugin per line, two whitespace-separated fields:
`<marketplace-source>  <plugin@marketplace>`. Comments (`#`) and blank lines
ignored. Seeded with:

```
https://github.com/obra/superpowers.git	superpowers@superpowers-dev
```

Uses the `superpowers-dev` marketplace (the obra repo added directly), matching
mononet.

**A2. `.devcontainer/provision-claude-plugins.sh`** — idempotent, non-fatal port
of mononet's script:

- `exit 0` (warn) if the `claude` CLI is absent or the manifest is missing.
- For each manifest line: add the marketplace if not already known (match by
  name or source), then `claude plugin install <plugin@marketplace> --scope user`
  if not already installed.
- Every failing step warns and continues — provisioning must **never** fail the
  container build (no network, install error, not logged in, etc.).

**A3. `post-create.sh`** — after the Lean build and the ownership guard (B2),
add a `>>> provisioning Claude Code plugins` step invoking A2.

**A4. `.claude/settings.json`** — update the `enabledPlugins` key from
`superpowers@claude-plugins-official` to `superpowers@superpowers-dev` so the
enabled key resolves to the plugin the manifest installs.

### B. Container-private `~/.claude` named volume

**B1. `devcontainer.json`**:

- Replace the `lean-playground` bind mount with a container-private named
  volume: `source=neural-network-proofs-claude-config,target=/home/vscode/.claude,type=volume`.
  Plugins, auth, memory, and sessions all persist in the volume across rebuilds.
- Remove `initializeCommand` (its only job was `mkdir`-ing the now-unused host
  playground dir; Docker creates the named volume automatically).

**B3. `README.md`** — rewrite the "Claude Code state persists…" paragraph
(currently describes the `~/.claude-devcontainer/lean-playground` bind mount) to
describe the named volume instead. This also retires the last live occurrence of
the stale `lean-playground` name.

**B2. Ownership guard.** Docker initializes named volumes **root-owned**, so the
non-root `vscode` user cannot write to `~/.claude` until we take ownership —
without this, the first `claude plugin …` call fails with `Permission denied`.
Replace `post-create.sh`'s unconditional `chown -R` with an idempotent, guarded
top-level chown (mononet's pattern): only act when the dir exists and is not
writable, and chown just the mount point (the volume starts empty, and all
subsequent writes are already as `vscode`). This runs **before** A3.

## Error handling

- Plugin provisioning: `set -u`, every `claude` call guarded with `|| warn …`;
  exits 0 regardless — never blocks container start.
- Ownership guard: conditional (`[ -d ] && [ ! -w ]`), so it is a no-op on
  rebuilds where the volume is already owned.

## Migration note

Switching `~/.claude` from the existing `lean-playground` bind mount to a fresh
named volume means the first rebuild starts with an empty `~/.claude`: users
re-authenticate the `claude` CLI once, and provisioning reinstalls the plugins.
A stale volume can be reset with `docker volume rm <project>_neural-network-proofs-claude-config`
(find the exact name via `docker volume ls | grep neural-network-proofs-claude-config`).

## Testing

Rebuild the container from scratch and confirm:

1. `claude plugin list` shows `superpowers@superpowers-dev` with **no** manual
   install step.
2. `/superpowers:brainstorming` is available in a fresh session.
3. Sessions/plugins persist across a container rebuild (named volume retained).
4. Provisioning with no network / not-logged-in `claude` warns but the container
   still comes up (best-effort guarantee).
