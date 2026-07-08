# Resolve repo loose ends — design

**Goal:** Close the documentation, CI, and local-branch loose ends surfaced by the 2026-07-08
whole-repo review, so the repository is internally consistent before the next work. No proof,
theorem-statement, or axiom changes.

## Context

The whole-repo review found the formalization healthy: `main` builds clean (3581 jobs, zero
warnings); all 7 headlines are axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorries);
no `sorry`/`admit`/`maxHeartbeats`/`native_decide`; no blanket `import Mathlib` anywhere; working
tree clean; no open PRs; remote has only `main`. The remaining loose ends are documentation
staleness, one CI gap, and local-branch clutter — none affecting correctness.

## Scope

Delivered as ONE `chore:` PR off `main` (three file edits) plus a local-only branch prune.

### 1. `CLAUDE.md` — reflect the completed Monotone development

Currently it says "Two developments are complete", lists monotone nets as "Next planned work", omits
Monotone from the layout table, and calls `UniversalApproximation/Monotone/` "reserved for the
future". Updates:

- **"What this is":** three complete, `sorry`-free developments — Cybenko, Leshno, and **Monotone**.
  Monotone = Mikulincer–Reichman (`monotone_interpolation`, `monotone_approximation`) + Sartor
  (`saturating_interpolation` = Thm 3.5; `nonpos_weight_universal` = Prop 3.11; plus Prop 3.8/3.10),
  with monotone one-sided-saturating activations.
- Remove the "Next planned work: … monotonic …" sentence.
- **Layout table:** add a Monotone row (`…/Monotone/` + `Monotone.lean`, namespace
  `UniversalApproximation.Monotone`); fix the root row to "re-exports the three UAT roots so
  `lake build` verifies all headlines".
- Remove the "reserved for the future monotone-NN work" sentence.

### 2. `NeuralNetworkProofs.lean` — complete the headline list

The root docstring claims it "builds and verifies all headlines" but lists only 4 of 7. Add the
missing three: `Cybenko.universal_approximation_eps`, `Monotone.saturating_interpolation`,
`Monotone.nonpos_weight_universal`. Imports/build are already correct — docstring only.

### 3. `.github/workflows/ci.yml` — widen the blanket-import gate repo-wide

The "ForMathlib minimal-imports gate" greps only `NeuralNetworkProofs/ForMathlib/`. Widen the grep
to `NeuralNetworkProofs/` (whole tree) so any future blanket `import Mathlib` fails CI, and reword
the step + message for the repo-wide scope. The repo is already blanket-import-free, so the widened
gate passes immediately — no ordering risk.

### 4. Local branch cleanup (no PR)

Delete `feat/leshno-uat` (drops obsolete commit `66a6375`, a design spec for already-filled Leshno
leaves) and the ~10 already-merged local branches (0 commits ahead of `main`). Keep `main`. Remote
already has only `main`.

## Verification

- `lake build NeuralNetworkProofs` green, zero warnings.
- `lake env lean scripts/check_sorry_free.lean` — all 7 headlines `[propext, Classical.choice,
  Quot.sound]`.
- The widened CI gate passes (`grep` finds no blanket `import Mathlib` in `NeuralNetworkProofs/`).
- Diffs are documentation + CI-config only — no `.lean` proof or statement changes.

## Out of scope

- Archival mentions of commit-signing / "monotone planned" in `docs/superpowers/plans/*` and
  `.claude/skills/*` (historical records; left as-is).
- The GitHub "signed commits" ruleset (already disabled; left as-is).
- Any change to a proof, theorem statement, or the formalization itself.
