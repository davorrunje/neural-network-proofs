# UAT Namespace Unification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split the topic-named `UniversalApproximation.Monotone` into author-named
`UniversalApproximation.MikulincerReichman` + `UniversalApproximation.Sartor` (keeping the shared
`ActStack` core under `Monotone`), add a `UniversalApproximation.lean` results aggregator, and
propagate the rename across Lean, the leanblueprint + `checkdecls` gate, the sorry-free gate,
`NeuralNetworkProofs.lean`, README, and CLAUDE.md.

**Architecture:** Pure rename/move of existing sorry-free code — no proof or statement content
changes. Each moved file is `git mv`'d, its `namespace` line changed, and `open
UniversalApproximation.Monotone` added so its unqualified uses of shared-core decls
(`ActStack`/`MonoNet`/`heaviside`/`Layer`/…) still resolve. Tasks are ordered so `lake build` +
the sorry-free gate stay green at every commit; the blueprint (a separate CI gate) is updated last.

**Tech Stack:** Lean 4, Mathlib, Lake 5.0.0, leanblueprint + checkdecls + doc-gen4.

**Spec:** `docs/superpowers/specs/2026-07-10-uat-namespace-unification-design.md`.

## Global Constraints

- **No `sorry`/`admit`; no proof/statement changes.** This is a rename/move only. Axiom profiles
  must be *identical* to before (`[propext, Classical.choice, Quot.sound]` for every headline).
- **Line length ≤ 100 codepoints** (measure codepoints, not bytes).
- **Minimal, precise imports** — unchanged by this refactor; do not add blanket imports.
- **File headers unchanged** (Apache-2.0 + `Authors: Davor Runje`); update only module docstrings
  where a file's role changes.
- **Namespaces:** shared core stays `UniversalApproximation.Monotone`; new
  `UniversalApproximation.MikulincerReichman` and `UniversalApproximation.Sartor`; `Runje`
  unchanged. Theorem/def **base names are unchanged** — only the namespace prefix moves.
- **Build gotcha (CLAUDE.md):** a rename invalidating all local oleans forces a from-scratch
  rebuild that can hit `Too many open files` (EMFILE). If `lake build` fails with EMFILE, build the
  affected modules serially (one `lake build NeuralNetworkProofs.<Module>` per invocation, in
  dependency order) then rerun `lake build`.
- **Sorry-free gate:** `lake env lean scripts/check_sorry_free.lean` — every headline reports
  exactly `[propext, Classical.choice, Quot.sound]`; any `sorryAx` fails.

## Move map (verified from the import DAG)

- **Shared core, KEPT in `Monotone/`** (namespace `UniversalApproximation.Monotone`): `Defs.lean`
  (`heaviside`, `ActStack`, `MonoNet`), `Basic.lean`.
- **→ `MikulincerReichman/`**: `Indicator.lean` (`dominationStack`), `Grid.lean`,
  `Interpolation.lean` (`monotone_interpolation`), `Approximation.lean` (`monotone_approximation`).
- **→ `Sartor/`**: `Saturating.lean` (`RightSaturating`, `LeftSaturating`, `reflect`,
  `rightSaturating_scaled_approx`, `approx_interior_value`), `SaturatingInterp.lean`
  (`saturating_interpolation`), `Equivalence.lean` (`prop_3_10_two_layer`), `NonPositive.lean`
  (`nonpos_weight_universal`).

External consumers of moved modules (from a repo-wide grep): only
`NeuralNetworkProofs/UniversalApproximation/Monotone.lean` (re-export) and
`NeuralNetworkProofs/UniversalApproximation/Runje/Approximation.lean` (imports M-R `Approximation`).

---

### Task 1: Split out `UniversalApproximation.Sartor`

**Files:**
- Move: `Monotone/Saturating.lean`, `Monotone/SaturatingInterp.lean`, `Monotone/Equivalence.lean`,
  `Monotone/NonPositive.lean` → `Sartor/` (same basenames).
- Create: `NeuralNetworkProofs/UniversalApproximation/Sartor.lean`
- Modify: `NeuralNetworkProofs/UniversalApproximation/Monotone.lean` (drop 4 Sartor imports),
  `NeuralNetworkProofs.lean` (add Sartor import), `scripts/check_sorry_free.lean` (open Sartor).

**Interfaces:**
- Consumes: shared core `UniversalApproximation.Monotone` (`ActStack`, `MonoNet`, `heaviside`,
  `Layer`, `Basic` lemmas) — unchanged.
- Produces: `UniversalApproximation.Sartor.{saturating_interpolation, nonpos_weight_universal,
  RightSaturating, LeftSaturating, reflect, prop_3_10_two_layer, …}` and the re-export root
  `NeuralNetworkProofs.UniversalApproximation.Sartor`.

- [ ] **Step 1: Move the four Sartor files.**

```bash
cd /workspaces/neural-network-proofs
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Saturating.lean \
       NeuralNetworkProofs/UniversalApproximation/Sartor/Saturating.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/SaturatingInterp.lean \
       NeuralNetworkProofs/UniversalApproximation/Sartor/SaturatingInterp.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Equivalence.lean \
       NeuralNetworkProofs/UniversalApproximation/Sartor/Equivalence.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/NonPositive.lean \
       NeuralNetworkProofs/UniversalApproximation/Sartor/NonPositive.lean
```

- [ ] **Step 2: In each moved file, change the namespace and open the shared core.**

In all four moved files, change the line `namespace UniversalApproximation.Monotone` to
`namespace UniversalApproximation.Sartor`, and immediately after it add:

```lean
open UniversalApproximation.Monotone
```

(Their unqualified uses of `ActStack`/`MonoNet`/`heaviside`/`Layer`/`Basic` lemmas now resolve via
this `open`. Same-file-set references, e.g. `NonPositive` using `reflect`/`prop_3_10_two_layer`,
resolve because those decls are now also in `UniversalApproximation.Sartor`.)

- [ ] **Step 3: Re-point intra-Sartor imports in the moved files.**

Change these import lines (shared-core imports `Monotone.Defs`/`Monotone.Basic` stay as-is):
- `Sartor/SaturatingInterp.lean`: `…Monotone.Saturating` → `…Sartor.Saturating`.
- `Sartor/Equivalence.lean`: `…Monotone.Saturating` → `…Sartor.Saturating`.
- `Sartor/NonPositive.lean`: `…Monotone.Saturating` → `…Sartor.Saturating`;
  `…Monotone.Equivalence` → `…Sartor.Equivalence`; `…Monotone.SaturatingInterp` →
  `…Sartor.SaturatingInterp`.
- `Sartor/Saturating.lean`: no sibling imports to change.

(Concretely: `import NeuralNetworkProofs.UniversalApproximation.Monotone.Saturating` becomes
`import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating`, etc.)

- [ ] **Step 4: Create the Sartor re-export root.**

Create `NeuralNetworkProofs/UniversalApproximation/Sartor.lean`:

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Sartor.Saturating
import NeuralNetworkProofs.UniversalApproximation.Sartor.SaturatingInterp
import NeuralNetworkProofs.UniversalApproximation.Sartor.Equivalence
import NeuralNetworkProofs.UniversalApproximation.Sartor.NonPositive

/-!
# Universal Approximation for Monotone Networks — Sartor et al. (2025)

> D. Sartor et al., "Advancing Constrained Monotonic Neural Networks: Achieving Universal
> Approximation Beyond Bounded Activations", arXiv:2505.02537 (2025).

For monotone, one-sided-saturating, non-constant activations, depth-4 monotone networks are
universal, via alternating-saturation non-negative weights (Thm 3.5) or, equivalently,
non-positive weights and a single activation (Prop 3.11), tied by the weight-sign ↔ saturation-side
reflection (Props 3.8/3.10). Built on the shared `ActStack` core in
`UniversalApproximation.Monotone`.

* `UniversalApproximation.Sartor.saturating_interpolation` — Theorem 3.5.
* `UniversalApproximation.Sartor.nonpos_weight_universal` — Proposition 3.11.
-/
```

- [ ] **Step 5: Drop the Sartor imports from `Monotone.lean`.**

In `NeuralNetworkProofs/UniversalApproximation/Monotone.lean`, delete the four import lines for
`Monotone.Saturating`, `Monotone.Equivalence`, `Monotone.SaturatingInterp`, `Monotone.NonPositive`.
(Leave the docstring for now; Task 2 rewrites it when the M-R files also leave.)

- [ ] **Step 6: Add the Sartor import to the top root.**

In `NeuralNetworkProofs.lean`, after `import NeuralNetworkProofs.UniversalApproximation.Monotone`
(line 8) add:

```lean
import NeuralNetworkProofs.UniversalApproximation.Sartor
```

- [ ] **Step 7: Update the sorry-free gate opens.**

In `scripts/check_sorry_free.lean`, the Sartor headlines (`saturating_interpolation`,
`nonpos_weight_universal`) are no longer under `Monotone`. Change the second `open` line from
`open UniversalApproximation.Runje` to:

```lean
open UniversalApproximation.Sartor UniversalApproximation.Runje
```

(The first `open` line keeps `…Monotone` — the M-R headlines are still there until Task 2. Keep
both `#print axioms` lines for the Sartor headlines; they now resolve via the `Sartor` open.)

- [ ] **Step 8: Build and run the gate.**

```bash
lake build
lake env lean scripts/check_sorry_free.lean
```

Expected: `lake build` green (use the serial-build EMFILE fallback if needed). The gate prints all
nine headline axiom lines; `saturating_interpolation` and `nonpos_weight_universal` now report
`[propext, Classical.choice, Quot.sound]` under `UniversalApproximation.Sartor`; no `sorryAx`.

- [ ] **Step 9: Commit.**

```bash
git add -A
git commit -m "refactor(sartor): split Sartor development into UniversalApproximation.Sartor"
```

---

### Task 2: Split out `UniversalApproximation.MikulincerReichman`

**Files:**
- Move: `Monotone/Indicator.lean`, `Monotone/Grid.lean`, `Monotone/Interpolation.lean`,
  `Monotone/Approximation.lean` → `MikulincerReichman/`.
- Create: `NeuralNetworkProofs/UniversalApproximation/MikulincerReichman.lean`
- Modify: `Monotone.lean` (slim to shared core + rewrite docstring), `NeuralNetworkProofs.lean`
  (add M-R import), `Runje/Approximation.lean` (re-point M-R import + open),
  `scripts/check_sorry_free.lean` (open MikulincerReichman).

**Interfaces:**
- Consumes: shared core `UniversalApproximation.Monotone` (unchanged); `Sartor` (from Task 1).
- Produces: `UniversalApproximation.MikulincerReichman.{monotone_interpolation,
  monotone_approximation, dominationStack, …}` and the re-export root
  `NeuralNetworkProofs.UniversalApproximation.MikulincerReichman`.

- [ ] **Step 1: Move the four M-R files.**

```bash
cd /workspaces/neural-network-proofs
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Indicator.lean \
       NeuralNetworkProofs/UniversalApproximation/MikulincerReichman/Indicator.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Grid.lean \
       NeuralNetworkProofs/UniversalApproximation/MikulincerReichman/Grid.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Interpolation.lean \
       NeuralNetworkProofs/UniversalApproximation/MikulincerReichman/Interpolation.lean
git mv NeuralNetworkProofs/UniversalApproximation/Monotone/Approximation.lean \
       NeuralNetworkProofs/UniversalApproximation/MikulincerReichman/Approximation.lean
```

- [ ] **Step 2: Change namespace + open shared core in each moved file.**

In all four moved files, change `namespace UniversalApproximation.Monotone` →
`namespace UniversalApproximation.MikulincerReichman`, and immediately after add:

```lean
open UniversalApproximation.Monotone
```

- [ ] **Step 3: Re-point intra-M-R imports.**

(Shared-core imports `Monotone.Defs`/`Monotone.Basic` stay.)
- `MikulincerReichman/Interpolation.lean`: `…Monotone.Indicator` → `…MikulincerReichman.Indicator`.
- `MikulincerReichman/Approximation.lean`: `…Monotone.Interpolation` →
  `…MikulincerReichman.Interpolation`; `…Monotone.Grid` → `…MikulincerReichman.Grid`.
- `MikulincerReichman/Indicator.lean`, `…/Grid.lean`: only shared-core imports — no change.

- [ ] **Step 4: Create the M-R re-export root.**

Create `NeuralNetworkProofs/UniversalApproximation/MikulincerReichman.lean`:

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Indicator
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Grid
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Interpolation
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman.Approximation

/-!
# Universal Approximation for Monotone Networks — Mikulincer–Reichman (2022)

> D. Mikulincer and R. Reichman, "The Size of the Weights Matter", arXiv:2207.05275 (2022).

Every monotone continuous function on the unit cube `[0,1]^d` is uniformly `ε`-approximated by a
depth-4 monotone threshold network, with exact interpolation on finitely many points. Built on the
shared `ActStack` core in `UniversalApproximation.Monotone`.

* `UniversalApproximation.MikulincerReichman.monotone_interpolation` — Result 1, interpolation.
* `UniversalApproximation.MikulincerReichman.monotone_approximation` — Result 1, approximation.
-/
```

- [ ] **Step 5: Slim `Monotone.lean` to the shared core + rewrite its docstring.**

Replace the entire `NeuralNetworkProofs/UniversalApproximation/Monotone.lean` with:

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Monotone.Defs
import NeuralNetworkProofs.UniversalApproximation.Monotone.Basic

/-!
# Monotone neural networks — shared core

Shared infrastructure for the monotone-network universal-approximation developments
(`UniversalApproximation.MikulincerReichman` and `UniversalApproximation.Sartor`, and reused by
`UniversalApproximation.Runje`): the activation-generic `ActStack` model, the monotone network
`MonoNet`, the `heaviside` gate, and shared lemmas.

* `UniversalApproximation.Monotone.ActStack`, `…MonoNet`, `…heaviside`.
-/
```

- [ ] **Step 6: Add the M-R import to the top root.**

In `NeuralNetworkProofs.lean`, add after the `Monotone` import:

```lean
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman
```

(Keep the `Monotone` import — it is now the shared core. Order: `…Monotone`, `…MikulincerReichman`,
`…Sartor`, `…Runje`.)

- [ ] **Step 7: Re-point Runje's reference to `monotone_approximation`.**

In `NeuralNetworkProofs/UniversalApproximation/Runje/Approximation.lean`:
- Change the import (line 7) `…Monotone.Approximation` → `…MikulincerReichman.Approximation`.
- The `open` line (currently `open UniversalApproximation.Monotone UniversalApproximation.Leshno`)
  becomes:

```lean
open UniversalApproximation.Monotone UniversalApproximation.MikulincerReichman
  UniversalApproximation.Leshno
```

(Keep `…Monotone` — `MonoNet`/`IsMonotone` are shared-core. Add `…MikulincerReichman` so the
unqualified `monotone_approximation` at the `jointTarget` call resolves. If the three-namespace
`open` exceeds 100 codepoints on one line, split across two lines as shown.)

- [ ] **Step 8: Update the sorry-free gate opens.**

In `scripts/check_sorry_free.lean`, `monotone_interpolation`/`monotone_approximation` are now under
`MikulincerReichman`. Set the two `open` lines to:

```lean
open UniversalApproximation.Cybenko UniversalApproximation.Leshno
open UniversalApproximation.MikulincerReichman UniversalApproximation.Sartor
  UniversalApproximation.Runje
```

(Drop `…Monotone` from the opens — no headline lives there now. Split the second `open` across two
lines if it exceeds 100 codepoints. All nine `#print axioms` lines are unchanged.)

- [ ] **Step 9: Build and run the gate.**

```bash
lake build
lake env lean scripts/check_sorry_free.lean
```

Expected: green build; all nine headlines report `[propext, Classical.choice, Quot.sound]`
(`monotone_interpolation`/`monotone_approximation` now under `MikulincerReichman`, Runje headlines
still clean); no `sorryAx`.

- [ ] **Step 10: Commit.**

```bash
git add -A
git commit -m "refactor(mr): split Mikulincer–Reichman into UniversalApproximation.MikulincerReichman"
```

---

### Task 3: Results aggregator, top-root simplification, and docs

**Files:**
- Create: `NeuralNetworkProofs/UniversalApproximation.lean`
- Modify: `NeuralNetworkProofs.lean`, `README.md`, `CLAUDE.md`.

**Interfaces:**
- Consumes: all development roots (`Cybenko`, `Leshno`, `Monotone`, `MikulincerReichman`, `Sartor`,
  `Runje`).
- Produces: `NeuralNetworkProofs.UniversalApproximation` (aggregator module).

- [ ] **Step 1: Create the aggregator.**

Create `NeuralNetworkProofs/UniversalApproximation.lean`:

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.UniversalApproximation.Monotone
import NeuralNetworkProofs.UniversalApproximation.MikulincerReichman
import NeuralNetworkProofs.UniversalApproximation.Sartor
import NeuralNetworkProofs.UniversalApproximation.Runje

/-!
# Universal approximation theorems — results aggregator

Re-exports every UAT development so a single import brings in all results. Headlines:

* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Cybenko.universal_approximation_eps` — Cybenko (1989), ε form.
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).
* `UniversalApproximation.MikulincerReichman.monotone_interpolation` — M–R (2022), interpolation.
* `UniversalApproximation.MikulincerReichman.monotone_approximation` — M–R (2022), approximation.
* `UniversalApproximation.Sartor.saturating_interpolation` — Sartor et al. (2025), Thm 3.5.
* `UniversalApproximation.Sartor.nonpos_weight_universal` — Sartor et al. (2025), Prop 3.11.
* `UniversalApproximation.Runje.partial_monotone_approximation` — Runje et al. (2026), partial-
  monotone UAP.
* `UniversalApproximation.Runje.PartMonoNet.monotone_snd` — Runje et al. (2026), soundness.

The shared `ActStack` core lives in `UniversalApproximation.Monotone`.
-/
```

- [ ] **Step 2: Simplify the top root.**

Replace the import block (lines 6–10) of `NeuralNetworkProofs.lean` with:

```lean
import NeuralNetworkProofs.UniversalApproximation
import NeuralNetworkProofs.NeuralNetwork.Network
```

Update its module docstring so the headline list matches the aggregator's (repoint the M-R and
Sartor bullets to their new namespaces, add the two Runje bullets if absent) and note that
`NeuralNetworkProofs.UniversalApproximation` is the canonical results aggregator.

- [ ] **Step 3: Build and run the gate.**

```bash
lake build
lake env lean scripts/check_sorry_free.lean
```

Expected: green; all nine headlines clean; no `sorryAx`.

- [ ] **Step 4: Update `README.md`.**

Make the developments list five author-named entries — Cybenko, Leshno, Mikulincer–Reichman
(interpolation + approximation), Sartor (saturating results + reflection props), Runje (partial-
monotone) — matching the existing voice. Where the layout is described, note that the shared
`ActStack` core lives under `UniversalApproximation.Monotone` (infrastructure, no headline), and
that `NeuralNetworkProofs.UniversalApproximation` aggregates all results. Repoint any theorem name
to its new namespace. (Read `README.md` first and edit in place; do not churn unrelated lines.)

- [ ] **Step 5: Update `CLAUDE.md`.**

- "What this is": change "Four developments" → "Five developments" and split the Monotone bullet
  into a Mikulincer–Reichman bullet (`…MikulincerReichman.monotone_interpolation`,
  `…monotone_approximation`) and a Sartor bullet (`…Sartor.saturating_interpolation`,
  `…nonpos_weight_universal`, reflection props). Keep the Cybenko/Leshno/Runje bullets, repointing
  none except the two split ones.
- Layout table: replace the single `Monotone/` row with three rows — shared
  `NeuralNetworkProofs/UniversalApproximation/Monotone/` + `Monotone.lean` |
  `UniversalApproximation.Monotone` | shared `ActStack` core; `…/MikulincerReichman/` +
  `MikulincerReichman.lean` | `UniversalApproximation.MikulincerReichman` | Mikulincer–Reichman
  development; `…/Sartor/` + `Sartor.lean` | `UniversalApproximation.Sartor` | Sartor et al.
  development. Add a row for `UniversalApproximation.lean` |
  `NeuralNetworkProofs.UniversalApproximation` | results aggregator (re-exports all UAT roots).
- Update the root-re-export note (the `NeuralNetworkProofs.lean` row / the "re-exports the … UAT
  roots" prose) to say the top root now imports the `UniversalApproximation` aggregator.

(Read `CLAUDE.md` first; edit in place.)

- [ ] **Step 6: Commit.**

```bash
git add -A
git commit -m "refactor(uat): add UniversalApproximation aggregator; simplify root; update docs"
```

---

### Task 4: Split the blueprint chapter and repoint declaration refs

**Files:**
- Create: `blueprint/src/chapter/mikulincer-reichman.tex`, `blueprint/src/chapter/sartor.tex`
- Delete: `blueprint/src/chapter/monotone.tex`
- Modify: `blueprint/src/content.tex`.

**Interfaces:**
- Consumes: the renamed Lean declarations (Tasks 1–2).
- Produces: two author-named blueprint chapters whose `\lean{}` refs resolve under `checkdecls`.

- [ ] **Step 1: Split `monotone.tex` into two chapters.**

Split the content of `blueprint/src/chapter/monotone.tex` at the boundary between M-R material
(heaviside/actstack/mononet/domination + `thm:mono-interp`/`thm:mono-approx`) and Sartor material
(`def:saturating` onward):
- `mikulincer-reichman.tex` — a `\chapter{Monotone networks — Mikulincer–Reichman}` holding the
  shared model definitions (`def:heaviside`, `def:actstack`, `def:mononet`, `def:domination`) and
  the two M-R theorems (`thm:mono-interp`, `thm:mono-approx`) with their surrounding prose/proofs.
- `sartor.tex` — a `\chapter{Monotone networks — Sartor et al.}` holding the Sartor definitions,
  lemmas, propositions, and theorems (`def:saturating`, `def:reflect`, `lem:sat-scaled`,
  `lem:approx-interior`, `prop:sign-sat`, `thm:sat-interp`, `prop:nonpos`). Its `\uses{def:mononet,
  def:heaviside, …}` cross-references resolve against labels defined in the M-R chapter (which is
  `\input` first — Step 3).

Preserve every `\label`, `\uses`, `\leanok`, and prose block; only the chapter split and the
`\lean{}` namespaces (Step 2) change.

- [ ] **Step 2: Repoint every `\lean{}` reference to its new namespace.**

Apply this exact mapping (shared-core refs are UNCHANGED):

| Blueprint ref | New `\lean{}` value |
|---|---|
| `heaviside` | `UniversalApproximation.Monotone.heaviside` (unchanged) |
| `ActStack` | `UniversalApproximation.Monotone.ActStack` (unchanged) |
| `MonoNet` | `UniversalApproximation.Monotone.MonoNet` (unchanged) |
| `dominationStack` | `UniversalApproximation.MikulincerReichman.dominationStack` |
| `monotone_interpolation` | `UniversalApproximation.MikulincerReichman.monotone_interpolation` |
| `monotone_approximation` | `UniversalApproximation.MikulincerReichman.monotone_approximation` |
| `RightSaturating` | `UniversalApproximation.Sartor.RightSaturating` |
| `LeftSaturating` | `UniversalApproximation.Sartor.LeftSaturating` |
| `reflect` | `UniversalApproximation.Sartor.reflect` |
| `rightSaturating_scaled_approx` | `UniversalApproximation.Sartor.rightSaturating_scaled_approx` |
| `approx_interior_value` | `UniversalApproximation.Sartor.approx_interior_value` |
| `prop_3_10_two_layer` | `UniversalApproximation.Sartor.prop_3_10_two_layer` |
| `saturating_interpolation` | `UniversalApproximation.Sartor.saturating_interpolation` |
| `nonpos_weight_universal` | `UniversalApproximation.Sartor.nonpos_weight_universal` |

- [ ] **Step 3: Update `content.tex`.**

In `blueprint/src/content.tex`, replace the line `\input{chapter/monotone}` with, in this order:

```tex
\input{chapter/mikulincer-reichman}
\input{chapter/sartor}
```

- [ ] **Step 4: Verify (blueprint build + checkdecls, with fallback).**

Primary (matches CI `.github/workflows/pages.yml`): install the blueprint toolchain and build, then
run the faithfulness gate.

```bash
bash scripts/setup-dev.sh --no-build --no-cache
export PATH="$HOME/.local/bin:$PATH"
leanblueprint web
lake exe checkdecls blueprint/lean_decls
```

Expected: `leanblueprint web` succeeds; `checkdecls` reports all declarations found (no "not found"
lines) — every `\lean{}` ref resolves to a real declaration under its new namespace.

**Fallback if `leanblueprint` cannot be installed in this environment:** verify each renamed
declaration name resolves, by running a scratch check (this is exactly what `checkdecls` does):

```bash
lake env lean --run /dev/stdin <<'EOF'
import NeuralNetworkProofs
open UniversalApproximation
#check @MikulincerReichman.monotone_interpolation
#check @MikulincerReichman.monotone_approximation
#check @MikulincerReichman.dominationStack
#check @Sartor.saturating_interpolation
#check @Sartor.nonpos_weight_universal
#check @Sartor.RightSaturating
#check @Sartor.LeftSaturating
#check @Sartor.reflect
#check @Sartor.rightSaturating_scaled_approx
#check @Sartor.approx_interior_value
#check @Sartor.prop_3_10_two_layer
#check @Monotone.heaviside
#check @Monotone.ActStack
#check @Monotone.MonoNet
EOF
```

Expected: every `#check` succeeds (no "unknown identifier"). Also `grep -rn
"UniversalApproximation.Monotone.\(dominationStack\|monotone_interpolation\|monotone_approximation\|RightSaturating\|LeftSaturating\|reflect\|rightSaturating_scaled_approx\|approx_interior_value\|prop_3_10_two_layer\|saturating_interpolation\|nonpos_weight_universal\)" blueprint/` returns nothing (no stale refs). If using the fallback, note in the report that the full `leanblueprint web`/`checkdecls` run is deferred to CI.

- [ ] **Step 5: Commit.**

```bash
git add -A
git commit -m "docs(blueprint): split monotone chapter into Mikulincer–Reichman + Sartor"
```

---

## Self-Review

**Spec coverage:**
- §2 target layout (shared core kept; M-R + Sartor split) → Tasks 1–2. ✓
- §3 reference mechanics (git mv, namespace change, `open Monotone`, re-export roots) → Tasks 1–2
  Steps. ✓
- §3 aggregator + §4 top root → Task 3 Steps 1–2. ✓
- §4 downstream: Runje fix → Task 2 Step 7; sorry-free gate → Tasks 1 Step 7, 2 Step 8; README →
  Task 3 Step 4; CLAUDE.md → Task 3 Step 5. ✓
- §5 blueprint split + ref repoint + content.tex + checkdecls → Task 4. ✓
- §6 verification (build, sorry-free identical axioms, checkdecls, grep sweep) → Tasks' gates +
  Task 4 Step 4 grep. ✓
- §7 non-goals (no Runje blueprint chapter; no proof changes; historical specs untouched) →
  respected (no task adds a Runje chapter or edits proofs). ✓

**Placeholder scan:** No `TBD`/`TODO`. Every edit is given with exact file, exact old→new strings,
and full re-export/aggregator file contents. Verification commands are concrete.

**Type/name consistency:** Namespaces (`UniversalApproximation.Monotone` shared,
`.MikulincerReichman`, `.Sartor`) and module paths are used identically across Tasks 1–4; the
blueprint mapping (Task 4 Step 2) matches the file→namespace assignment in the Move map and Tasks
1–2; `NeuralNetworkProofs.lean` import evolution is consistent (Sartor added T1, M-R added T2,
collapsed to the aggregator T3); the sorry-free `open` evolution is consistent across T1 Step 7 and
T2 Step 8.

**Ordering:** Each Lean task (1–3) ends green on `lake build` + the sorry-free gate. The blueprint
`checkdecls` gate is only exercised in Task 4 (it is a separate `lake exe`, not part of `lake
build`), so intermediate commits do not need it green.
