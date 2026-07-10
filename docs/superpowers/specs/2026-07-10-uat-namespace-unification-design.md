# UAT namespace unification (design)

**Date:** 2026-07-10
**Status:** design approved, pending spec review → implementation plan

## 1. Goal

Make every UAT development author-named, consistent with `Cybenko`, `Leshno`, and the new
`Runje`. Today `UniversalApproximation.Monotone` is topic-named and holds **two** developments
(Mikulincer–Reichman and Sartor et al.) sharing one `ActStack` core. Split the paper-specific
results into author-named namespaces, keep the shared core under the (kept) `Monotone` name, and
propagate the rename across every place that references the moved declarations: Lean, the
leanblueprint + `checkdecls` gate, the sorry-free gate, `NeuralNetworkProofs.lean`, README, and
CLAUDE.md.

This is a **rename/move refactor of existing sorry-free code** — no proof or statement content
changes. It is the deferred follow-up from the Runje spec (§8) and the
`namespace-unification-followup` memory.

## 2. Target Lean layout

The internal import DAG has no Mikulincer–Reichman ↔ Sartor edges (only shared-core → both), so
the split is clean.

| Folder / namespace | Files | Notable decls |
|---|---|---|
| `Monotone/` = `UniversalApproximation.Monotone` (shared core, **kept**) | `Defs`, `Basic` | `heaviside`, `ActStack`, `MonoNet`, `dominationStack`, shared lemmas (`sort_key_linear_extension`, …) |
| `MikulincerReichman/` = `UniversalApproximation.MikulincerReichman` (**new**) | `Indicator`, `Grid`, `Interpolation`, `Approximation` | `monotone_interpolation`, `monotone_approximation` |
| `Sartor/` = `UniversalApproximation.Sartor` (**new**) | `Saturating`, `SaturatingInterp`, `Equivalence`, `NonPositive` | `saturating_interpolation`, `nonpos_weight_universal`, `RightSaturating`, `LeftSaturating`, `reflect`, `prop_3_10_two_layer` |
| `Runje/` = `UniversalApproximation.Runje` (**unchanged content**) | as merged | `partial_monotone_approximation`, `PartMonoNet.monotone_snd` |

Theorem/def **base names are unchanged**; only the namespace prefix changes. Concretely the four
Monotone headlines become:

- `UniversalApproximation.MikulincerReichman.monotone_interpolation`
- `UniversalApproximation.MikulincerReichman.monotone_approximation`
- `UniversalApproximation.Sartor.saturating_interpolation`
- `UniversalApproximation.Sartor.nonpos_weight_universal`

### Classification basis (from the import DAG)

- `Defs` imports nothing (Monotone-internal); everyone imports it → **shared**.
- `Basic` imports nothing; imported by `Indicator` (M-R) and `SaturatingInterp` (Sartor) → **shared**.
- `Indicator`←`Defs,Basic`; `Grid`←`Defs`; `Interpolation`←`Defs,Indicator,Basic`;
  `Approximation`←`Defs,Interpolation,Grid`. Used only by M-R → **Mikulincer–Reichman**.
- `Saturating`←nothing; `SaturatingInterp`←`Defs,Basic,Saturating`; `Equivalence`←`Defs,Saturating`;
  `NonPositive`←`Defs,Saturating,Equivalence,SaturatingInterp`. Used only by Sartor → **Sartor**.

## 3. Reference & import mechanics

For each moved file:

1. `git mv` into the new folder (`MikulincerReichman/` or `Sartor/`).
2. Change its module doc + `namespace UniversalApproximation.Monotone` → the new namespace.
3. Add `open UniversalApproximation.Monotone` so unqualified uses of shared-core decls
   (`ActStack`, `MonoNet`, `heaviside`, `Layer`, etc.) still resolve.
4. Re-point intra-paper imports to the new module paths (e.g. `MikulincerReichman.Approximation`
   imports `MikulincerReichman.Interpolation` and `MikulincerReichman.Grid`); shared-core imports
   stay `Monotone.Defs` / `Monotone.Basic`.

### Re-export roots

- `Monotone.lean` slims to re-export only `Monotone.Defs` + `Monotone.Basic` (shared core), with an
  updated docstring describing it as the shared monotone-network infrastructure.
- New `MikulincerReichman.lean` re-exports the four M-R modules (docstring credits Mikulincer–Reichman
  2022, lists the two headlines).
- New `Sartor.lean` re-exports the four Sartor modules (docstring credits Sartor et al. 2025, lists
  the two headlines + the reflection props).

### Results aggregator (new)

Add `NeuralNetworkProofs/UniversalApproximation.lean` (module
`NeuralNetworkProofs.UniversalApproximation`) that re-exports **all** development roots — `Cybenko`,
`Leshno`, `Monotone` (shared core), `MikulincerReichman`, `Sartor`, `Runje` — with a docstring that
summarizes every headline theorem in one canonical place:

- `…Cybenko.universal_approximation`, `…Cybenko.universal_approximation_eps`
- `…Leshno.leshno_dense_iff`
- `…MikulincerReichman.monotone_interpolation`, `…MikulincerReichman.monotone_approximation`
- `…Sartor.saturating_interpolation`, `…Sartor.nonpos_weight_universal`
- `…Runje.partial_monotone_approximation`, `…Runje.PartMonoNet.monotone_snd`

This mirrors the per-development root pattern one level up and gives a single import for all UAT
results. `NeuralNetworkProofs.UniversalApproximation` = the UAT results; `NeuralNetworkProofs` (top
root) = everything, including `NeuralNetwork` infrastructure and `ForMathlib`.

## 4. Downstream consistency

- **`Runje/`** — `Runje/Defs.lean` imports `Monotone.Defs` (MonoNet: still valid, shared core kept —
  no change). `Runje/Approximation.lean` imports `Monotone.Approximation` and references
  `monotone_approximation`: repoint the import to `MikulincerReichman.Approximation`, update its
  `open`/reference to `MikulincerReichman.monotone_approximation`. Rebuild + re-run the Runje
  headlines through the sorry-free gate to confirm axioms unchanged.
- **`NeuralNetworkProofs.lean`** (top root) — simplify to `import
  NeuralNetworkProofs.UniversalApproximation` (the new aggregator, §3) + `import
  NeuralNetworkProofs.NeuralNetwork.Network`, dropping the individual Cybenko/Leshno/Monotone
  imports (now transitive via the aggregator). Update its docstring: reference the aggregator as the
  canonical headline summary and repoint the M-R/Sartor headline bullets to their new namespaces.
  All headlines remain reachable by the default `lake build`.
- **`scripts/check_sorry_free.lean`** — update the `open` line (replace
  `UniversalApproximation.Monotone` with `UniversalApproximation.MikulincerReichman
  UniversalApproximation.Sartor`, splitting the `open` across lines to stay ≤100 codepoints as the
  Runje work did) so the four `#print axioms` names still resolve. The Runje headline lines are
  unaffected.
- **`README.md`** — the developments list becomes **five** author-named entries: Cybenko, Leshno,
  Mikulincer–Reichman, Sartor, Runje. The single Monotone bullet splits into a Mikulincer–Reichman
  entry (interpolation + approximation) and a Sartor entry (saturating results + reflection props),
  matching the surrounding voice. The shared `Monotone` core is infrastructure (no headline), noted
  where the layout is described rather than as a development bullet.
- **`CLAUDE.md`** — "What this is": change "Four developments" → **"Five developments"** and split
  the Monotone bullet into a Mikulincer–Reichman bullet and a Sartor bullet (headlines repointed to
  the new namespaces). Layout table: the one `Monotone/` row becomes three rows — shared
  `Monotone/` (= `UniversalApproximation.Monotone`, shared `ActStack` core), `MikulincerReichman/`,
  and `Sartor/`. Add a row for the new aggregator `UniversalApproximation.lean`
  (= `NeuralNetworkProofs.UniversalApproximation`, re-exports all UAT development roots + summarizes
  the headlines). Update the "re-exports the … UAT roots" note to reflect that the top root now goes
  through the `UniversalApproximation` aggregator.

## 5. Blueprint split

- Split `blueprint/src/chapter/monotone.tex` into `blueprint/src/chapter/mikulincer-reichman.tex`
  and `blueprint/src/chapter/sartor.tex`.
- The shared model definitions (`def:heaviside`, `def:actstack`, `def:mononet`, `def:domination`,
  refs `\lean{UniversalApproximation.Monotone.*}`) open the **Mikulincer–Reichman** chapter (it is
  the development that establishes the model); the Sartor chapter cross-references them via existing
  `\uses{def:mononet, def:heaviside, …}` (leanblueprint `\uses` works across chapters).
- Repoint every `\lean{}` ref to its new namespace: shared defs → `…Monotone.*`; M-R theorems
  (`monotone_interpolation`, `monotone_approximation`) → `…MikulincerReichman.*`; Sartor
  defs/lemmas/theorems (`RightSaturating`, `LeftSaturating`, `reflect`,
  `rightSaturating_scaled_approx`, `approx_interior_value`, `prop_3_10_two_layer`,
  `saturating_interpolation`, `nonpos_weight_universal`) → `…Sartor.*`.
- Update `blueprint/src/content.tex`: replace `\input{chapter/monotone}` with
  `\input{chapter/mikulincer-reichman}` and `\input{chapter/sartor}`.
- `blueprint/lean_decls` is generated from the `\lean{}` macros at build time, so `checkdecls`
  follows automatically once the refs are correct — no hand-editing of `lean_decls`.

## 6. Verification (acceptance gate)

In order:

1. `lake build` — fully green (all headlines reachable via `NeuralNetworkProofs.lean`).
2. `lake env lean scripts/check_sorry_free.lean` — every headline (Cybenko, Leshno, the four
   renamed Monotone headlines under their new namespaces, both Runje headlines) reports exactly
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx` anywhere. Since this is a pure
   rename/move, the axiom profiles must be **identical** to before.
3. Blueprint builds and `lake exe checkdecls blueprint/lean_decls` passes — every `\lean{}` ref
   resolves to a real declaration under its new namespace.
4. `grep` sweep: no stray `UniversalApproximation.Monotone.<movedDecl>` references remain in Lean,
   `.tex`, `.md`, or CI config (allowing legitimate historical mentions in `docs/superpowers/`
   plans/specs, which describe past work and are not updated).

## 7. Scope / non-goals

- **In scope:** the rename/move and all reference updates in §3–§5; the shared core keeps the
  `Monotone` name.
- **Non-goals (recorded follow-ups):**
  - Adding a Runje chapter to the blueprint (the blueprint currently omits Runje entirely; separate
    doc task).
  - Any change to proof/statement content, or to Cybenko/Leshno/Runje internals.
  - Historical `docs/superpowers/` plans/specs are left as-is (they document past work).

## 8. Risks

- **Broad but mechanical.** The risk is missing a reference site, caught by the §6 gate (build +
  checkdecls + grep sweep). Low proof risk (no proof changes).
- **`open` shadowing.** Adding `open UniversalApproximation.Monotone` in moved files could in
  principle clash with a local name; caught immediately by the build. Expected clean given the
  files already lived in that namespace.
- **Blueprint cross-chapter `\uses`.** The Sartor chapter references M-R/shared labels; confirm the
  labels are defined (in the M-R chapter) before use in the generated dependency graph — a
  leanblueprint build check.

## 9. Conventions

Follow CLAUDE.md: line length ≤ 100 codepoints, no `sorry`/`admit`, minimal precise imports
(unchanged by this refactor), sorry-free gate. Per the CLAUDE.md build gotcha, a rename that
invalidates all local oleans forces a from-scratch rebuild that can hit EMFILE; build the affected
modules serially in dependency order if needed.
