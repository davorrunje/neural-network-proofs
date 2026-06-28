# ForMathlib upstream-conformance (two phases: mechanical + proof decomposition)

**Date:** 2026-06-28
**Status:** Approved (design); proceeding to plan.
**Branch:** `refactor/formathlib-conformance` (Phase 1) from `main`; Phase 2 a separate branch/PR after.

## Goal

Bring all nine `NeuralNetworkProofs/ForMathlib/` files in line with Mathlib community standards, as a
**behavior-preserving** refactor (no statement or proof-*result* changes; public statements and
axioms unchanged). Two phases, delivered as **two PRs**:

- **Phase 1 (mechanical):** minimal specific imports, a copyright header + repo `LICENSE`, and
  `mathlibStandardSet` lint-cleanliness.
- **Phase 2 (proof decomposition):** split the long monolithic proofs into small, named, documented
  auxiliary lemmas; drop the `maxHeartbeats` override; extract shared proof skeletons. Aggressive
  scope — every proof longer than ~20 lines.

## Background / motivation

`ForMathlib/` holds nine files (~2092 lines) intended for eventual Mathlib upstreaming, but they
currently violate Mathlib conventions on two axes:

- **Mechanical:** every file does **`import Mathlib`** (Mathlib never imports the whole library; each
  file must import only the specific `Mathlib.…` modules it uses); there is **no `LICENSE` file** and
  **no copyright headers**; module docstrings carry a non-standard `Intended Mathlib home:` note.
- **Proof structure:** several proofs are far longer than Mathlib norms (one is ~458 lines and needs
  `set_option maxHeartbeats 1600000`); Mathlib favors many small, named, reusable lemmas.

**Side benefit of Phase 1:** replacing `import Mathlib` (which loads *all* of Mathlib per file) with
minimal imports sharply reduces per-file olean loading — expected to eliminate the concurrent-rebuild
`Too many open files` (EMFILE) problem seen in prior refactors and to speed builds.

---

## Phase 1 — mechanical conformance (PR 1)

### Scope
1. Add an **Apache License 2.0** `LICENSE` file at the repo root.
2. For each `ForMathlib/*.lean`: minimal imports; copyright header; module-doc normalization (keeping
   the `Intended Mathlib home:` note); `mathlibStandardSet` lint-cleanliness.

Intra-`ForMathlib` imports (e.g. `import NeuralNetworkProofs.ForMathlib.ConvolutionPolynomial`) are
**unchanged**; only the `import Mathlib` line is replaced.

### Approach (per file, dependency order — leaves first)
1. **Minimal imports.** Use `Mathlib.Tactic.MinImports` (`#min_imports` / the `minImports` linter) or
   `lake exe shake` to find the specific `Mathlib.…` modules the file uses; replace `import Mathlib`
   with that list (sorted), keeping intra-`ForMathlib` imports; iterate against the build.
2. **Copyright header** as the first lines, Mathlib layout:
   ```
   /-
   Copyright (c) 2026 Davor Runje. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Davor Runje
   -/
   ```
   (Mathlib convention: name only, no email.)
3. **Module docstring** normalized to `/-! # Title … -/` after the imports; keep the
   `Intended Mathlib home:` note.
4. **Lint-clean:** resolve every `mathlibStandardSet` warning (header, line length ≤100 codepoints,
   naming, …).

### Enable the `minImports` linter (mandatory)
Enable the `minImports` linter on every `ForMathlib` file (`set_option linter.minImports true` at the
top of each file) so imports cannot regress to over-broad sets, and the files must be **clean** of its
warnings. Enforce it: extend the CI to **fail if `lake build` emits any linter warning** for the
`ForMathlib` files (the sorry-free job already shells out; add a warning check). Scope is `ForMathlib`
only for now — the other modules (`Cybenko`, `Leshno`, `NeuralNetwork`) still do `import Mathlib`, so a
repo-wide `linter.minImports` would flag them; minimizing those is a separate future step.

### Done-criteria
- No `import Mathlib` remains; intra-`ForMathlib` imports intact; `LICENSE` present; every file has
  the header.
- `linter.minImports` is enabled on every `ForMathlib` file and they are warning-clean; CI fails on
  any `ForMathlib` linter warning.
- `lake build` green, no `mathlibStandardSet` warnings on `ForMathlib`.
- `git diff` touches only imports/headers/docstrings/`set_option` — no declaration signature or proof
  body changed.

---

## Phase 2 — proof decomposition (PR 2, after Phase 1 merges)

### Principle
Replace long monolithic proofs with small, **named, `private` auxiliary lemmas** (docstrings on any
that read as reusable API), so each remaining proof is short and the structure is legible — the
canonical Mathlib style. Public statements, signatures, and axioms are **unchanged**; only proof
bodies are refactored into supporting lemmas.

### Scope — every proof > ~20 lines (22 total)

Guideline, not a blind line cap: decompose where extracting a named sub-lemma improves clarity. A
proof that is a single irreducible computation (one `ring`/`simp`/`fun_prop`/`field_simp` block) may
remain if no meaningful sub-lemma exists. The hard requirements are: **drop `maxHeartbeats`** and
decompose the three giants.

| File | Proof (lines) |
|------|----------------|
| `UniformRiemannConvolution` | `tendstoUniformly_riemannSum_aeContinuous` (~458, **+maxHeartbeats**), `tendstoUniformly_riemannSum_continuous` (~137), `exists_cthickening_measure_lt` (35) |
| `RidgePowersSpan` | `ridgePoly_span` (100), `coeff_ridgePoly_one` (25), `coeff_scaleHom` (23) |
| `RieszKantorovich` | `Lpos` (40), `rkSup_smul` (35), `instSemilatticeSup` (29), `rkSup_add` (23) |
| `PolynomialDistribution` | `aePolynomial_of_annihilates_moment_vanishing` (89), `exists_factor` (33) |
| `ConvolutionDegreeBound` | `conv_left_comm_mul` (70), `exists_uniform_degree_bound` (54) |
| `ConvolutionPolynomial` | `monomial_conv_isPoly` (53), `poly_conv_isPoly` (49) |
| `IteratedDerivPolynomial` | `iteratedDeriv_eq_zero_imp_poly` (66), `exists_antideriv` (31) |
| `SmoothCompactAntideriv` | `exists_iteratedDeriv_eq_of_moments_zero` (36), `moment_antideriv` (34), `hasCompactSupport_antideriv` (27) |
| `ConvolutionIteratedDeriv` | `iteratedDeriv_convolution_left` (27) |

### Specific must-do items
- **`tendstoUniformly_riemannSum_aeContinuous`:** decompose the good/bad-cell argument into named
  lemmas (φ-variation bound; good-cell oscillation bound via uniform continuity; bad-cell measure
  bound via `cthickening`; per-cell split; assembly) and **remove `set_option maxHeartbeats 1600000`**
  (decomposition should bring each piece within the default budget).
- **Shared cell skeleton:** `tendstoUniformly_riemannSum_continuous` and the a.e.-continuous proof
  duplicate the equispaced cell-decomposition setup (node defs, `g_eq`/`hg_sum`/`hr_sum`, the
  `Nat.ceil` mesh argument). Extract the `f`-agnostic parts into shared `private` lemmas used by both,
  removing the duplication a prior review flagged.

### Approach (per file)
Work file-by-file (a natural task unit). For each long proof: identify the logically separable
sub-steps, lift each into a `private` lemma with a clear name (Mathlib naming) and the minimal
hypotheses, then rewrite the original proof as a short assembly of those lemmas. Build and re-check
axioms after each file.

### Parallel execution (concurrent agents)
Because Phase 2 is behavior-preserving and changes only proof bodies / adds `private` lemmas, a file's
*public API is unchanged*, so files are independent for decomposition — they can be worked
**concurrently**. Mechanism: **git-worktree isolation** — one agent per file, each in its own worktree
on its own branch (so they don't race the shared working tree / git index); the controller builds,
verifies axioms, and merges the per-file branches. Concurrency is bounded by build resources (each
worktree has its own `.lake` and needs Mathlib oleans), so run a **modest batch (≈2–4 at a time)**,
not all nine. This is viable specifically *because Phase 1 minimized imports*: each file then loads
only its few `Mathlib.…` modules, so concurrent builds are light and avoid the `import Mathlib`
EMFILE thrashing. (The two `UniformRiemannConvolution` proofs share extracted skeleton lemmas, so that
file is one unit, decomposed by a single agent.)

### Done-criteria
- No `set_option maxHeartbeats` remains in `ForMathlib`.
- No proof in `ForMathlib` materially exceeds ~20 lines except irreducible single-tactic computations
  (documented if kept).
- The shared cell skeleton is factored out (no duplication between the two Riemann proofs).
- `lake build` green; public statements/signatures **unchanged**; `#print axioms` unchanged on the
  decomposed declarations *and* on the downstream consumers
  (`UniversalApproximation.Leshno.leshno_dense_iff`, `UniversalApproximation.Cybenko.universal_approximation`)
  → `[propext, Classical.choice, Quot.sound]`.

---

## Cross-cutting verification (both phases)

Behavior preservation is the invariant. After each phase:
- `lake build` green.
- `#print axioms` on the downstream headline consumers unchanged
  (`leshno_dense_iff`, `universal_approximation`) — proves nothing broke through the `ForMathlib`
  dependency chain.
- The set of **public** declaration names and their statements is unchanged (Phase 2 adds `private`
  lemmas and may add `private` helpers; it does not alter or remove public API).

## Delivery / sequencing

- **PR 1 (Phase 1):** branch `refactor/formathlib-conformance` off `main`. Mechanical, low-risk.
- **PR 2 (Phase 2):** a new branch off `main` after PR 1 merges. Judgment-heavy; cleaner
  imports/headers from Phase 1 keep its diff readable.

## Global constraints

- Behavior-preserving: no public statement, signature, or proof-*result* changes. Phase 1 = imports/
  headers/docstrings/`LICENSE` only; Phase 2 = proof-body refactor into `private` lemmas only.
- Minimal Mathlib imports; no new non-Mathlib dependency.
- Line length ≤ 100 codepoints.
- Commits SSH-signed.
- Build green + axioms unchanged, verified per file; serial builds available if EMFILE recurs
  mid-refactor (should diminish once Phase 1 minimizes imports).
