# Repository reorganization, rename, CI, and CLAUDE.md

**Date:** 2026-06-27
**Status:** Approved (design); proceeding to plan.

## Goal

Restructure the repository so each formalized proof, the general neural-network infrastructure, and
the Mathlib-upstream candidates each live in a clearly-named folder; rename the project from
`LeanPlayground` to `NeuralNetworkProofs` (it outgrew its "playground" origin); add CI that builds
everything and fails on a reintroduced `sorry`; and add a `CLAUDE.md`. The reorganization reserves a
clean home for the next work item — universal approximation theorems for **monotonic** neural
networks — without building it here.

## Scope

**In scope (this spec → one plan):**
1. Rename `LeanPlayground` → `NeuralNetworkProofs` (package, lib, module-path prefix, root dir/file,
   `defaultTargets`, all imports, GitHub repo).
2. Restructure into `ForMathlib/`, `NeuralNetwork/`, and `UniversalApproximation/{Cybenko,Leshno}/`.
3. Align namespaces with the new folders.
4. Re-export both UAT roots from the package root so the default `lake build` verifies both headlines.
5. CI (GitHub Actions): Mathlib cache + full build + a sorry-free axiom gate.
6. `CLAUDE.md`.

**Out of scope (future, separate specs/plans):**
- The monotonic-NN UAT proofs themselves (papers: *Size and depth of monotone neural networks*,
  Mikulincer–Reichman; *Advancing Constrained Monotonic Neural Networks*, Sartor–Sinigaglia–Susto).
  The layout reserves `UniversalApproximation/Monotone/` (namespace `UniversalApproximation.Monotone`)
  for them; they will reuse `NeuralNetwork/` (a monotone-constrained `Layer`). Not created now (empty
  directories are not tracked by git).
- Decoupling `ForMathlib/TestFunctionDegreeBound.lean` from its Leshno dependency (see Known wrinkles).
- Renaming the local workspace directory `/workspaces/lean-playground` and the devcontainer mount
  (environment-level; a manual follow-up for the maintainer).

## Sequencing

This refactor rewrites nearly every file's `import` lines and moves most files. It must be its **own
branch and PR, landing after PR #9 merges** (or rebased on it); mixing it with #9 would make #9
unreviewable and create large conflicts. The spec and plan can be written now regardless.

## Current state (baseline)

```
LeanPlayground/
  Basic.lean, Intro.lean              ← already deleted on the feat/leshno-sorry-free branch (#9)
  Contrib/                            ← 9 files, each with an "Intended Mathlib home:" header
    ConvolutionIteratedDeriv, ConvolutionPolynomial, IteratedDerivPolynomial,
    PolynomialDistribution, RidgePowersSpan, RieszKantorovich, SmoothCompactAntideriv,
    TestFunctionDegreeBound, UniformRiemannConvolution
  UniversalApproximation/
    Activation, Discriminatory, Family, Network, Riesz, Theorem   ← Cybenko (loose)
    Leshno/ , Leshno.lean                                         ← Leshno (foldered)
  UniversalApproximation.lean                                     ← Cybenko root re-export
LeanPlayground.lean                   ← package root (re-exports both, post-#9)
lakefile.toml                         ← name = "lean_playground", lib "LeanPlayground"
```

Key facts established during design:
- Leshno and Cybenko are independent (no cross-references).
- `Layer`/`Network` (in `Network.lean`) are referenced only by Cybenko's `Family.lean`.
- `ForMathlib/TestFunctionDegreeBound.lean` imports `…Leshno.MollifyDef` (a dev dependency).
- Cybenko's `Riesz.lean` uses `Contrib.RieszKantorovich`; Leshno uses 8 of the 9 Contrib files.

## Target layout

```
NeuralNetworkProofs/
  ForMathlib/                  (was Contrib/) — Mathlib-upstream candidates
    <9 files, unchanged contents except import-path updates>
  NeuralNetwork/               general neural-network infrastructure
    Network.lean               (moved from UniversalApproximation/Network.lean)
  UniversalApproximation/
    Cybenko/
      Activation.lean  Discriminatory.lean  Family.lean  Riesz.lean  Theorem.lean
    Cybenko.lean               (was UniversalApproximation.lean — Cybenko root re-export)
    Leshno/                    (unchanged)
    Leshno.lean                (unchanged)
NeuralNetworkProofs.lean       (was LeanPlayground.lean) — re-exports both UAT roots
lakefile.toml
.github/workflows/ci.yml
CLAUDE.md
```

`UniversalApproximation/Monotone/` is the reserved (uncreated) home for future monotone UATs.

## Namespace map

| File(s) | Namespace before | Namespace after |
|---|---|---|
| `NeuralNetwork/Network.lean` | `UniversalApproximation` | `NeuralNetwork` |
| `UniversalApproximation/Cybenko/*` + `Cybenko.lean` | `UniversalApproximation` | `UniversalApproximation.Cybenko` |
| `UniversalApproximation/Leshno/*` + `Leshno.lean` | `UniversalApproximation.Leshno` | unchanged |
| `ForMathlib/*` | per-file (e.g. `ConvolutionPolynomial`) | unchanged |

The module-path prefix `LeanPlayground` → `NeuralNetworkProofs` is orthogonal to these math
namespaces. Headline theorem names after the refactor:
- `UniversalApproximation.Cybenko.universal_approximation` (and `…universal_approximation_eps`)
- `UniversalApproximation.Leshno.leshno_dense_iff`

Renaming the Cybenko namespace touches Cybenko-internal references only (Leshno is independent).
`Family.lean` must `open NeuralNetwork` (or qualify) for `Layer`/`Network`.

## Rename details

| Artifact | From | To |
|---|---|---|
| Lake package name | `lean_playground` | `neural_network_proofs` |
| `[[lean_lib]]` name / module root | `LeanPlayground` | `NeuralNetworkProofs` |
| `defaultTargets` | `["LeanPlayground"]` | `["NeuralNetworkProofs"]` |
| Root dir / file | `LeanPlayground/`, `LeanPlayground.lean` | `NeuralNetworkProofs/`, `NeuralNetworkProofs.lean` |
| All imports | `import LeanPlayground.…` | `import NeuralNetworkProofs.…` |
| GitHub repo | `lean-playground` | `neural-network-proofs` |

GitHub rename via `gh repo rename neural-network-proofs` (GitHub keeps a redirect from the old name;
`gh` updates the local `origin` remote). This is an outward-facing action authorized by the
maintainer's explicit request. The local checkout directory and devcontainer mount are left as-is.

## Root re-export (`NeuralNetworkProofs.lean`)

```lean
import NeuralNetworkProofs.UniversalApproximation.Cybenko
import NeuralNetworkProofs.UniversalApproximation.Leshno
import NeuralNetworkProofs.NeuralNetwork.Network
```

with a module docstring naming both headline theorems. This keeps the default `lake build` target's
closure covering both developments (the gap that previously hid a stale `Theorem.olean`).

## CI design (`.github/workflows/ci.yml`)

- Triggers: `push` and `pull_request` targeting `main`.
- Use `leanprover/lean-action@v1` (installs the toolchain from `lean-toolchain`, restores the Mathlib
  build cache via `lake exe cache get`, runs `lake build`).
- **Sorry-free gate** as a subsequent step: build/run a small checker (a Lean file under a CI-only
  path, or `lake env lean` on an inline script) that emits `#print axioms` for
  `UniversalApproximation.Cybenko.universal_approximation`,
  `UniversalApproximation.Cybenko.universal_approximation_eps`, and
  `UniversalApproximation.Leshno.leshno_dense_iff`, and **fails the job if the output contains
  `sorryAx`**. This catches an admitted regression that still compiles (a `sorry` is only a warning).
- The checker theorem list is maintained alongside the headline theorems; adding a future
  monotone-UAT headline adds a line.

## CLAUDE.md

Authored with the built-in `/init` as a starting point, then tailored. There is no superpowers-
specific CLAUDE.md skill; `/init` is the appropriate tool. Required content:
- One-paragraph project description (formalizing UATs for neural networks in Lean 4 + Mathlib).
- Folder taxonomy and the namespace map (so a fresh agent knows where things live and how
  module paths relate to namespaces).
- Build & verify commands: `lake build`; the `#print axioms` sorry-free check and what a clean axiom
  set looks like (`[propext, Classical.choice, Quot.sound]`).
- Conventions: lines ≤ **100 codepoints** (note byte-vs-codepoint for unicode math glyphs); the
  no-`sorry` / report-blockers (do not hide or weaken) discipline; the `ForMathlib/` upstream
  convention and the "Intended Mathlib home" header.
- Pointer to the SDD workflow artifacts under `docs/superpowers/`.

## Known wrinkles (documented, not fixed here)

- `ForMathlib/TestFunctionDegreeBound.lean` imports `…Leshno.MollifyDef`, so it is not cleanly
  upstreamable yet. It stays in `ForMathlib/` with a header note that the Leshno dependency must be
  decoupled before actual upstreaming. Decoupling is out of scope.

## Verification / done-criteria

- `git mv` used for all moves so history is preserved.
- `lake build` of the (renamed) default target is green and its closure includes both UAT roots.
- `#print axioms` on `UniversalApproximation.Cybenko.universal_approximation`,
  `…universal_approximation_eps`, and `UniversalApproximation.Leshno.leshno_dense_iff` →
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`), checked on freshly-built oleans.
- No `import LeanPlayground.` remains anywhere; no `LeanPlayground` package/lib artifact remains.
- CI workflow present and (locally) the sorry-free checker behaves as specified.
- `CLAUDE.md` present with the content above.
- GitHub repo renamed; `origin` remote points to the new URL.
- No proof content changed (only moves, import-path updates, namespace renames, docstrings).

## Global constraints

- Do not change the *statements* or proofs of any theorem; this is moves + renames + imports +
  docstrings only. Proof content is untouched.
- Preserve git history via `git mv`.
- No new Mathlib upstream dependency.
- Line length ≤ 100 codepoints.
- A reintroduced/hidden `sorry` is never acceptable; the CI gate enforces this for the headlines.
- Commits SSH-signed.
- Land as a separate branch/PR after PR #9 merges (or rebased on it).
