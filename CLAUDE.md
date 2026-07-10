# CLAUDE.md

Guidance for working in this repository.

## What this is

`NeuralNetworkProofs` formalizes **universal approximation theorems (UATs) for neural networks** in
Lean 4 + Mathlib. Four developments are complete and `sorry`-free:

- **Cybenko (1989)** — a single-hidden-layer network with a continuous sigmoidal activation is dense
  in `C(K, ℝ)`. Headline: `UniversalApproximation.Cybenko.universal_approximation`.
- **Leshno–Lin–Pinkus–Schocken (1993)** — an `M`-class activation densely approximates iff it is not
  (a.e.) a polynomial. Headline: `UniversalApproximation.Leshno.leshno_dense_iff`.
- **Monotone networks** — depth-4 monotone networks are universal for monotone functions.
  Mikulincer–Reichman (2022): threshold nets interpolate and uniformly approximate
  (`UniversalApproximation.Monotone.monotone_interpolation`, `…monotone_approximation`). Sartor et
  al. (2025): monotone one-sided-saturating activations — `…saturating_interpolation` (Thm 3.5,
  ε-approximate) and `…nonpos_weight_universal` (Prop 3.11), tied together by the point-reflection /
  weight-sign–saturation equivalence (Props 3.8 & 3.10).
- **Runje (2026): partially monotone networks** — a non-monotone feature block is embedded via an
  unconstrained single-hidden-layer Leshno network, clamped, concatenated with the monotone block,
  and fed to a monotone network. Soundness (`…Runje.PartMonoNet.monotone_snd`) and the UAP headline
  (`…Runje.partial_monotone_approximation`).

## Layout and namespaces

The Lean module-path prefix (`NeuralNetworkProofs`) is independent of the math namespaces.

| Path | Namespace | Contents |
|------|-----------|----------|
| `NeuralNetworkProofs/ForMathlib/` | per-file (e.g. `ConvolutionPolynomial`) | Mathlib-upstream candidates; each file has an `Intended Mathlib home:` header |
| `NeuralNetworkProofs/NeuralNetwork/` | `NeuralNetwork` | general NN infrastructure (`NeuralNetwork.Layer`, `NeuralNetwork.Network`) |
| `NeuralNetworkProofs/UniversalApproximation/Cybenko/` + `Cybenko.lean` | `UniversalApproximation.Cybenko` | the Cybenko development |
| `NeuralNetworkProofs/UniversalApproximation/Leshno/` + `Leshno.lean` | `UniversalApproximation.Leshno` | the Leshno development |
| `NeuralNetworkProofs/UniversalApproximation/Monotone/` + `Monotone.lean` | `UniversalApproximation.Monotone` | the monotone-network development (Mikulincer–Reichman + Sartor et al.) |
| `NeuralNetworkProofs/UniversalApproximation/Runje/` + `Runje.lean` | `UniversalApproximation.Runje` | the Runje et al. partial-monotone development |
| `NeuralNetworkProofs.lean` | — | root: re-exports the four UAT roots so `lake build` verifies all headlines |

## Build and verify

To set up a dev environment (container or host) plus the blueprint preview toolchain, run
`scripts/setup-dev.sh` — see `CONTRIBUTING.md`. Preview the blueprint with `leanblueprint web`
then `leanblueprint serve`.

```bash
lake build                 # build the default target (covers all headlines)
```

**Sorry-free check** — the real correctness gate (a `sorry` is only a *warning*, so a green build
does not by itself prove the development is admit-free):

```bash
lake env lean scripts/check_sorry_free.lean
```

A clean headline reports exactly `[propext, Classical.choice, Quot.sound]`. If any line contains
`sorryAx`, an admitted proof has been (re)introduced. CI runs this gate and fails on `sorryAx`.

> **`#print axioms` reads the compiled `.olean`, not the source.** After moving/renaming files or
> changing a proof, rebuild (`lake build`) before trusting `#print axioms` / `lean_verify` — a stale
> olean reports the *old* axioms. The default target must transitively include a theorem for
> `lake build` to check it; the root `NeuralNetworkProofs.lean` re-exports the four UAT roots for
> exactly this reason.

### Build gotcha: serialize after large file moves

A rename/move that invalidates *all* local oleans forces a from-scratch rebuild of ~26 modules. The
default `lake build` runs them concurrently, and several heavy modules loading `import Mathlib` at
once reliably hit `Too many open files` (EMFILE) in this environment. This Lake (5.0.0) has **no
`-j`/`--jobs` flag**. Work around it by building serially, one module per invocation, in dependency
order (Mathlib stays cached, so only the local modules build):

```bash
for m in ForMathlib.ConvolutionPolynomial ... UniversalApproximation.Cybenko NeuralNetworkProofs; do
  lake build "NeuralNetworkProofs.$m"
done
lake build   # final full build confirms green (all cached by now)
```

A module may print `error: build failed` (transient EMFILE) standalone yet succeed as a dependency
of the next — that is expected. Incremental builds (a few changed modules) do not need this.

## Conventions

- **Line length ≤ 100 codepoints.** Mathlib glyphs (`≤ ∞ ℝ • ⋆ ∫ ⟪⟫`) are one codepoint each;
  byte-count tools over-report — measure codepoints (`python3 -c "print(len(line))"`).
- **No `sorry`/`admit`.** A research-grade blocker is reported honestly (and, in agent workflows, as
  `NEEDS_CONTEXT`), never hidden as `sorry` or worked around by weakening a theorem statement.
- **Prefer minimal, precise imports over blanket `import Mathlib`.** This is the preferred way for
  every file, not just `ForMathlib/`. Whole-library `import Mathlib` makes `lake build` much slower
  and worsens the concurrent-build EMFILE issue above; import only the specific Mathlib modules a
  file needs (e.g. `import Mathlib.Topology.ContinuousMap.Compact`). `#min_imports` and
  `lake exe shake` suggest candidates, but both under-report open-scoped notation, instances, and
  tactics — always confirm with a clean build. Existing files that still carry `import Mathlib`
  (e.g. `Leshno/ClassM.lean`) should be trimmed opportunistically when touched.
- **`ForMathlib/` is upstream-facing.** Keep those files self-contained (Mathlib-only deps where
  possible) and carry an `Intended Mathlib home:` header.

## Design docs

Specs and implementation plans live under `docs/superpowers/specs/` and `docs/superpowers/plans/`.
