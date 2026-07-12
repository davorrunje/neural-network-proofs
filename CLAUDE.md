# CLAUDE.md

Guidance for working in this repository.

## What this is

`NeuralNetworkProofs` formalizes **universal approximation theorems (UATs) for neural networks** in
Lean 4 + Mathlib. Six developments are complete and `sorry`-free:

- **Cybenko (1989)** — a single-hidden-layer network with a continuous sigmoidal activation is dense
  in `C(K, ℝ)`. Headline: `UniversalApproximation.Cybenko.universal_approximation`.
- **Leshno–Lin–Pinkus–Schocken (1993)** — an `M`-class activation densely approximates iff it is not
  (a.e.) a polynomial. Headline: `UniversalApproximation.Leshno.leshno_dense_iff`.
- **Mikulincer–Reichman (2022)** — depth-4 monotone threshold networks interpolate and uniformly
  approximate any monotone function
  (`UniversalApproximation.MikulincerReichman.monotone_interpolation`, `…monotone_approximation`),
  on the shared activation-generic core in `UniversalApproximation.Monotone`.
- **Sartor et al. (2025)** — monotone one-sided-saturating activations — Theorem 3.5
  (`UniversalApproximation.Sartor.saturating_interpolation`, ε-approximate) and Prop 3.11
  (`…nonpos_weight_universal`), tied together by the point-reflection / weight-sign–saturation
  equivalence (Props 3.8 & 3.10).
- **Runje et al. (forthcoming): Deep Constrained Monotonic Neural Networks** — extends
  Runje–Shankaranarayana 2023; skip connections make deep constrained monotone networks trainable.
  Formalized soundness (a residual stack of any depth is monotone,
  `…Runje.ResNet.monotone_toFun`) and the deep-monotone UAP headline
  (`…Runje.deep_monotone_approximation`). Includes partial monotonicity as a secondary result: a
  non-monotone feature block is embedded via an unconstrained single-hidden-layer Leshno network,
  clamped, concatenated with the monotone block, and fed to a monotone network — soundness
  (`…Runje.PartMonoNet.monotone_snd`) and the UAP headline
  (`…Runje.partial_monotone_approximation`).
- **Amos et al. (2017)** — **Input-Convex Neural Networks**: an ICNN with nonnegative propagation
  weights and convex, nondecreasing activations denotes a convex function — soundness
  (`UniversalApproximation.Amos.icnn_convex`) — and any convex, differentiable function is
  uniformly approximated on any compact set by such a network — UAP
  (`…Amos.icnn_approximation`); the general non-differentiable case is forthcoming.

## Layout and namespaces

The Lean module-path prefix (`NeuralNetworkProofs`) is independent of the math namespaces.

| Path | Namespace | Contents |
|------|-----------|----------|
| `NeuralNetworkProofs/ForMathlib/` | per-file (e.g. `ConvolutionPolynomial`) | Mathlib-upstream candidates; each file has an `Intended Mathlib home:` header |
| `NeuralNetworkProofs/NeuralNetwork/` | `NeuralNetwork` | general NN infrastructure (`NeuralNetwork.Layer`, `NeuralNetwork.Network`) |
| `NeuralNetworkProofs/UniversalApproximation/Cybenko/` + `Cybenko.lean` | `UniversalApproximation.Cybenko` | the Cybenko development |
| `NeuralNetworkProofs/UniversalApproximation/Leshno/` + `Leshno.lean` | `UniversalApproximation.Leshno` | the Leshno development |
| `NeuralNetworkProofs/UniversalApproximation/Monotone/` + `Monotone.lean` | `UniversalApproximation.Monotone` | shared `ActStack` core (infrastructure, no headline) |
| `NeuralNetworkProofs/UniversalApproximation/MikulincerReichman/` + `MikulincerReichman.lean` | `UniversalApproximation.MikulincerReichman` | the Mikulincer–Reichman development |
| `NeuralNetworkProofs/UniversalApproximation/Sartor/` + `Sartor.lean` | `UniversalApproximation.Sartor` | the Sartor et al. development |
| `NeuralNetworkProofs/UniversalApproximation/Runje/` + `Runje.lean` | `UniversalApproximation.Runje` | the Runje et al. deep constrained monotonic development (partial monotonicity secondary) |
| `NeuralNetworkProofs/UniversalApproximation/Amos/` + `Amos.lean` | `UniversalApproximation.Amos` | Input-Convex Neural Networks — soundness and UAP (differentiable convex; general case forthcoming) |
| `NeuralNetworkProofs/UniversalApproximation.lean` | `NeuralNetworkProofs.UniversalApproximation` | results aggregator (re-exports all UAT roots) |
| `NeuralNetworkProofs.lean` | — | root: imports the `UniversalApproximation` aggregator so `lake build` verifies all headlines |

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
> `lake build` to check it; the root `NeuralNetworkProofs.lean` imports the `UniversalApproximation`
> aggregator, which re-exports all seven UAT roots, for exactly this reason.

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
