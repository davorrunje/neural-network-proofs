# CLAUDE.md

Guidance for working in this repository.

## What this is

`NeuralNetworkProofs` formalizes **universal approximation theorems (UATs) for neural networks** in
Lean 4 + Mathlib. Two developments are complete and `sorry`-free:

- **Cybenko (1989)** — a single-hidden-layer network with a continuous sigmoidal activation is dense
  in `C(K, ℝ)`. Headline: `UniversalApproximation.Cybenko.universal_approximation`.
- **Leshno–Lin–Pinkus–Schocken (1993)** — an `M`-class activation densely approximates iff it is not
  (a.e.) a polynomial. Headline: `UniversalApproximation.Leshno.leshno_dense_iff`.

Next planned work: UATs for **monotonic** neural networks (lands under
`UniversalApproximation/Monotone/`).

## Layout and namespaces

The Lean module-path prefix (`NeuralNetworkProofs`) is independent of the math namespaces.

| Path | Namespace | Contents |
|------|-----------|----------|
| `NeuralNetworkProofs/ForMathlib/` | per-file (e.g. `ConvolutionPolynomial`) | Mathlib-upstream candidates; each file has an `Intended Mathlib home:` header |
| `NeuralNetworkProofs/NeuralNetwork/` | `NeuralNetwork` | general NN infrastructure (`NeuralNetwork.Layer`, `NeuralNetwork.Network`) |
| `NeuralNetworkProofs/UniversalApproximation/Cybenko/` + `Cybenko.lean` | `UniversalApproximation.Cybenko` | the Cybenko development |
| `NeuralNetworkProofs/UniversalApproximation/Leshno/` + `Leshno.lean` | `UniversalApproximation.Leshno` | the Leshno development |
| `NeuralNetworkProofs.lean` | — | root: re-exports both UAT roots so `lake build` verifies both headlines |

`UniversalApproximation/Monotone/` (namespace `UniversalApproximation.Monotone`) is reserved for the
future monotone-NN work.

## Build and verify

```bash
lake build                 # build the default target (covers both headlines)
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
> `lake build` to check it; the root `NeuralNetworkProofs.lean` re-exports both UAT roots for exactly
> this reason.

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
- **`ForMathlib/` is upstream-facing.** Keep those files self-contained (Mathlib-only deps where
  possible) and carry an `Intended Mathlib home:` header.
- Commits are SSH-signed (`git commit -S`).

## Design docs

Specs and implementation plans live under `docs/superpowers/specs/` and `docs/superpowers/plans/`.
