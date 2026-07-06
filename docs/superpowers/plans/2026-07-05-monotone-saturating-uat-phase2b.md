# Phase 2b — Theorem 3.5 co-design (resolving the depth-4 assembly crux)

> Status note, not yet an execution plan. Records the resolution of the Task-4 (`saturating_
> interpolation`, Thm 3.5) blocker reported in `.superpowers/sdd/sat23-task-4-report.md`
> (git-ignored scratch), so the design work survives. Awaiting a go/architecture decision.

## Why Task 4 stopped (honest blocker, no `sorry`)

Task 4 returned `NEEDS_CONTEXT`. The depth-4 construction of Thm 3.5 (arXiv:2505.02537) does **not**
follow by assembling the Tasks 1–3 lemmas as the plan assumed: those lemmas are per-layer half-space
(Lemma 3.6) and single-layer intersection (Lemma 3.7) estimates, but the theorem chains **three
nested one-sided-saturating activations** (`σ₁,σ₂,σ₃`, alternating `𝒮⁻,𝒮⁺,𝒮⁻`). The design spec
already flagged this "Phase-2 co-design" as unresolved. Three coupled gaps, and their resolution:

### Gap 1 — the non-saturating side is unbounded

A `𝒮⁻` activation has a finite limit only at `−∞`; its `+∞` side may diverge. So a layer-1 neuron's
"on" output is unbounded, with no finite target to feed layer 2.

**Resolution.** Do not send a single global gain `λ→∞`. Choose each layer's gain **sequentially and
finitely**: `λ₁` large enough that L1's *saturating* side is within `η₁` of its finite limit, then
shift by that limit `c₁ = σ₁(−∞)` so L1 outputs are `≥ 0`, `≈ 0` on the saturating side and `≥ m₁`
(a definite, finite separation, at the finitely many data points) on the other. Polarity is arranged
(via input sign / `reflect`, Prop 3.10) so the informative distinction always lands on a saturating
side downstream. Each layer sees a **bounded** input range; no actual `∞` is ever evaluated.

### Gap 2 — `intersection_inside_value` needs *exact* zero interior inputs

`intersection_inside_value` requires `∀ i, h i = 0` exactly to yield `σ b`. A saturating L1 gives
only `h i ≈ 0`. The naive fix ("`|h i| ≤ δ` ⇒ `|σ(λ∑h+b) − σ(b)| ≤ ε`") is **false** with `δ` fixed
and `λ→∞`.

**Resolution.** The genuine content is *not* a new deep lemma — it is an ε-δ continuity fact plus
assembly bookkeeping. New lemma (easy):

```
approx_interior_value : ContinuousAt σ b → 0 < ε →
    ∃ δ > 0, ∀ t, |t − b| ≤ δ → |σ t − σ b| ≤ ε
```

In the assembly, ensure the pre-activation `λ₂·∑h + b` is within `δ` of `b` by choosing the
*previous* layer's gain `λ₁` large enough that `∑h` is within `δ / λ₂` of `0`. The gains chain
**backwards** (`λ₃` fixed first → sets L3's input margin → sets L2's required output accuracy →
sets `λ₂` → sets L1's required accuracy → sets `λ₁`); no joint limit, just nested "∃ large enough".

The interior bias `b` must be a **continuity point** of `σ`. This needs **no extra hypothesis on
`σ`**: the net is existentially quantified, and a monotone `σ` has only countably many
discontinuities (`Monotone.countable_not_continuousWithinAt` / dense continuity points in Mathlib),
so we *choose* `b` at a continuity point inside the existence proof. Faithful to the paper.

### Gap 3 — γ-normalized read-out; Phase-1 engine symbols are `private`

The interior value is `γ = σ³(b)` (an arbitrary real, not `1`), so the level-set neuron outputs
`≈ γ·𝟙_A`, not `𝟙_A`; the read-out must divide by `γ`. And `readout_error_bound`, `reindex`,
`readW`, `readBias`, `interpNet_toFun_reindex` in `Interpolation.lean` are `private`.

**Resolution.** (i) Expose the needed Phase-1 read-out lemmas (add public wrappers in
`Interpolation.lean` — additive, does not touch the frozen M-R headlines). (ii) A γ-normalized
read-out `readW i = (y'ᵢ − y'ᵢ₋₁)/γ` with its own telescoping identity; `readout_error_bound`'s
`(∑|readW|)·η ≤ ε` bound then applies with `η` the L3 level-set accuracy. Requires `γ ≠ 0`.

## The one genuine faithfulness question (needs a decision / paper check)

`γ = σ³(b) ≠ 0` is required to normalize. If `σ³` is constant `0` (degenerate: both saturation
limits `0`), no interpolation is possible. **Does Thm 3.5 carry an implicit non-degeneracy
hypothesis** (σ non-constant / distinct saturation limits)? Options:

- confirm from the primary source whether Thm 3.5 assumes it, and mirror that hypothesis exactly; or
- add the minimal faithful non-degeneracy hypothesis (`∃ continuity point b, σ³ b ≠ 0`) with a
  documented deviation note.

This is a theorem-statement (faithfulness) choice, not an implementation detail — hence escalated.

## Remaining work once the architecture is fixed

1. `approx_interior_value` + "monotone ⇒ choose good bias" existence (`Saturating.lean`; low risk).
2. Public read-out wrappers in `Interpolation.lean` (additive; frozen headlines byte-identical).
3. The depth-4 assembly `saturating_interpolation` with backward-chained finite gains, polarity via
   `reflect`, and γ-normalized telescoping read-out (the bulk; medium-hard bookkeeping, uses the
   existing `*_intersection_vanishes` / `*_scaled_approx_bias` lemmas per layer).
4. Then Task 6 (`nonpos_weight_universal`, Prop 3.11) unblocks (it consumes Task 4 + Task 5).

## Paper-confirmed construction (arXiv:2505.02537, Thm 3.5 + Lemmas 3.6/3.7)

Verified against the primary source. Thm 3.5: MLP, non-negative weights, **3 hidden layers**,
interpolates any monotone non-decreasing `f` on `n` points, provided activations are monotone
non-decreasing and **alternate saturation** — Case 1 `𝒮⁻,𝒮⁺,𝒮⁻` or Case 2 `𝒮⁺,𝒮⁻,𝒮⁺`.
**No non-degeneracy hypothesis is stated.** Construction: L1 half-spaces (`σ¹(−∞)=0` normalized,
`σ¹(+∞)>0`); L2 intersections `⋂_{j>i} A⁻` via Lemma 3.7 → `≈ γ²·𝟙`, `γ²<0`; L3 intersections of
complements → `≈ γ³·𝟙_{A⁽³⁾}`, `γ³>0`, with `A⁽³⁾ᵢ = {xⱼ : f(xⱼ) ≥ f(xᵢ)}` (the level sets); L4
read-out `w = [f(x₁)−b, f(x₂)−f(x₁), …]/γ³` telescopes to `f(xᵢ)`. Lemma 3.7 asserts the interior
`≈0 → ≈γ = σᵏ(b)` (hand-waved via `λ→∞`); bias `b` "chosen post-hoc to achieve desired γ".

**Sharpened faithfulness finding.** The stated hypotheses are strictly weaker than the construction
rigorously needs. The construction requires: `σ¹(+∞) > σ¹(−∞)` (L1 separates); `σ²` attains a
suitable (negative) `γ²`; `σ³` attains `γ³ ≠ 0` at a continuity point (read-out divides by `γ³`);
and `σ²,σ³` continuous at their chosen biases (for a rigorous interior). For a constant σ, or one
whose image lacks the needed sign, the paper's specific construction does not go through. This is a
genuine gap between the paper's statement and its proof — resolving it is a theorem-statement
(faithfulness) decision, analogous to the ε-vs-exact gate.

## Derived construction blueprint (Case 1: σ₁∈𝒮⁻, σ₂∈𝒮⁺, σ₃∈𝒮⁻)

Own construction (the paper's exact proof was not extractable; this is a self-designed equivalent,
verified correct on paper — Lean is the final backstop). Reindex points `x' = x∘satReindex`, sorted
so `y'` nondecreasing and `satReindex` a linear extension. Evaluate only at data points `x'_j`.

**Minimal non-degeneracy hypotheses (the faithful additions): `σ₁, σ₂, σ₃` each non-constant**
(`∃ a b, σ_k a < σ_k b`). Everything else (biases at continuity points) is achieved *inside* the
existence proof — monotone ⇒ continuity points dense — so no further hypothesis on the `σ_k`.

Monotonicity forces the sign-flips: non-negative weights ⇒ every layer is increasing, so a single
`𝒮⁻` layer can only make an *increasing* coordinate detector (small below θ, large above). Hence:

- **L1 (σ₁∈𝒮⁻), `d·n` coord neurons.** Neuron `(r,c) = σ₁(λ₁(x_c − (x'_r)_c + m/2))`, `m` = min
  nonzero coord gap. Shifted by `−c₁ = −σ₁(−∞)`: `≈ 0` if `x_c ≤ (x'_r)_c` (below), else `≥ m₁ > 0`
  (`m₁>0` needs σ₁ non-constant). Both sides via `leftSaturating_scaled_approx_bias`.
- **L2 (σ₂∈𝒮⁺), `n` neurons.** Per `r`: `σ₂(λ₂·∑_c (L1_{r,c} − c₁) + b₂)`. Inputs `≥ 0`. Outside
  (`x ≰ x'_r`, some coord above, input `≥ m₁`): `rightSaturating_intersection_vanishes` ⇒ `≈ c₂⁺`.
  Inside (`x ≤ x'_r`, all inputs `≈ 0`): `approx_interior_value` (σ₂ cont. at `b₂`) ⇒ `≈ σ₂(b₂)`.
  Shift by `−c₂⁺=−σ₂(+∞)`: `D'_r ≈ γ₂·𝟙(x ≤ x'_r)`, `γ₂ := σ₂(b₂)−σ₂(+∞) < 0` (needs σ₂ non-const,
  b₂ below sup). Lower-set indicator; `·γ₂<0` ⇒ increasing ✓.
- **L3 (σ₃∈𝒮⁻), `n` neurons.** Per `i`: `σ₃(λ₃·∑_{r<i} 1·D'_r + b₃)` (weights `1 ≥ 0`; `−c₂⁺`
  shifts absorbed into `b₃`). Uses `𝟙(i≤j) = 1 − 𝟙(j ≤ i−1)` and `𝟙(j≤i−1) = ∃ r<i, x'_j ≤ x'_r`.
  For `j < i`: term `r=j` gives `≈γ₂<0`, others `≤ small`, so the SUM `≤ −m₃` (bounded by term
  estimates, NOT the intersection lemma) ⇒ `leftSaturating_scaled_approx_bias` ⇒ `≈ c₃⁻`. For
  `j ≥ i`: all `r<i` have `x'_j ≰ x'_r` (linear ext) so `D'_r ≈ 0`, sum `≈ 0` ⇒ `approx_interior`
  ⇒ `≈ σ₃(b₃)`. Shift by `−c₃⁻=−σ₃(−∞)`: `V_i ≈ γ₃·𝟙(i≤j)`, `γ₃ := σ₃(b₃)−σ₃(−∞) > 0` (σ₃
  non-const) ⇒ read-out weights `≥ 0` ✓.
- **L4 read-out:** `satReadout_error_bound` with `γ = γ₃ > 0`: pre-read-out `V` within `η` of
  `γ₃·𝟙(i≤j)` ⇒ output within `(∑|satReadW|)·η ≤ ε`.

**Gain chaining (backward, all finite):** fix `b₂,b₃` (continuity pts) ⇒ `γ₂,γ₃,m₃` fixed ⇒ pick
`λ₃` (L3 outside margin `m₃`, inside radius) ⇒ pick `λ₂` (L2 outside `m₁`, and small enough L2 error
`δ₂` so L3 interior holds) ⇒ pick `λ₁` (L1 accuracy `δ₁` so L2 interior holds). No joint limit.

## What is already done and sound (committed, unsigned, this branch)

Def 3.3 predicates, `reflect` + Prop 3.8 (T1); Lemma 3.6 (T2); Lemma 3.7 (T3); Prop 3.10 layer-pair
equivalence (T5) — all reviewed and axiom-clean. Only Thm 3.5 (T4) and Prop 3.11 (T6, gated on T4)
remain.
