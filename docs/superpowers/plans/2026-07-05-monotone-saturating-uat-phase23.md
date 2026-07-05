# Monotone Saturating-Activation UAT — Phases 2+3 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development. Steps use
> checkbox (`- [ ]`) syntax. Stacks on Phase 1 (same branch `feat/monotone-saturating-uat`); lands in
> the single combined PR #19.

**Goal:** Formalize Sartor et al. Theorem 3.5 (Result 1) and Propositions 3.8/3.10/3.11 (Results 2/3)
on top of the Phase-1 activation-generic core, `sorry`-free.

**Architecture:** Build the saturating-activation predicates (Def 3.3) + point-reflection (Prop 3.8);
the quantitative half-space (Lemma 3.6) and intersection (Lemma 3.7) limits; assemble the depth-4
alternating-saturation interpolation net (Thm 3.5, **ε-approximate** — see gate resolution) reusing
Phase-1 `readout_error_bound` + `sort_key_linear_extension`; then the weight-sign↔saturation
equivalence (Prop 3.10) and non-positive-weight universal approximation (Prop 3.11).

**Tech Stack:** Lean 4 + Mathlib; lean-lsp; subagent-driven-development.

## Global Constraints

- **Faithful Thm 3.5 statement = ε-APPROXIMATE interpolation** (gate resolved): the paper's literal
  `g(xᵢ)=f(xᵢ)` is a λ→∞ idealization (Lemmas 3.6/3.7 are "≈"; Def 3.3 saturation requires the limit
  to *exist*, not be attained). The true, provable statement for finite nets:
  `∀ ε>0, ∃ N (monotone MLP, depth 4, activations monotone + alternating-saturation), ∀ i,
  |N.toFun (x i) − y i| ≤ ε`. Document the paper's idealized `=` in the theorem docstring (honest
  deviation note — NOT a silent weakening).
- **Frozen (unchanged):** M-R headlines `monotone_interpolation`, `monotone_approximation`
  (byte-identical + `[propext, Classical.choice, Quot.sound]`) and the `MonoNet` interface.
- **Reuse Phase 1:** `ActStack` (per-layer activation), `MonoNet`, `readout_error_bound`,
  `Basic.sort_key_linear_extension`, `Basic.dist_le_of_coord`. Do not duplicate.
- **`sorry`/`admit`-free.** A genuine research blocker → **`NEEDS_CONTEXT`**, never `sorry`, never a
  weakened statement. Several tasks below are research-hard; honesty is mandatory.
- **No `set_option maxHeartbeats`; lines ≤ 100 codepoints; docstrings on public decls.**
- **Deferred signing:** all commits **unsigned**; do NOT sign (user batch-signs later). Do NOT open a
  new PR — commits stack on the existing branch/PR #19.
- **Branch:** `feat/monotone-saturating-uat`.

## New headlines (namespace `UniversalApproximation.Monotone`; provisional names)

- `saturating_interpolation` — Theorem 3.5 (ε-approximate, statement above).
- `nonpos_weight_universal` — Proposition 3.11.
- supporting public: `reflect` (σ'(x) = −σ(−x)) + Prop 3.8 lemmas; the Prop 3.10 equivalence lemma.

## Construction reference (from the paper)

- **Def 3.3:** `RightSaturating σ := ∃ L, Tendsto σ atTop (𝓝 L)`; `LeftSaturating σ` via `atBot`.
- **Lemma 3.6 (half-space):** layer-1 neuron `σ(λ αᵀ(x−β))`, `α ≥ 0`; as `λ→∞` → `σ(+∞)` on
  `αᵀ(x−β)>0`, `σ(−∞)` on `<0`. For `σ∈𝒮⁻`: `σ(−∞)=` the finite left limit.
- **Lemma 3.7 (intersection):** `σ(b + λ ∑ᵢ hᵢ)` with large `λ` → `σ(sat side)=0` outside `A`,
  `σ(b)=γ` inside, per saturation side.
- **Thm 3.5 layers:** L1 half-spaces, L2 intersections, L3 level-sets `Aᵢ={x: f(x)≥f(xᵢ)}`, L4
  read-out `g = b + ∑ⱼ (f(xⱼ)−f(xⱼ₋₁))·𝟙_{Aⱼ}` (telescopes to `f(xᵢ)`; weights ≥ 0 since sorted).
- **Prop 3.8:** `σ'(x) = −σ(−x)` monotone; `σ∈𝒮⁻ ↔ σ'∈𝒮⁺`.
- **Prop 3.10:** two consecutive `W≤0` layers with `σ` ≡ two `W≥0` layers with `σ'`.
- **Prop 3.11:** 4-layer `W≤0`, `σ∈𝒮⁻∪𝒮⁺` universal (via 3.10 → alternating → Thm 3.5).

## Per-Task Protocol

Read the brief + named interfaces; implement; build the module; `lean_diagnostic_messages` clean;
for headline tasks confirm axiom-clean + M-R headlines still byte-identical; `git add`, STOP
(controller commits UNSIGNED, packages, dispatches reviewer, records ledger). **If a proof is
research-blocked, report NEEDS_CONTEXT with the precise obstruction — never `sorry`.**

---

## Task 1: Saturating predicates + point reflection (`Saturating.lean`, part A)

**Files:** Create `NeuralNetworkProofs/UniversalApproximation/Monotone/Saturating.lean` (part A).
**Produces:** `RightSaturating σ`, `LeftSaturating σ` (Def 3.3, via `Filter.Tendsto σ atTop/atBot
(𝓝 _)`); `reflect (σ) : ℝ → ℝ := fun x => −σ (−x)`; `reflect_monotone (Monotone σ → Monotone
(reflect σ))`; `reflect_rightSaturating_iff` / `reflect_leftSaturating_iff` (Prop 3.8: `σ∈𝒮⁻ ↔
reflect σ ∈ 𝒮⁺` and dual); `reflect_reflect : reflect (reflect σ) = σ`.
**Notes:** pure Mathlib analysis (`Filter.Tendsto`, `Filter.tendsto_neg_atBot_iff`, `Monotone.neg`,
`neg_neg`). Tractable.
- [ ] Implement + prove; module builds; diagnostics clean. Stage; controller commits unsigned.

## Task 2: Quantitative half-space limit — Lemma 3.6 (`Saturating.lean`, part B)  ★ analytic core

**Files:** Modify `Saturating.lean`.
**Consumes:** Task 1 predicates. **Produces:** a quantitative half-space lemma: for `σ` monotone +
right/left-saturating, and a finite margin `m > 0`, for every `ε>0` there is `λ` such that
`σ (λ t)` is within `ε` of its saturation value whenever `|t| ≥ m` (both sides), i.e. the neuron
approximates the half-space indicator to `ε` off the margin. State it so Task 4 can apply it at the
finite dataset's separation margin.
**Strategy:** from `Tendsto σ atTop (𝓝 L⁺)`, `∀ ε, ∃ M, ∀ z ≥ M, |σ z − L⁺| ≤ ε`; take `λ ≥ M/m`.
Dual for `atBot`. Uses `Metric.tendsto_atTop`/`NormedAddCommGroup` ε-δ of limits.
- [ ] Implement + prove; diagnostics clean. **NEEDS_CONTEXT (not `sorry`) if the quantitative
  packaging proves intractable.** Stage; controller commits unsigned.

## Task 3: Intersection via saturation — Lemma 3.7 (`Saturating.lean`, part C)  ★ analytic core

**Files:** Modify `Saturating.lean`.
**Consumes:** Tasks 1–2. **Produces:** the intersection lemma: a saturating unit over a non-negative
combination of (approximate) half-space indicators approximates `γ·𝟙_A` (A = intersection) to `ε`
off-margin, per saturation side (the `σ(−∞)=0` / `σ(+∞)=0` alternation). State quantitatively for
Task 4.
**Strategy:** compose Task 2's bound; the "outside A ⇒ pre-activation saturates to the 0 side"
argument via monotonicity + the non-negative combination. Research-hard.
- [ ] Implement + prove; diagnostics clean. NEEDS_CONTEXT if blocked. Stage; commit unsigned.

## Task 4: Theorem 3.5 — depth-4 alternating-saturation interpolation (`Saturating.lean`, part D)  ★ crux

**Files:** Modify `Saturating.lean`.
**Consumes:** Tasks 1–3; Phase-1 `readout_error_bound`, `sort_key_linear_extension`, `MonoNet`,
`ActStack`. **Produces (headline):** `saturating_interpolation` — the ε-approximate statement in
Global Constraints, for activations `σ¹,σ²,σ³` monotone with alternating saturation (𝒮⁻,𝒮⁺,𝒮⁻ or
reverse).
**Strategy:** reindex by `sort_key_linear_extension` (as M-R); build the depth-4 `ActStack` with the
three alternating saturating activations + gain `λ` (L1 half-spaces, L2 intersections, L3 level-sets)
+ non-negative telescoping read-out (`readW i = f(x'ᵢ)−f(x'ᵢ₋₁)`, ≥ 0 by sort); for target `ε`,
pick `λ` (via Tasks 2–3 at the dataset's separation margin) so the pre-read-out level-set vector is
within `η` of `𝟙(i≤j)`, then `readout_error_bound` gives `≤ (∑|readW|)·η ≤ ε`. Prove `IsMonotone`
(monotone activations + non-negative weights) and `depth = 4`.
**Docstring:** note the paper states Thm 3.5 as exact `g(xᵢ)=f(xᵢ)` (λ→∞ idealization); we formalize
the finite-net ε-approximate form.
- [ ] Implement + prove; module build exit 0; `lean_verify …saturating_interpolation` →
  `[propext, Classical.choice, Quot.sound]`; M-R headlines still byte-identical. **NEEDS_CONTEXT (not
  `sorry`) if the assembly/λ-choice won't close.** Stage; commit unsigned.

## Task 5: Weight-sign ↔ saturation equivalence — Prop 3.10 (`Equivalence.lean`)

**Files:** Create `Equivalence.lean`.
**Consumes:** Task 1 (`reflect`, Prop 3.8), `Defs` (`ActStack`, `Layer`). **Produces:** the layer-pair
equivalence — a two-layer `ActStack` segment with non-positive weights and activation `σ` denotes the
same function as a segment with non-negative weights and activation `reflect σ` (Prop 3.10). State
via the layer denotations (`Layer.toFun`); the sign flip is absorbed by `reflect` (`−σ(−·)`) and
`W ↦ −W`.
**Strategy:** algebraic — `(reflect σ)((−W).mulVec x + c') = −σ(−((−W)·x+c')) = σ(W·x − c')`;
choose biases so the two segments agree. Mostly computational (`Matrix.neg_mulVec`, `neg_neg`).
- [ ] Implement + prove; diagnostics clean. NEEDS_CONTEXT if blocked. Stage; commit unsigned.

## Task 6: Non-positive-weight universal approximation — Prop 3.11 (`NonPositive.lean`)

**Files:** Create `NonPositive.lean`.
**Consumes:** Task 4 (`saturating_interpolation`) + Task 5 (Prop 3.10). **Produces (headline):**
`nonpos_weight_universal` — a 4-layer non-positive-weight MLP with `σ∈𝒮⁻∪𝒮⁺` ε-approximates any
monotone dataset (Prop 3.11), by applying Prop 3.10 to convert to the non-negative alternating case
and invoking `saturating_interpolation`.
- [ ] Implement + prove; `lean_verify …nonpos_weight_universal` axiom-clean. NEEDS_CONTEXT if blocked.
  Stage; commit unsigned.

## Task 7: Wiring (`Monotone.lean`, `scripts/check_sorry_free.lean`)

**Files:** Modify `Monotone.lean` (import `Saturating`, `Equivalence`, `NonPositive`; docstring);
`scripts/check_sorry_free.lean` (add the two new headlines).
- [ ] `lake build …Monotone` exit 0; the gate lists all headlines. Stage; commit unsigned.

---

## Task F1: Whole-branch verification
- [ ] Full `lake build` green; all headlines (M-R + `saturating_interpolation` +
  `nonpos_weight_universal`) `[propext, Classical.choice, Quot.sound]` on fresh oleans; M-R headlines
  byte-identical to `origin/main`; sorry-free gate clean; no `maxHeartbeats`; ≤ 100 codepoints.

## Task F2: Final whole-branch review
- [ ] `review-package $(git merge-base origin/main HEAD) HEAD`; dispatch final reviewer (most capable
  model): faithful ε-statement (+ documented idealization note); saturating construction sound;
  Prop 3.10/3.11 correct; frozen invariants intact; no `sorry`. Fix Critical/Important via one fix
  subagent; re-verify.

## Task F3: HELD — batch-sign + finalize PR (user present)
- [ ] When the user returns: confirm signing; batch-sign all unpushed commits from the last pushed
  commit; verify all `G`; re-verify build + axioms; push (fast-forward); update PR #19 to describe
  the full Phases 1–3 formalization; confirm CI.
