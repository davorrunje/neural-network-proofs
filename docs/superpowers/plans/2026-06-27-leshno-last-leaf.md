# Closing the Last Leshno Leaf — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the single remaining `sorry` in the development —
`UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` — with a complete proof, making
`Mollify.mollify_ridge_mem_T` and `leshno_dense_iff` `sorryAx`-free (0 leaves).

**Architecture:** Classical Lebesgue-criterion ("good/bad cell") proof done by hand, in the existing
file `LeanPlayground/Contrib/UniformRiemannConvolution.lean`. Three small `private` helper lemmas are
added above the leaf; then the leaf's `sorry` is filled by an ε-management proof that splits the
per-cell integrand error into a φ-variation term (handled by uniform continuity of `φ` on the compact
`Icc (-M) M`) and an f-variation term (handled by splitting cells into "good" cells — disjoint from a
metric thickening of the discontinuity-closure, where `f` is uniformly continuous on a compact set —
and "bad" cells, whose total length is controlled by `tendsto_measure_cthickening_of_isCompact`).

**Tech Stack:** Lean 4 + Mathlib (`import Mathlib`, already present). Verification via the lean-lsp MCP
tools (`lean_diagnostic_messages`, `lean_verify`, `lean_goal`, `lean_multi_attempt`, `lean_loogle`,
`lean_local_search`, `lean_hover_info`).

## Global Constraints

- Do **not** modify `leshno_dense_iff`, `mollify`, `ClassM`, `T`, the `riemannSum` definition, the
  *statement* of `tendstoUniformly_riemannSum_aeContinuous`, or any already-proved lemma (in
  particular `tendstoUniformly_riemannSum_continuous` stays byte-unchanged).
- Do **not** modify any existing Cybenko file.
- No new Mathlib upstream dependency; the file's `import Mathlib` is the only import.
- Line length ≤ 100 codepoints (note: glyphs like `≤ ∞ ⋆ • ℝ` are one codepoint; byte-count linters
  over-report — measure in codepoints).
- A research-grade blocker is reported as **NEEDS_CONTEXT**, never hidden as a `sorry`, and never
  worked around by weakening the leaf statement.
- Commits are **unsigned for now** (`git commit --no-gpg-sign`), to be re-signed later.
- Verification bar: `lean_verify <name>` must report axioms `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`) for every newly-proved declaration.

## Confirmed Mathlib facts (verified to exist this session)

- `tendsto_measure_cthickening_of_isCompact (hs : IsCompact s) :`
  `Filter.Tendsto (fun r => μ (Metric.cthickening r s)) (𝓝 0) (𝓝 (μ s))` — needs
  `[ProperSpace α] [IsFiniteMeasureOnCompacts μ]`, both instances hold for `(volume : Measure ℝ)`.
- `IsCompact.uniformContinuousOn_of_continuous (hs : IsCompact s) (hf : ContinuousOn f s) :`
  `UniformContinuousOn f s`.
- `Iio_mem_nhds : a < b → Set.Iio b ∈ 𝓝 a` (used in `ℝ≥0∞`).
- `Metric.eventually_nhds_iff : (∀ᶠ x in 𝓝 a, p x) ↔ ∃ ε > 0, ∀ ⦃x⦄, dist x a < ε → p x`.

Any *other* lemma name in this plan is a best guess: confirm with `lean_local_search` /
`lean_loogle` / `lean_hover_info` before relying on it, and adapt tactics as needed. If a genuinely
required fact is absent from Mathlib, report NEEDS_CONTEXT.

## File context

`LeanPlayground/Contrib/UniformRiemannConvolution.lean` opens with `import Mathlib`,
`namespace UniformRiemannConvolution`, `open MeasureTheory Topology`. It defines:

```lean
noncomputable def riemannSum (f φ : ℝ → ℝ) (M : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    f (s - (-M + (i : ℝ) * (2 * M / m))) * φ (-M + (i : ℝ) * (2 * M / m)) * (2 * M / m)
```

and proves `tendstoUniformly_riemannSum_continuous` (the continuous-`f` case) using the cell
decomposition skeleton (`g_eq`, `hg_sum`, `hr_sum`, node facts `a`, `ha0`, `ham`, `hastep`, `ha_le`,
`ha_lb`, `ha_ub`, `hcell`) — Task 2 reuses that skeleton verbatim, re-derived inline. Read lines
17–152 of that proof before writing Task 2.

The leaf to fill (lines ~181–188):

```lean
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S := by
  sorry
```

---

### Task 1: Three `private` scaffolding lemmas

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean` (insert after
  `tendstoUniformly_riemannSum_continuous`, before the leaf's docstring).

**Interfaces:**
- Produces, in `namespace UniformRiemannConvolution`:
  - `exists_uniform_bound {f : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C) {M : ℝ}`
    `(hM : 0 < M) {S : Set ℝ} (hS : IsCompact S) :`
    `∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ y ∈ Set.Icc (-M) M, |f (s - y)| ≤ C`
  - `uniformContinuousOn_off_disc {f : ℝ → ℝ} {A : Set ℝ} (hA : IsCompact A)`
    `(hdisj : Disjoint A (closure {t : ℝ | ¬ ContinuousAt f t})) : UniformContinuousOn f A`
  - `exists_cthickening_measure_lt {K : Set ℝ} (hK : IsCompact K)`
    `(hKnull : MeasureTheory.volume K = 0) {η : ENNReal} (hη : 0 < η) :`
    `∃ δ₀ : ℝ, 0 < δ₀ ∧ MeasureTheory.volume (Metric.cthickening δ₀ K) < η`

- [ ] **Step 1: Add `exists_uniform_bound`.**

```lean
private theorem exists_uniform_bound {f : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C) {M : ℝ} (hM : 0 < M)
    {S : Set ℝ} (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ y ∈ Set.Icc (-M) M, |f (s - y)| ≤ C := by
  obtain ⟨R₀, hR₀⟩ := hS.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ := hbdd (R₀ + M)
  refine ⟨max C 0, le_max_right _ _, fun s hs y hy => ?_⟩
  have hsR : |s| ≤ R₀ := by
    have := hR₀ hs
    simpa [Real.dist_eq, sub_zero] using this
  have hyM : |y| ≤ M := by
    rw [Set.mem_Icc] at hy; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hle : |s - y| ≤ R₀ + M :=
    calc |s - y| ≤ |s| + |y| := abs_sub _ _
      _ ≤ R₀ + M := by linarith
  exact le_trans (hC _ hle) (le_max_left _ _)
```

Notes: `IsCompact.isBounded` then `Bornology.IsBounded.subset_closedBall` gives `S ⊆ closedBall 0 R₀`,
so `s ∈ S → dist s 0 ≤ R₀ → |s| ≤ R₀`. `abs_sub` is the triangle inequality `|a - b| ≤ |a| + |b|`
(if that exact name is unavailable, use `abs_sub_le` / `abs_sub_abs_le_abs_sub` family or
`(abs_add _ _).trans` after `sub_eq_add_neg`; confirm via `lean_loogle "|?a - ?b| ≤ |?a| + |?b|"`).
The `max C 0` guarantees `0 ≤ C`; since `|f t| ≥ 0`, plain `C` is already `≥ 0`, but `max` is robust.

- [ ] **Step 2: Verify Step 1.** `lean_diagnostic_messages` on the file shows no new errors at this
  lemma; `lean_verify UniformRiemannConvolution.exists_uniform_bound` →
  `[propext, Classical.choice, Quot.sound]`. (The pre-existing leaf `sorry` warning still shows; that
  is expected until Task 2.)

- [ ] **Step 3: Add `uniformContinuousOn_off_disc`.**

```lean
private theorem uniformContinuousOn_off_disc {f : ℝ → ℝ} {A : Set ℝ}
    (hA : IsCompact A) (hdisj : Disjoint A (closure {t : ℝ | ¬ ContinuousAt f t})) :
    UniformContinuousOn f A := by
  apply hA.uniformContinuousOn_of_continuous
  intro x hx
  have hxnot : x ∉ {t : ℝ | ¬ ContinuousAt f t} := fun hmem =>
    (Set.disjoint_left.mp hdisj) hx (subset_closure hmem)
  exact (not_not.mp hxnot).continuousWithinAt
```

Note: `ContinuousAt.continuousWithinAt` turns the pointwise `ContinuousAt f x` into
`ContinuousWithinAt f A x`, which is exactly `ContinuousOn f A` pointwise.

- [ ] **Step 4: Verify Step 3.** `lean_verify UniformRiemannConvolution.uniformContinuousOn_off_disc`
  → `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 5: Add `exists_cthickening_measure_lt`.**

```lean
private theorem exists_cthickening_measure_lt {K : Set ℝ}
    (hK : IsCompact K) (hKnull : MeasureTheory.volume K = 0)
    {η : ENNReal} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ MeasureTheory.volume (Metric.cthickening δ₀ K) < η := by
  have htend := tendsto_measure_cthickening_of_isCompact (μ := MeasureTheory.volume) hK
  rw [hKnull] at htend
  have hev : ∀ᶠ r in nhds (0 : ℝ),
      MeasureTheory.volume (Metric.cthickening r K) < η :=
    htend.eventually (Iio_mem_nhds hη)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  linarith
```

Note: after `rw [hKnull]`, `htend : Tendsto (fun r => volume (cthickening r K)) (𝓝 0) (𝓝 0)`.
`Iio_mem_nhds hη : Set.Iio η ∈ 𝓝 (0 : ℝ≥0∞)`, and `Tendsto.eventually` pulls it back to `𝓝 (0:ℝ)`.
`hball` has implicit binder `⦃x⦄`; if application shape differs, supply `(x := ε/2)` explicitly.

- [ ] **Step 6: Verify Step 5.** `lean_verify UniformRiemannConvolution.exists_cthickening_measure_lt`
  → `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 7: Commit.**

```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit --no-gpg-sign -m "feat(contrib): scaffolding lemmas for the a.e.-continuous Riemann leaf"
```

---

### Task 2: Prove `tendstoUniformly_riemannSum_aeContinuous`

**Files:**
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean` (replace the leaf's `sorry`; leave
  its docstring and *statement* unchanged).

**Interfaces:**
- Consumes (from Task 1): `exists_uniform_bound`, `uniformContinuousOn_off_disc`,
  `exists_cthickening_measure_lt` (signatures above).
- Consumes (from this file, unchanged): the cell-decomposition technique of
  `tendstoUniformly_riemannSum_continuous` (lines 17–152) — read it first and reuse `g_eq`, `hg_sum`,
  `hr_sum`, `a`, `ha0`, `ham`, `hastep`, `ha_le`, `ha_lb`, `ha_ub` verbatim where they are
  `f`-agnostic.
- Produces: the leaf, fully proved (no `sorry`).

This is the substantial task. Build it incrementally with `lean_goal` / `lean_multi_attempt`,
verifying after each major `have`. The proof has the following structure; implement it as a sequence
of `have` blocks. Do **not** weaken the statement; if a step is genuinely blocked, report
NEEDS_CONTEXT.

- [ ] **Step 1: Dispatch the empty-`S` case and set up constants.**

```lean
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp [TendstoUniformlyOn]    -- vacuous on ∅; adapt if `simp` does not close it
  -- φ is bounded and uniformly continuous on the compact `Icc (-M) M`
  have hMM : (-M : ℝ) ≤ M := by linarith
  have hφUC : UniformContinuousOn φ (Set.Icc (-M) M) :=
    (isCompact_Icc).uniformContinuousOn_of_continuous hφ.continuousOn
  obtain ⟨B, hB0, hBbd⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Set.Icc (-M) M, |φ y| ≤ B := by
    obtain ⟨x, _, hx⟩ := (isCompact_Icc).exists_isMaxOn
      (Set.nonempty_Icc.mpr hMM) (continuous_abs.comp hφ).continuousOn
    exact ⟨|φ x|, abs_nonneg _, fun y hy => hx hy⟩
  obtain ⟨C, hC0, hCbd⟩ := exists_uniform_bound hbdd hM hS
```

Notes: `exists_isMaxOn` / `IsCompact.exists_isMaxOn` gives the sup of `|φ|` on `Icc`; confirm the
exact name and argument order with `lean_local_search "exists_isMaxOn"`. An equivalent route is
`IsCompact.bddAbove_image` + `Real.sSup`. Either yields the uniform bound `B`.

- [ ] **Step 2: Fix the compact `J` and the null compact `K`; record their properties.**

```lean
  set J : Set ℝ := Set.Icc (sInf S - M) (sSup S + M) with hJdef
  have hJcompact : IsCompact J := isCompact_Icc
  -- every relevant evaluation point `s - y` lies in `J`
  have hsy_mem : ∀ s ∈ S, ∀ y ∈ Set.Icc (-M) M, s - y ∈ J := by
    intro s hs y hy
    have hsl : sInf S ≤ s := Real.sInf_le_of_... -- use boundedness of compact S
    have hsu : s ≤ sSup S := Real.le_sSup_of_...
    rw [Set.mem_Icc] at hy ⊢; constructor <;> linarith [hy.1, hy.2]
  set K : Set ℝ := closure {t : ℝ | ¬ ContinuousAt f t} ∩ J with hKdef
  have hKcompact : IsCompact K := hJcompact.inter_left isClosed_closure
  have hKnull : MeasureTheory.volume K = 0 :=
    measure_mono_null (Set.inter_subset_left) hdisc
```

Notes: `sInf S ≤ s` and `s ≤ sSup S` for `s ∈ S` need `S` bounded+nonempty: use
`Real.sInf_le`/`Real.le_sSup` with `hS.bddBelow`/`hS.bddAbove` (compact ⟹ bounded), or
`hS.isBounded`. Confirm exact lemma names via `lean_local_search`. `IsCompact.inter_left` needs the
*closed* factor; `closure …` is closed (`isClosed_closure`).

- [ ] **Step 3: Begin the uniform-convergence proof; introduce `ε` and the three budgets.**

```lean
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- bad-cell budget: pick η with 2 * B * C * η.toReal < ε/3 (work in ℝ via ENNReal.ofReal)
  -- good-cell budget ε/3 via uniform continuity of f on the compact complement
  -- φ-budget ε/3 via hφUC and the bound C
```

Choose `η : ℝ≥0∞ := ENNReal.ofReal (ε / (3 * (2 * B * C + 1)))` (positive since `ε > 0`). Obtain
`δ₀` from `exists_cthickening_measure_lt hKcompact hKnull (η-pos)`. Define the compact complement
`A := J \ Metric.thickening δ₀ K`; show `IsCompact A` (`hJcompact.diff Metric.isOpen_thickening`) and
`Disjoint A (closure {¬ContinuousAt f})` (a point of `A` is in `J`, so if it were in the closure it
would be in `K ⊆ Metric.thickening δ₀ K` by `Metric.self_subset_thickening (by positivity)`,
contradicting `A`'s definition). Hence `uniformContinuousOn_off_disc hAcompact hAdisj :`
`UniformContinuousOn f A`; from `Metric.uniformContinuousOn_iff` obtain `δ_f > 0` for the modulus
`ε / (3 * (2 * M + 1))`. From `hφUC` obtain `δ_φ > 0` for the modulus `ε / (3 * (C * 2 * M + 1))`.

- [ ] **Step 4: Choose the cell-count threshold `N`.**

```lean
  rw [Filter.eventually_atTop]
  refine ⟨Nat.ceil (2 * M / (min δ_f (min δ_φ δ₀))) + 1, fun m hm => ?_⟩
  intro s hs
```

Then derive (as in the continuous proof) `1 ≤ m`, `(0:ℝ) < m`, `Δ := 2 * M / m`, `0 < Δ`, and
`Δ < δ_f`, `Δ < δ_φ`, `Δ < δ₀` (the cell width is below each modulus; same `Nat.ceil` argument as
lines 55–66, applied to the `min`).

- [ ] **Step 5: Reuse the cell decomposition.** Copy verbatim from the continuous proof (they are
  `f`-agnostic): the node definitions `a`, `ha0`, `ham`, `hastep`, `ha_le`, `ha_lb`, `ha_ub`, the
  interval-integrability `hII`, `g_eq`, `hg_sum`, and `hr_sum`. These rewrite the target distance into
  `‖∑ᵢ (∫_cellᵢ f(s-y)φ(y) - ∫_cellᵢ f(s-aᵢ)φ(aᵢ))‖`.

- [ ] **Step 6: Per-cell split into φ-term and f-term.** For each `i ∈ range m`, with
  `aᵢ := a i ∈ Icc (-M) M` (from `ha_lb`, `ha_ub`):

```lean
  -- pointwise on the cell:
  -- f(s-y)·φ(y) - f(s-aᵢ)·φ(aᵢ)
  --   = f(s-y)·(φ(y) - φ(aᵢ)) + (f(s-y) - f(s-aᵢ))·φ(aᵢ)
```

Bound `‖∫_cellᵢ (f(s-y)φ(y) - f(s-aᵢ)φ(aᵢ)) dy‖` by the sum of the two term-integrals using
`intervalIntegral.norm_integral_le_of_norm_le_const` on each piece (the integrands are
interval-integrable: products/differences of `(hcont … )`-style continuous-in-`y` and constants;
note `y ↦ f (s - y)` need not be continuous, but it is interval-integrable on the cell because it is
bounded and a.e.-continuous — use `IntervalIntegrable` of a bounded measurable function, via the
a.e.-strong-measurability already available in the development; confirm the cleanest
`IntervalIntegrable` constructor with `lean_loogle`).

  - **φ-term per cell:** `|f(s-y)| ≤ C` (`hCbd s hs y …`, valid since `y ∈ Icc (-M) M` on the cell)
    and `|φ(y) - φ(aᵢ)| ≤ ε / (3*(C*2*M+1))` (`hφUC`'s modulus, `dist y aᵢ ≤ Δ < δ_φ`). So the φ-term
    integral `≤ C · (ε/(3*(C*2*M+1))) · Δ`. Summed over `range m`: `≤ ε/3` (telescoping `m·Δ = 2M`).
  - **f-term per cell:** `|φ(aᵢ)| ≤ B` (`hBbd`), so the f-term integral
    `≤ B · ∫_cellᵢ |f(s-y) - f(s-aᵢ)| dy`. Classify the cell:
    - **good** (`Set.Icc (s - a (i+1)) (s - a i) ∩ Metric.thickening δ₀ K = ∅`, i.e. the image cell in
      `u = s - y` space misses the thickening): then every `u` in the image cell and `s - aᵢ` lie in
      `A`, distance `≤ Δ < δ_f`, so `|f(s-y) - f(s-aᵢ)| ≤ ε/(3*(2M+1))` by the `UniformContinuousOn f A`
      modulus; integral `≤ ε/(3*(2M+1))·Δ`.
    - **bad** (image cell meets `Metric.thickening δ₀ K`): bound the integrand by `2C`
      (`|f(s-y)|, |f(s-aᵢ)| ≤ C`), integral `≤ 2C·Δ`.
  - **Bad-cell total.** The image cells `Iᵢ := Set.Icc (s - a (i+1)) (s - a i)` for `i ∈ range m`
    partition `J' := Icc (s-M) (s+M) ⊆ J` with pairwise-null overlaps. Each *bad* `Iᵢ` lies in
    `Metric.cthickening (δ₀ + Δ) K` (a point of `Iᵢ` within `δ₀` of `K`, plus cell width `≤ Δ`, gives
    every point within `δ₀ + Δ`; use `Metric.thickening_subset_cthickening` and the triangle bound on
    `Metric.infEdist` / `EMetric.infEdist`). Hence
    `∑_{bad} Δ = volume (⋃_{bad} Iᵢ) ≤ volume (Metric.cthickening (δ₀ + Δ) K)`. Since `δ₀ + Δ` need
    not be `≤ δ₀`, instead apply `exists_cthickening_measure_lt` to get `δ₀` with
    `volume (cthickening δ₀ K) < η` and require `Δ < δ₀` so that, choosing the *good/bad* split
    against `thickening (δ₀/2) K` and the containment radius `δ₀/2 + Δ < δ₀`, monotonicity of
    `cthickening` (`Metric.cthickening_mono`) gives `volume (cthickening (δ₀/2 + Δ) K) < η`.
    [Implementation choice: set the thickening radius used for the good/bad split to `δ₀/2`, and the
    `N`-threshold so `Δ < δ₀/2`; then bad cells lie in `cthickening (δ₀/2 + Δ) K ⊆ cthickening δ₀ K`.]
    Use `MeasureTheory.measure_biUnion_finset₀` (pairwise `AEDisjoint`, adjacent closed intervals
    share only a null endpoint) to turn `∑_{bad} Δ` into `volume (⋃_{bad} Iᵢ)`. Conclude
    `∑_{bad} (2C·Δ) = 2C·∑_{bad} Δ ≤ 2C·η.toReal < ε/3` by the choice of `η`.

- [ ] **Step 7: Assemble the three budgets.** φ-term sum `≤ ε/3`, good-cell f-term sum `≤ B·ε/3`-ish
  (fold the `B` factor into the chosen modulus so the good-cell contribution is `≤ ε/3`), bad-cell
  f-term sum `≤ ε/3`. Combine via `norm_sum_le`, `Finset.sum_le_sum`, and the telescoping
  `m · Δ = 2M`; conclude the total `< ε`. Close the `Metric.dist` goal exactly as the continuous proof
  does at lines 138–152 (`Real.dist_eq`, `Finset.sum_sub_distrib`, the `calc`).

  > **Tuning note for the implementer:** the exact constant in each modulus (the `+1` denominators)
  > exists only to keep divisions positive and the final inequality strict; adjust the three moduli so
  > each partial sum is `≤ ε/3` and the total is `< ε`. Keep `B` and `C` factored into the good-cell
  > and bad-cell moduli respectively. The arithmetic is bookkeeping, not mathematics — drive it with
  > `nlinarith`/`linarith` + `positivity` as in the continuous proof.

- [ ] **Step 8: Verify the leaf.**
  - `lean_diagnostic_messages` on the file: **zero** `sorry` warnings, zero errors.
  - `lean_verify UniformRiemannConvolution.tendstoUniformly_riemannSum_aeContinuous` →
    `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

- [ ] **Step 9: Commit.**

```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean
git commit --no-gpg-sign -m "feat(contrib): prove tendstoUniformly_riemannSum_aeContinuous (good/bad-cell)"
```

---

### Task 3: Downstream verification and inventory update

**Files:**
- Modify: `LeanPlayground/UniversalApproximation/Leshno.lean` (admit-inventory docstring, lines ~32–71).
- Modify: `LeanPlayground/Contrib/UniformRiemannConvolution.lean` (leaf docstring: replace the BLOCKER
  note with a short "proved via good/bad cells" summary).
- Possibly modify: `LeanPlayground/UniversalApproximation/Leshno/Mollify.lean` (only if a docstring
  there still calls this a leaf).

**Interfaces:**
- Consumes: the now-proved leaf from Task 2.
- Produces: a `sorryAx`-free development with an accurate inventory.

- [ ] **Step 1: Full build.** Run `lean_build` (or `lake build`); expect a green build with no errors.
  Record the job count.

- [ ] **Step 2: Verify the whole chain is `sorryAx`-free.**
  - `lean_verify Mollify.mollify_ridge_mem_T` → `[propext, Classical.choice, Quot.sound]`.
  - `lean_verify Leshno.leshno_dense_iff` (use the fully-qualified name as it appears in `Theorem.lean`)
    → `[propext, Classical.choice, Quot.sound]`.
  - If either still shows `sorryAx`, trace the dependency (some other admit was lurking) and report
    NEEDS_CONTEXT — do not edit the inventory to claim 0 leaves until both are clean.

- [ ] **Step 3: Update the leaf docstring** in `UniformRiemannConvolution.lean`: replace the multi-
  paragraph `BLOCKER (research-grade, reserved as a leaf)` block with a concise proof summary, e.g.:

```lean
/-- Same uniform Riemann-sum convergence as `tendstoUniformly_riemannSum_continuous`, but for `f`
only locally bounded and a.e. continuous (`volume (closure {t | ¬ ContinuousAt f t}) = 0`).

Proved by the classical Lebesgue-criterion ("good/bad cell") argument: the per-cell integrand error
splits into a φ-variation term (uniform continuity of `φ` on the compact `Icc (-M) M`) and an
f-variation term, whose cells split into good cells (disjoint from a metric thickening of the
discontinuity-closure, where `f` is uniformly continuous on a compact set) and bad cells, whose total
length is controlled by `tendsto_measure_cthickening_of_isCompact`. Uniform in `s ∈ S` because the
null compact `K = closure {¬ContinuousAt f} ∩ J` and the thickening radius are independent of `s`. -/
```

- [ ] **Step 4: Update the admit inventory** in `Leshno.lean`: move
  `tendstoUniformly_riemannSum_aeContinuous` from the "Remaining documented research leaf" section to
  the "Proved" section, and rewrite the header sentence(s) (lines ~34–38) to state that the
  development is now **fully `sorry`-free — 0 leaves**, so `lean_verify`/`#print axioms` on the
  top-level theorems report only `[propext, Classical.choice, Quot.sound]`. Remove the now-stale
  "exactly one `sorry`" wording.

- [ ] **Step 5: Fix any stale leaf reference** in `Mollify.lean` (search for "leaf" / "sorry" /
  "tendstoUniformly_riemannSum_aeContinuous" in that file's docstrings; update if present). If none,
  skip.

- [ ] **Step 6: Final diagnostics.** `lean_diagnostic_messages` on
  `UniformRiemannConvolution.lean`, `Mollify.lean`, and `Leshno.lean`: zero `sorry`, zero errors.
  `git grep -n "sorry" LeanPlayground/` shows no live `sorry` in the Leshno development (only the
  word inside comments/docstrings, if any — confirm none are actual tactic `sorry`).

- [ ] **Step 7: Commit.**

```bash
git add LeanPlayground/Contrib/UniformRiemannConvolution.lean \
        LeanPlayground/UniversalApproximation/Leshno.lean \
        LeanPlayground/UniversalApproximation/Leshno/Mollify.lean
git commit --no-gpg-sign -m "docs(leshno): last leaf closed — development is sorry-free (0 leaves)"
```

---

## Self-Review

**Spec coverage.** Leaf statement (untouched) → Task 2. φ-term → Task 2 Step 6. f-term good/bad split
→ Task 2 Step 6. `exists_uniform_bound` / `uniformContinuousOn_off_disc` /
`exists_cthickening_measure_lt` (spec components 1–3) → Task 1. Done-criteria (`lean_verify` clean,
downstream sorryAx-free, inventory → 0 leaves, build green) → Task 3. All global constraints carried
verbatim into the header. Covered.

**Placeholder scan.** No "TBD"/"implement later". The two `Real.sInf_le_of_…` / `Real.le_sSup_of_…`
fragments in Task 2 Step 2 and the `exists_isMaxOn` name in Step 1 are explicitly flagged as
names-to-confirm with a concrete fallback, not silent gaps; the per-step verification commands are
exact. Task 2 is intentionally given as a structured proof strategy with named lemmas rather than a
single verbatim tactic block — appropriate for a ~200-line interlocking ε-proof — with NEEDS_CONTEXT
as the discipline if a step is genuinely blocked.

**Type consistency.** `K`, `J`, `A`, `Δ`, `δ₀`, `B`, `C`, `η` are used consistently across Task 2.
Helper signatures in Task 1's Interfaces match their Step bodies. The good/bad split radius is fixed
at `δ₀/2` with containment radius `δ₀/2 + Δ ≤ δ₀` (Step 6) so the single `exists_cthickening_measure_lt`
call at radius `δ₀` covers the bad cells via `Metric.cthickening_mono`.
