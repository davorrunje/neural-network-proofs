import Mathlib

/-! # Uniform Riemann-sum approximation of a convolution against a continuous kernel.
Intended Mathlib home: `Mathlib/Analysis/Convolution` (confirm with maintainers). -/

namespace UniformRiemannConvolution

open MeasureTheory Topology

/-- Point-sampling Riemann sum of `y ↦ f (s - y) * φ y` over `m` equal cells of `Icc (-M) M`. -/
noncomputable def riemannSum (f φ : ℝ → ℝ) (M : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    f (s - (-M + (i : ℝ) * (2 * M / m))) * φ (-M + (i : ℝ) * (2 * M / m)) * (2 * M / m)

/-- For continuous `f`, continuous `φ` supported in `Icc (-M) M`, and a compact `S`, the
point-sampling Riemann sums converge to the convolution integral uniformly for `s ∈ S`. -/
theorem tendstoUniformly_riemannSum_continuous
    {f φ : ℝ → ℝ} (hf : Continuous f) (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S := by
  -- The joint integrand `Φ (s, y) = f (s - y) * φ y` is continuous.
  set Φ : ℝ × ℝ → ℝ := fun p => f (p.1 - p.2) * φ p.2 with hΦ
  have hΦcont : Continuous Φ := by
    fun_prop
  -- It is uniformly continuous on the compact set `S ×ˢ Icc (-M) M`.
  have hK : IsCompact (S ×ˢ Set.Icc (-M) M) := hS.prod (isCompact_Icc)
  have hUC : UniformContinuousOn Φ (S ×ˢ Set.Icc (-M) M) :=
    hK.uniformContinuousOn_of_continuous hΦcont.continuousOn
  -- Reduce the convolution integral to an interval integral on `(-M)..M`.
  have hMM : (-M : ℝ) ≤ M := by linarith
  have g_eq : ∀ s : ℝ, (∫ y, f (s - y) * φ y) = ∫ y in (-M)..M, f (s - y) * φ y := by
    intro s
    rw [intervalIntegral.integral_of_le hMM]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-M) M) (f := fun y => f (s - y) * φ y)]
    intro y hy
    have : φ y = 0 := by
      by_contra h
      exact hy (hsupp h)
    rw [this, mul_zero]
  -- Continuity of the integrand in `y` for fixed `s` (used for interval-integrability).
  have hcont_y : ∀ s : ℝ, Continuous (fun y => f (s - y) * φ y) := by
    intro s; fun_prop
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Choose the modulus `ε' = ε / (2 * M + 1)` and obtain `δ` from uniform continuity.
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff.mp hUC) (ε / (2 * M + 1))
    (by positivity)
  rw [Filter.eventually_atTop]
  refine ⟨Nat.ceil (2 * M / δ) + 1, fun m hm => ?_⟩
  intro s hs
  -- Basic facts about `m` and the cell width `Δ = 2 * M / m`.
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  set Δ : ℝ := 2 * M / m with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; positivity
  have hΔlt : Δ < δ := by
    rw [hΔdef, div_lt_iff₀ hmpos]
    have h1 : 2 * M / δ < m := by
      calc 2 * M / δ ≤ Nat.ceil (2 * M / δ) := Nat.le_ceil _
        _ < (Nat.ceil (2 * M / δ) + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self _
        _ ≤ m := by exact_mod_cast hm
    rw [div_lt_iff₀ hδ] at h1
    linarith
  -- Cell left-endpoints.
  set a : ℕ → ℝ := fun i => -M + (i : ℝ) * Δ with hadef
  have ha0 : a 0 = -M := by simp [hadef]
  have ham : a m = M := by
    simp only [hadef, hΔdef]
    field_simp
    ring
  have hastep : ∀ i, a (i + 1) - a i = Δ := by
    intro i; simp only [hadef]; push_cast; ring
  -- The integrand `y ↦ f (s - y) * φ y` is interval-integrable on every cell.
  have hII : ∀ i, IntervalIntegrable (fun y => f (s - y) * φ y) MeasureTheory.volume
      (a i) (a (i + 1)) := fun i => (hcont_y s).intervalIntegrable _ _
  -- Express the convolution integral as a sum over cells.
  have hg_sum : (∫ y, f (s - y) * φ y)
      = ∑ i ∈ Finset.range m, ∫ y in (a i)..(a (i + 1)), f (s - y) * φ y := by
    rw [g_eq s, ← ha0, ← ham]
    exact (intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hII k)).symm
  -- Express the Riemann sum as a sum over cells (constant integrand per cell).
  have hr_sum : riemannSum f φ M m s
      = ∑ i ∈ Finset.range m, ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i) := by
    rw [riemannSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const, hastep i]
    simp only [hadef, hΔdef, smul_eq_mul]
    ring
  -- Node monotonicity and containment in `Icc (-M) M`.
  have ha_le : ∀ i, a i ≤ a (i + 1) := by
    intro i; have := hastep i; linarith
  have ha_lb : ∀ i, -M ≤ a i := by
    intro i; simp only [hadef]; have : (0:ℝ) ≤ (i : ℝ) * Δ := by positivity
    linarith
  have ha_ub : ∀ i, i ≤ m → a i ≤ M := by
    intro i hi
    have hmono : a i ≤ a m := by
      simp only [hadef]
      have : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
      nlinarith [hΔpos]
    rw [ham] at hmono; exact hmono
  -- Per-cell error bound.
  have hcell : ∀ i ∈ Finset.range m,
      ‖(∫ y in (a i)..(a (i + 1)), f (s - y) * φ y)
        - ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i)‖ ≤ (ε / (2 * M + 1)) * Δ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hai_mem : a i ∈ Set.Icc (-M) M := ⟨ha_lb i, ha_ub i (le_of_lt hi)⟩
    rw [← intervalIntegral.integral_sub (hII i)
      (intervalIntegrable_const)]
    have hbound : ∀ y ∈ Set.uIoc (a i) (a (i + 1)),
        ‖f (s - y) * φ y - f (s - a i) * φ (a i)‖ ≤ ε / (2 * M + 1) := by
      intro y hy
      rw [Set.uIoc_of_le (ha_le i)] at hy
      have hy_mem : y ∈ Set.Icc (-M) M :=
        ⟨le_trans (ha_lb i) (le_of_lt hy.1), le_trans hy.2 (ha_ub (i + 1) hi)⟩
      have hd : dist ((s, y) : ℝ × ℝ) (s, a i) < δ := by
        rw [Prod.dist_eq]
        simp only [dist_self]
        have : dist y (a i) ≤ Δ := by
          rw [Real.dist_eq, abs_le]
          constructor <;> [skip; skip] <;>
            [(have := hy.1; have := hastep i; linarith);
             (have := hy.2; have := hastep i; linarith)]
        exact lt_of_le_of_lt (by simpa using this) hΔlt
      have := hδ' (s, y) ⟨hs, hy_mem⟩ (s, a i) ⟨hs, hai_mem⟩ hd
      simp only [hΦ, Real.dist_eq] at this ⊢
      exact le_of_lt this
    calc ‖∫ y in (a i)..(a (i + 1)), (f (s - y) * φ y - f (s - a i) * φ (a i))‖
        ≤ (ε / (2 * M + 1)) * |a (i + 1) - a i| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = (ε / (2 * M + 1)) * Δ := by rw [hastep i, abs_of_pos hΔpos]
  -- Combine: total error `≤ m * (ε' * Δ) = ε' * 2M < ε`.
  rw [Real.dist_eq, hg_sum, hr_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ i ∈ Finset.range m,
        ((∫ y in (a i)..(a (i + 1)), f (s - y) * φ y)
          - ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i))‖
      ≤ ∑ i ∈ Finset.range m,
          ‖(∫ y in (a i)..(a (i + 1)), f (s - y) * φ y)
            - ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, (ε / (2 * M + 1)) * Δ := Finset.sum_le_sum hcell
    _ = (m : ℝ) * ((ε / (2 * M + 1)) * Δ) := by rw [Finset.sum_const, Finset.card_range]; ring
    _ = (ε / (2 * M + 1)) * (2 * M) := by
          rw [hΔdef]; field_simp
    _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [hε, hM]

/-- Same uniform Riemann-sum convergence as `tendstoUniformly_riemannSum_continuous`, but for `f`
only **locally bounded and a.e. continuous** (`volume (closure {t | ¬ ContinuousAt f t}) = 0`).
The null discontinuity set controls the cells straddling discontinuities (Lebesgue's criterion).

BLOCKER (research-grade, reserved as a leaf). Splitting the per-cell integrand error
`f(s-yᵢ)·φ(yᵢ) - f(s-y)·φ(y) = f(s-yᵢ)·(φ(yᵢ)-φ(y)) + (f(s-yᵢ)-f(s-y))·φ(y)` reduces the proof to
two terms. The **φ-variation** term is handled exactly as in the continuous case (uniform continuity
of `φ` + the uniform bound on `f` from `hbdd` on the compact `S - Icc (-M) M`). The **f-variation**
term `∑ᵢ φ(yᵢ) ∫_cell (f(s-yᵢ)-f(s-y)) dy` is the L¹ partition-oscillation of `y ↦ f(s-y)` and is
the Lebesgue criterion for Riemann integrability of the *point-sampled* equispaced Riemann sum,
**uniformly** in `s ∈ S`. Two routes were investigated and both bottom out on measure-theoretic
infrastructure that this Mathlib does not package:

* Riemann↔Lebesgue via `BoxIntegral` (tagged prepartitions under the `Riemann` integration-params
  filter, e.g. `BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt`) neither specialises to
  this fixed equispaced point-sampling sum nor gives a parameter-uniform tendsto.
* Dominating the `f`-variation term by the pointwise oscillation `⨆_{h∈[0,Δ]} |f(v)-f(v+h)|` over a
  fixed (`s`-independent) compact domain, then dominated convergence: the bound holds and its
  integral does tend to `0`, but the oscillation majorant is a supremum over an *uncountable*
  compact index, so its (a.e.) measurability needs a measurable section-supremum / analytic-set
  (`AnalyticSet.nullMeasurableSet`) result that Mathlib lacks. The naive countable (rational) sup
  undershoots: at a discontinuity reached only by an irrational shift it misses the jump.

The remaining tractable in-repo route is the classical good/bad-cell argument (cover the null
closure of the discontinuity set by a small-measure open set via outer regularity, use uniform
continuity on the compact complement, and bound the straddling cells uniformly in `s`) — a
many-line measure-theory development reserved as this leaf. -/
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S := by
  sorry

end UniformRiemannConvolution
