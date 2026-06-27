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

private theorem exists_uniform_bound {f : ℝ → ℝ}
    (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C) {M : ℝ} (_hM : 0 < M)
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

private theorem uniformContinuousOn_off_disc {f : ℝ → ℝ} {A : Set ℝ}
    (hA : IsCompact A) (hdisj : Disjoint A (closure {t : ℝ | ¬ ContinuousAt f t})) :
    UniformContinuousOn f A := by
  apply hA.uniformContinuousOn_of_continuous
  intro x hx
  have hxnot : x ∉ {t : ℝ | ¬ ContinuousAt f t} := fun hmem =>
    (Set.disjoint_left.mp hdisj) hx (subset_closure hmem)
  exact (not_not.mp hxnot).continuousWithinAt

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

set_option maxHeartbeats 1600000 in
-- The good/bad-cell argument is a long interlocking ε-proof (cell decomposition + a.e.-continuity
-- measurability + a measure-theoretic bad-cell bound), so it exceeds the default heartbeat budget.
/-- Same uniform Riemann-sum convergence as `tendstoUniformly_riemannSum_continuous`, but for `f`
only **locally bounded and a.e. continuous** (`volume (closure {t | ¬ ContinuousAt f t}) = 0`).
The null discontinuity set controls the cells straddling discontinuities (Lebesgue's criterion).

Proved by the classical good/bad-cell argument. Splitting the per-cell integrand error
`f(s-y)·φ(y) - f(s-yᵢ)·φ(yᵢ) = f(s-y)·(φ(y)-φ(yᵢ)) + (f(s-y)-f(s-yᵢ))·φ(yᵢ)` gives two terms.
The **φ-variation** term is bounded by uniform continuity of `φ` on the compact `Icc (-M) M` and the
uniform bound on `f` from `hbdd` (`exists_uniform_bound`). For the **f-variation** term, let
`K = closure {t | ¬ ContinuousAt f t} ∩ J` for the fixed compact window
`J = Icc (sInf S - M) (sSup S + M)` holding every `s - y`; `K` is compact and null. Cells split
into **good** cells (off `Metric.thickening (δ₀/2) K`, lying in the compact
`J \ thickening (δ₀/2) K` where `f` is uniformly continuous, via `uniformContinuousOn_off_disc`)
and **bad** cells (whose image cells lie in `Metric.cthickening δ₀ K`, of total measure `< η` by
`exists_cthickening_measure_lt` / `tendsto_measure_cthickening_of_isCompact`). Since `K` and `δ₀`
are independent of `s`, all three ε/3 budgets are uniform in `s ∈ S`. No analytic-set or
measurable-selection infrastructure is needed (the earlier oscillation-supremum and `BoxIntegral`
routes that needed it are avoided entirely). -/
theorem tendstoUniformly_riemannSum_aeContinuous
    {f φ : ℝ → ℝ} (hbdd : ∀ R, ∃ C, ∀ t, |t| ≤ R → |f t| ≤ C)
    (hdisc : MeasureTheory.volume (closure {t : ℝ | ¬ ContinuousAt f t}) = 0)
    (hφ : Continuous φ) {M : ℝ} (hM : 0 < M)
    (hsupp : Function.support φ ⊆ Set.Icc (-M) M) {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun m s => riemannSum f φ M m s)
      (fun s => ∫ y, f (s - y) * φ y) Filter.atTop S := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp [TendstoUniformlyOn]
  have hMM : (-M : ℝ) ≤ M := by linarith
  -- bound on φ over the compact `Icc (-M) M`
  obtain ⟨B, hB0, hBbd⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Set.Icc (-M) M, |φ y| ≤ B := by
    obtain ⟨x, _, hx⟩ := (isCompact_Icc).exists_isMaxOn
      (Set.nonempty_Icc.mpr hMM) (continuous_abs.comp hφ).continuousOn
    exact ⟨|φ x|, abs_nonneg _, fun y hy => hx hy⟩
  -- uniform bound on `f (s - y)` for `s ∈ S`, `y ∈ Icc (-M) M`
  obtain ⟨C, hC0, hCbd⟩ := exists_uniform_bound hbdd hM hS
  -- The discontinuity-closure `D` is null.
  set D : Set ℝ := closure {t : ℝ | ¬ ContinuousAt f t} with hDdef
  have hDclosed : IsClosed D := isClosed_closure
  have hf_contOn : ContinuousOn f Dᶜ := by
    intro x hx
    have hxnot : x ∉ {t : ℝ | ¬ ContinuousAt f t} := fun hmem => hx (subset_closure hmem)
    exact (not_not.mp hxnot).continuousWithinAt
  -- For fixed `s`, `fun y => f (s - y)` is a.e.-strongly-measurable.
  have hAEf : ∀ s : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun y => f (s - y)) MeasureTheory.volume := by
    intro s
    have hmp : MeasureTheory.MeasurePreserving (fun t => s - t)
        MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume s
    -- good set in `y`: preimage of the open `Dᶜ`
    set U : Set ℝ := (fun t => s - t) ⁻¹' Dᶜ with hUdef
    have hUopen : IsOpen U :=
      hDclosed.isOpen_compl.preimage (continuous_const.sub continuous_id)
    have hcontU : ContinuousOn (fun y => f (s - y)) U := by
      have hsub : ContinuousOn (fun y => s - y) U :=
        (continuous_const.sub continuous_id).continuousOn
      exact hf_contOn.comp hsub (fun y hy => hy)
    have hAE_U : MeasureTheory.AEStronglyMeasurable (fun y => f (s - y))
        (MeasureTheory.volume.restrict U) :=
      hcontU.aestronglyMeasurable hUopen.measurableSet
    -- bad set `Uᶜ` is null
    have hUcnull : MeasureTheory.volume Uᶜ = 0 := by
      have : Uᶜ = (fun t => s - t) ⁻¹' D := by
        rw [hUdef]; rw [Set.preimage_compl, compl_compl]
      rw [this, hmp.measure_preimage (hDclosed.measurableSet.nullMeasurableSet), hDdef, hdisc]
    have hAE_Uc : MeasureTheory.AEStronglyMeasurable (fun y => f (s - y))
        (MeasureTheory.volume.restrict Uᶜ) := by
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hUcnull]
      exact MeasureTheory.aestronglyMeasurable_zero_measure _
    have hunion : MeasureTheory.AEStronglyMeasurable (fun y => f (s - y))
        (MeasureTheory.volume.restrict (U ∪ Uᶜ)) :=
      (aestronglyMeasurable_union_iff).mpr ⟨hAE_U, hAE_Uc⟩
    rwa [Set.union_compl_self, MeasureTheory.Measure.restrict_univ] at hunion
  -- compact window `J` containing all evaluation points `s - y`
  set J : Set ℝ := Set.Icc (sInf S - M) (sSup S + M) with hJdef
  have hJcompact : IsCompact J := isCompact_Icc
  have hsy_mem : ∀ s ∈ S, ∀ y ∈ Set.Icc (-M) M, s - y ∈ J := by
    intro s hs y hy
    have hsl : sInf S ≤ s := csInf_le hS.bddBelow hs
    have hsu : s ≤ sSup S := le_csSup hS.bddAbove hs
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> [linarith [hy.2]; linarith [hy.1]]
  -- the relevant (compact) part of the discontinuity set
  set K : Set ℝ := D ∩ J with hKdef
  have hKcompact : IsCompact K := hJcompact.inter_left hDclosed
  have hKnull : MeasureTheory.volume K = 0 :=
    measure_mono_null Set.inter_subset_left (hDdef ▸ hdisc)
  -- uniform continuity of φ on `Icc (-M) M`
  have hφUC : UniformContinuousOn φ (Set.Icc (-M) M) :=
    (isCompact_Icc).uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- bad-cell budget `η`
  set η : ENNReal := ENNReal.ofReal (ε / (3 * (2 * B * C + 1))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef, ENNReal.ofReal_pos]; positivity
  obtain ⟨δ₀, hδ₀pos, hδ₀meas⟩ := exists_cthickening_measure_lt hKcompact hKnull hηpos
  -- compact complement where `f` is uniformly continuous
  set A : Set ℝ := J \ Metric.thickening (δ₀ / 2) K with hAdef
  have hAcompact : IsCompact A := hJcompact.diff Metric.isOpen_thickening
  have hAdisj : Disjoint A D := by
    rw [Set.disjoint_left]
    intro u huA huD
    have huK : u ∈ K := ⟨huD, huA.1⟩
    exact huA.2 (Metric.self_subset_thickening (by positivity) K huK)
  have hfUC : UniformContinuousOn f A := uniformContinuousOn_off_disc hAcompact hAdisj
  -- f-modulus `δ_f`
  obtain ⟨δ_f, hδ_f, hδ_f'⟩ := (Metric.uniformContinuousOn_iff.mp hfUC)
    (ε / (3 * (B * (2 * M) + 1))) (by positivity)
  -- φ-modulus `δ_φ`
  obtain ⟨δ_φ, hδ_φ, hδ_φ'⟩ := (Metric.uniformContinuousOn_iff.mp hφUC)
    (ε / (3 * (C * (2 * M) + 1))) (by positivity)
  -- common cell-width threshold
  set R : ℝ := min δ_f (min δ_φ (δ₀ / 2)) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; refine lt_min hδ_f (lt_min hδ_φ ?_); positivity
  rw [Filter.eventually_atTop]
  refine ⟨Nat.ceil (2 * M / R) + 1, fun m hm => ?_⟩
  intro s hs
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  set Δ : ℝ := 2 * M / m with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; positivity
  have hΔltR : Δ < R := by
    rw [hΔdef, div_lt_iff₀ hmpos]
    have h1 : 2 * M / R < m := by
      calc 2 * M / R ≤ Nat.ceil (2 * M / R) := Nat.le_ceil _
        _ < (Nat.ceil (2 * M / R) + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self _
        _ ≤ m := by exact_mod_cast hm
    rw [div_lt_iff₀ hRpos] at h1
    linarith
  have hΔlt_f : Δ < δ_f := lt_of_lt_of_le hΔltR (min_le_left _ _)
  have hΔlt_φ : Δ < δ_φ :=
    lt_of_lt_of_le hΔltR (le_trans (min_le_right _ _) (min_le_left _ _))
  have hΔlt_δ₀ : Δ < δ₀ / 2 :=
    lt_of_lt_of_le hΔltR (le_trans (min_le_right _ _) (min_le_right _ _))
  -- `y ↦ f (s - y)` is interval-integrable on every interval (bounded + a.e. measurable).
  have hIIf : ∀ p q : ℝ, IntervalIntegrable (fun y => f (s - y)) MeasureTheory.volume p q := by
    intro p q
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    obtain ⟨Cpq, hCpq⟩ := hbdd (|s| + (|p| ⊔ |q|))
    have hfin : MeasureTheory.volume (Set.uIcc p q) ≠ ⊤ :=
      (isCompact_uIcc.measure_lt_top).ne
    apply MeasureTheory.Measure.integrableOn_of_bounded (M := Cpq) hfin (hAEf s)
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIcc).mpr (Filter.Eventually.of_forall ?_)
    intro y hy
    rw [Set.uIcc_eq_union, Set.mem_union, Set.mem_Icc, Set.mem_Icc] at hy
    have hyb : |y| ≤ |p| ⊔ |q| := by
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [abs_le] <;> constructor <;>
        first
          | (calc -(|p| ⊔ |q|) ≤ -|p| := by simp [le_sup_left]
                _ ≤ p := neg_abs_le p
                _ ≤ y := h1)
          | (calc -(|p| ⊔ |q|) ≤ -|q| := by simp [le_sup_right]
                _ ≤ q := neg_abs_le q
                _ ≤ y := h1)
          | (calc y ≤ q := h2
                _ ≤ |q| := le_abs_self q
                _ ≤ |p| ⊔ |q| := le_sup_right)
          | (calc y ≤ p := h2
                _ ≤ |p| := le_abs_self p
                _ ≤ |p| ⊔ |q| := le_sup_left)
    have : |s - y| ≤ |s| + (|p| ⊔ |q|) :=
      calc |s - y| ≤ |s| + |y| := abs_sub _ _
        _ ≤ |s| + (|p| ⊔ |q|) := by linarith
    exact hCpq _ this
  -- Cell left-endpoints (copied from the continuous proof; `f`-agnostic).
  set a : ℕ → ℝ := fun i => -M + (i : ℝ) * Δ with hadef
  have ha0 : a 0 = -M := by simp [hadef]
  have ham : a m = M := by
    simp only [hadef, hΔdef]; field_simp; ring
  have hastep : ∀ i, a (i + 1) - a i = Δ := by
    intro i; simp only [hadef]; push_cast; ring
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
  -- interval-integrability of the full integrand on each cell
  have hII : ∀ i, IntervalIntegrable (fun y => f (s - y) * φ y) MeasureTheory.volume
      (a i) (a (i + 1)) := fun i => (hIIf (a i) (a (i + 1))).mul_continuousOn hφ.continuousOn
  -- Express the convolution integral and the Riemann sum as sums over cells.
  have g_eq : (∫ y, f (s - y) * φ y) = ∫ y in (-M)..M, f (s - y) * φ y := by
    rw [intervalIntegral.integral_of_le hMM]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-M) M) (f := fun y => f (s - y) * φ y)]
    intro y hy
    have : φ y = 0 := by by_contra h; exact hy (hsupp h)
    rw [this, mul_zero]
  have hg_sum : (∫ y, f (s - y) * φ y)
      = ∑ i ∈ Finset.range m, ∫ y in (a i)..(a (i + 1)), f (s - y) * φ y := by
    rw [g_eq, ← ha0, ← ham]
    exact (intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hII k)).symm
  have hr_sum : riemannSum f φ M m s
      = ∑ i ∈ Finset.range m, ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i) := by
    rw [riemannSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const, hastep i]
    simp only [hadef, hΔdef, smul_eq_mul]; ring
  classical
  -- "good" cell: every evaluation point `s - y` (and `s - a i`) avoids the thickening.
  set good : ℕ → Prop := fun i =>
    ∀ y ∈ Set.Icc (a i) (a (i + 1)), s - y ∉ Metric.thickening (δ₀ / 2) K with hgooddef
  -- per-cell bound, splitting the integrand into a φ-variation and an f-variation term
  have hcell : ∀ i ∈ Finset.range m,
      ‖(∫ y in (a i)..(a (i + 1)), f (s - y) * φ y)
        - ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i)‖
        ≤ C * (ε / (3 * (C * (2 * M) + 1))) * Δ
          + B * (if good i then ε / (3 * (B * (2 * M) + 1)) else 2 * C) * Δ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hai_mem : a i ∈ Set.Icc (-M) M := ⟨ha_lb i, ha_ub i (le_of_lt hi)⟩
    -- interval-integrability of the two pieces
    have hII1 : IntervalIntegrable (fun y => f (s - y) * (φ y - φ (a i)))
        MeasureTheory.volume (a i) (a (i + 1)) :=
      (hIIf (a i) (a (i + 1))).mul_continuousOn (by fun_prop)
    have hII2 : IntervalIntegrable (fun y => (f (s - y) - f (s - a i)) * φ (a i))
        MeasureTheory.volume (a i) (a (i + 1)) :=
      ((hIIf (a i) (a (i + 1))).sub intervalIntegrable_const).mul_continuousOn (by fun_prop)
    -- rewrite the cell difference as the integral of the pointwise difference
    rw [← intervalIntegral.integral_sub (hII i) intervalIntegrable_const]
    have hsplit : ∀ y, f (s - y) * φ y - f (s - a i) * φ (a i)
        = f (s - y) * (φ y - φ (a i)) + (f (s - y) - f (s - a i)) * φ (a i) := by
      intro y; ring
    rw [show (fun y => f (s - y) * φ y - f (s - a i) * φ (a i))
        = (fun y => f (s - y) * (φ y - φ (a i)) + (f (s - y) - f (s - a i)) * φ (a i))
      from funext hsplit]
    rw [intervalIntegral.integral_add hII1 hII2]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · -- φ-variation term
      have hbnd : ∀ y ∈ Set.uIoc (a i) (a (i + 1)),
          ‖f (s - y) * (φ y - φ (a i))‖ ≤ C * (ε / (3 * (C * (2 * M) + 1))) := by
        intro y hy
        rw [Set.uIoc_of_le (ha_le i)] at hy
        have hy_mem : y ∈ Set.Icc (-M) M :=
          ⟨le_trans (ha_lb i) (le_of_lt hy.1), le_trans hy.2 (ha_ub (i + 1) hi)⟩
        have hfb : |f (s - y)| ≤ C := hCbd s hs y hy_mem
        have hdyai : dist y (a i) < δ_φ := by
          rw [Real.dist_eq]
          have hle : |y - a i| ≤ Δ := by
            rw [abs_le]; have := hastep i
            constructor <;> [linarith [hy.1]; linarith [hy.2]]
          exact lt_of_le_of_lt hle hΔlt_φ
        have hφb : |φ y - φ (a i)| ≤ ε / (3 * (C * (2 * M) + 1)) := by
          have := hδ_φ' y hy_mem (a i) hai_mem hdyai
          rw [Real.dist_eq] at this; linarith
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hfb hφb (abs_nonneg _) hC0
      calc ‖∫ y in (a i)..(a (i + 1)), f (s - y) * (φ y - φ (a i))‖
          ≤ C * (ε / (3 * (C * (2 * M) + 1))) * |a (i + 1) - a i| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hbnd
        _ = C * (ε / (3 * (C * (2 * M) + 1))) * Δ := by rw [hastep i, abs_of_pos hΔpos]
    · -- f-variation term
      have hφai : |φ (a i)| ≤ B := hBbd _ hai_mem
      by_cases hg : good i
      · -- good cell: use uniform continuity of `f` on `A`
        rw [if_pos hg]
        have hbnd : ∀ y ∈ Set.uIoc (a i) (a (i + 1)),
            ‖(f (s - y) - f (s - a i)) * φ (a i)‖
              ≤ B * (ε / (3 * (B * (2 * M) + 1))) := by
          intro y hy
          rw [Set.uIoc_of_le (ha_le i)] at hy
          have hy_mem : y ∈ Set.Icc (a i) (a (i + 1)) := ⟨le_of_lt hy.1, hy.2⟩
          have hy_mem' : y ∈ Set.Icc (-M) M :=
            ⟨le_trans (ha_lb i) (le_of_lt hy.1), le_trans hy.2 (ha_ub (i + 1) hi)⟩
          -- both `s - y` and `s - a i` lie in `A`
          have hsyJ : s - y ∈ J := hsy_mem s hs y hy_mem'
          have hsaJ : s - a i ∈ J := hsy_mem s hs (a i) hai_mem
          have hsyA : s - y ∈ A := ⟨hsyJ, hg y hy_mem⟩
          have haiInCell : a i ∈ Set.Icc (a i) (a (i + 1)) := ⟨le_refl _, ha_le i⟩
          have hsaA : s - a i ∈ A := ⟨hsaJ, hg (a i) haiInCell⟩
          have hdist : dist (s - y) (s - a i) < δ_f := by
            rw [Real.dist_eq]
            have heq : |(s - y) - (s - a i)| = |a i - y| := by ring_nf
            rw [heq]
            have hle : |a i - y| ≤ Δ := by
              rw [abs_le]; have := hastep i
              constructor <;> [linarith [hy.2]; linarith [hy.1]]
            exact lt_of_le_of_lt hle hΔlt_f
          have hfd : |f (s - y) - f (s - a i)| ≤ ε / (3 * (B * (2 * M) + 1)) := by
            have := hδ_f' (s - y) hsyA (s - a i) hsaA hdist
            rw [Real.dist_eq] at this; linarith
          rw [Real.norm_eq_abs, abs_mul]
          calc |f (s - y) - f (s - a i)| * |φ (a i)|
              ≤ (ε / (3 * (B * (2 * M) + 1))) * B :=
                mul_le_mul hfd hφai (abs_nonneg _) (by positivity)
            _ = B * (ε / (3 * (B * (2 * M) + 1))) := by ring
        calc ‖∫ y in (a i)..(a (i + 1)), (f (s - y) - f (s - a i)) * φ (a i)‖
            ≤ B * (ε / (3 * (B * (2 * M) + 1))) * |a (i + 1) - a i| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hbnd
          _ = B * (ε / (3 * (B * (2 * M) + 1))) * Δ := by rw [hastep i, abs_of_pos hΔpos]
      · -- bad cell: crude bound `2C`
        rw [if_neg hg]
        have hbnd : ∀ y ∈ Set.uIoc (a i) (a (i + 1)),
            ‖(f (s - y) - f (s - a i)) * φ (a i)‖ ≤ B * (2 * C) := by
          intro y hy
          rw [Set.uIoc_of_le (ha_le i)] at hy
          have hy_mem' : y ∈ Set.Icc (-M) M :=
            ⟨le_trans (ha_lb i) (le_of_lt hy.1), le_trans hy.2 (ha_ub (i + 1) hi)⟩
          have hfy : |f (s - y)| ≤ C := hCbd s hs y hy_mem'
          have hfai : |f (s - a i)| ≤ C := hCbd s hs (a i) hai_mem
          have hfd : |f (s - y) - f (s - a i)| ≤ 2 * C :=
            le_trans (abs_sub _ _) (by linarith)
          rw [Real.norm_eq_abs, abs_mul]
          calc |f (s - y) - f (s - a i)| * |φ (a i)|
              ≤ (2 * C) * B := mul_le_mul hfd hφai (abs_nonneg _) (by positivity)
            _ = B * (2 * C) := by ring
        calc ‖∫ y in (a i)..(a (i + 1)), (f (s - y) - f (s - a i)) * φ (a i)‖
            ≤ B * (2 * C) * |a (i + 1) - a i| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hbnd
          _ = B * (2 * C) * Δ := by rw [hastep i, abs_of_pos hΔpos]
  have ha_mono : ∀ i j : ℕ, i ≤ j → a i ≤ a j := by
    intro i j hij; simp only [hadef]
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith [hΔpos]
  -- The set of "bad" cells.
  set Bad : Finset ℕ := (Finset.range m).filter (fun i => ¬ good i) with hBaddef
  -- Image cells in `u = s - y` space (half-open, hence genuinely disjoint).
  set Cell : ℕ → Set ℝ := fun i => Set.Ioc (a i) (a (i + 1)) with hCelldef
  -- Containment of bad image cells in the closed thickening of radius `δ₀`.
  have hbad_sub : ∀ i ∈ Bad,
      (fun y => s - y) '' Cell i ⊆ Metric.cthickening δ₀ K := by
    intro i hi u hu
    obtain ⟨y, hyCell, rfl⟩ := hu
    rw [hBaddef, Finset.mem_filter] at hi
    have hnotgood : ¬ good i := hi.2
    rw [hgooddef] at hnotgood
    simp only [not_forall, not_not, exists_prop] at hnotgood
    obtain ⟨y₀, hy₀mem, hy₀thick⟩ := hnotgood
    rw [hCelldef] at hyCell
    have hyIcc : y ∈ Set.Icc (a i) (a (i + 1)) := ⟨le_of_lt hyCell.1, hyCell.2⟩
    -- `s - y₀` is within `δ₀/2` of `K`
    rw [Metric.mem_thickening_iff_infEDist_lt] at hy₀thick
    rw [Metric.mem_cthickening_iff]
    -- triangle inequality on `infEDist`
    calc Metric.infEDist (s - y) K
        ≤ Metric.infEDist (s - y₀) K + edist (s - y) (s - y₀) :=
          Metric.infEDist_le_infEDist_add_edist
      _ ≤ ENNReal.ofReal (δ₀ / 2) + ENNReal.ofReal Δ := by
          refine add_le_add hy₀thick.le ?_
          rw [edist_dist, Real.dist_eq]
          apply ENNReal.ofReal_le_ofReal
          have heq : |(s - y) - (s - y₀)| = |y₀ - y| := by ring_nf
          rw [heq, abs_le]
          have h1 := hyIcc.1; have h2 := hyIcc.2
          have h3 := hy₀mem.1; have h4 := hy₀mem.2
          have := hastep i
          constructor <;> linarith
      _ ≤ ENNReal.ofReal δ₀ := by
          rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hΔpos)]
          apply ENNReal.ofReal_le_ofReal; linarith
  -- Measure of the union of bad image cells is `< η`.
  have hmp : MeasureTheory.MeasurePreserving (fun t => s - t)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume s
  have hunion_le : MeasureTheory.volume (⋃ i ∈ Bad, Cell i)
      ≤ MeasureTheory.volume (Metric.cthickening δ₀ K) := by
    have hsub : (⋃ i ∈ Bad, Cell i)
        ⊆ (fun y => s - y) ⁻¹' (Metric.cthickening δ₀ K) := by
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨i, hiBad, hyCell⟩ := hy
      exact hbad_sub i hiBad ⟨y, hyCell, rfl⟩
    calc MeasureTheory.volume (⋃ i ∈ Bad, Cell i)
        ≤ MeasureTheory.volume ((fun y => s - y) ⁻¹' (Metric.cthickening δ₀ K)) :=
          measure_mono hsub
      _ = MeasureTheory.volume (Metric.cthickening δ₀ K) :=
          hmp.measure_preimage Metric.isClosed_cthickening.measurableSet.nullMeasurableSet
  -- Turn the union measure into the cardinality count.
  have hcell_meas : ∀ i, MeasureTheory.volume (Cell i) = ENNReal.ofReal Δ := by
    intro i; rw [hCelldef]; simp only [Real.volume_Ioc, hastep i]
  have hdisjBad : (↑Bad : Set ℕ).Pairwise
      (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) Cell) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : a (i + 1) ≤ a j := ha_mono _ _ h
      refine Disjoint.aedisjoint ?_
      simp only [hCelldef]
      exact Set.Ioc_disjoint_Ioc.mpr
        (le_trans (min_le_left _ _) (le_trans hle (le_max_right _ _)))
    · have hle : a (j + 1) ≤ a i := ha_mono _ _ h
      refine Disjoint.aedisjoint ?_
      simp only [hCelldef]
      exact Set.Ioc_disjoint_Ioc.mpr
        (le_trans (min_le_right _ _) (le_trans hle (le_max_left _ _)))
  have hbiUnion : MeasureTheory.volume (⋃ i ∈ Bad, Cell i)
      = (Bad.card : ENNReal) * ENNReal.ofReal Δ := by
    rw [MeasureTheory.measure_biUnion_finset₀ hdisjBad
      (fun i _ => (measurableSet_Ioc).nullMeasurableSet)]
    simp only [hcell_meas, Finset.sum_const, nsmul_eq_mul]
  -- Hence `Bad.card * Δ ≤ ε / (3 * (2 * B * C + 1))`.
  have hbadcard : (Bad.card : ℝ) * Δ ≤ ε / (3 * (2 * B * C + 1)) := by
    have hlt : (Bad.card : ENNReal) * ENNReal.ofReal Δ < η := by
      rw [← hbiUnion]; exact lt_of_le_of_lt hunion_le hδ₀meas
    rw [hηdef] at hlt
    have hofr : ENNReal.ofReal ((Bad.card : ℝ) * Δ)
        < ENNReal.ofReal (ε / (3 * (2 * B * C + 1))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simpa using hlt
    have := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hofr
    linarith
  -- Assemble the three budgets.
  rw [Real.dist_eq, hg_sum, hr_sum, ← Finset.sum_sub_distrib, ← Real.norm_eq_abs]
  -- per-cell: dominate by φ-budget + good-budget + bad-indicator
  have hcell' : ∀ i ∈ Finset.range m,
      ‖(∫ y in (a i)..(a (i + 1)), f (s - y) * φ y)
        - ∫ _y in (a i)..(a (i + 1)), f (s - a i) * φ (a i)‖
        ≤ C * (ε / (3 * (C * (2 * M) + 1))) * Δ + B * (ε / (3 * (B * (2 * M) + 1))) * Δ
          + (if ¬ good i then 2 * B * C * Δ else 0) := by
    intro i hi
    refine le_trans (hcell i hi) ?_
    by_cases hg : good i
    · rw [if_pos hg, if_neg (not_not.mpr hg)]; simp only [add_zero]
      exact le_of_eq (by ring)
    · rw [if_neg hg, if_pos (by exact hg)]
      have hgood_nonneg : 0 ≤ B * (ε / (3 * (B * (2 * M) + 1))) * Δ := by positivity
      have : B * (2 * C) * Δ = 2 * B * C * Δ := by ring
      linarith
  refine lt_of_le_of_lt (le_trans (norm_sum_le _ _) (Finset.sum_le_sum hcell')) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- evaluate the three sums
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  rw [← Finset.sum_filter]
  have hbadsum : ∑ _i ∈ Bad, 2 * B * C * Δ = 2 * B * C * ((Bad.card : ℝ) * Δ) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hbadsum]
  -- the `m * Δ = 2 * M` telescoping identity
  have hmΔ : (m : ℝ) * Δ = 2 * M := by rw [hΔdef]; field_simp
  -- φ-budget ≤ ε/3
  have hφbud : (m : ℝ) * (C * (ε / (3 * (C * (2 * M) + 1))) * Δ) ≤ ε / 3 := by
    have : (m : ℝ) * (C * (ε / (3 * (C * (2 * M) + 1))) * Δ)
        = C * (2 * M) / (3 * (C * (2 * M) + 1)) * ε := by
      rw [show (m : ℝ) * (C * (ε / (3 * (C * (2 * M) + 1))) * Δ)
        = C * ((m : ℝ) * Δ) * ε / (3 * (C * (2 * M) + 1)) by ring, hmΔ]; ring
    rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hCM : 0 ≤ C * (2 * M) := by positivity
    nlinarith [hε, hCM]
  -- good-budget ≤ ε/3
  have hgbud : (m : ℝ) * (B * (ε / (3 * (B * (2 * M) + 1))) * Δ) ≤ ε / 3 := by
    have : (m : ℝ) * (B * (ε / (3 * (B * (2 * M) + 1))) * Δ)
        = B * (2 * M) / (3 * (B * (2 * M) + 1)) * ε := by
      rw [show (m : ℝ) * (B * (ε / (3 * (B * (2 * M) + 1))) * Δ)
        = B * ((m : ℝ) * Δ) * ε / (3 * (B * (2 * M) + 1)) by ring, hmΔ]; ring
    rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hBM : 0 ≤ B * (2 * M) := by positivity
    nlinarith [hε, hBM]
  -- bad-budget < ε/3
  have hbbud : 2 * B * C * ((Bad.card : ℝ) * Δ) < ε / 3 := by
    have h2bc : 0 ≤ 2 * B * C := by positivity
    have hkey : 2 * B * C * ((Bad.card : ℝ) * Δ)
        ≤ 2 * B * C * (ε / (3 * (2 * B * C + 1))) :=
      mul_le_mul_of_nonneg_left hbadcard h2bc
    refine lt_of_le_of_lt hkey ?_
    rw [show 2 * B * C * (ε / (3 * (2 * B * C + 1)))
      = (2 * B * C) * ε / (3 * (2 * B * C + 1)) by ring]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hε, h2bc]
  -- combine the three budgets: total < ε
  calc (m : ℝ) * (C * (ε / (3 * (C * (2 * M) + 1))) * Δ)
        + (m : ℝ) * (B * (ε / (3 * (B * (2 * M) + 1))) * Δ)
        + 2 * B * C * ((Bad.card : ℝ) * Δ)
      < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add_of_le_of_lt (add_le_add hφbud hgbud) hbbud
    _ = ε := by ring

end UniformRiemannConvolution
