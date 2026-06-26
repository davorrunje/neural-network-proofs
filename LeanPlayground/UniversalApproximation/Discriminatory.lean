import Mathlib
import LeanPlayground.UniversalApproximation.Activation

/-! # Discriminatory property of sigmoidal activations (Cybenko 1989, §3). -/

namespace UniversalApproximation

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A sigmoidal function is bounded: continuity plus finite limits at ±∞. -/
theorem Sigmoidal.bounded {σ : ℝ → ℝ} (hσ : Sigmoidal σ) : ∃ C, ∀ t, |σ t| ≤ C := by
  -- Near `+∞`, `σ` is within `1` of `1`, hence `|σ| ≤ 2`.
  have hT : ∀ᶠ t in Filter.atTop, |σ t| ≤ 2 := by
    have := hσ.atTop.eventually (eventually_abs_sub_lt 1 (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with t ht
    have : |σ t - 1| < 1 := ht
    rw [abs_sub_lt_iff] at this
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  -- Near `-∞`, `σ` is within `1` of `0`, hence `|σ| ≤ 1`.
  have hB : ∀ᶠ t in Filter.atBot, |σ t| ≤ 1 := by
    have := hσ.atBot.eventually (eventually_abs_sub_lt 0 (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with t ht
    have : |σ t - 0| < 1 := ht
    simp only [sub_zero] at this
    linarith [this]
  rw [eventually_atTop] at hT
  rw [eventually_atBot] at hB
  obtain ⟨A, hA⟩ := hT
  obtain ⟨B, hBb⟩ := hB
  -- On the compact interval `[B, A]`, continuity gives a bound `C`.
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := B) (b := A)).exists_bound_of_continuousOn
    (f := σ) hσ.continuous.continuousOn
  refine ⟨max C 2, fun t => ?_⟩
  rcases le_or_gt t B with h | h
  · calc |σ t| ≤ 1 := hBb t h
      _ ≤ max C 2 := le_trans (by norm_num) (le_max_right _ _)
  rcases le_or_gt A t with h' | h'
  · exact le_trans (hA t h') (le_max_right _ _)
  · have hmem : t ∈ Set.Icc B A := ⟨le_of_lt h, le_of_lt h'⟩
    have := hC t hmem
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)

/-- As `m → ∞`, `σ (m * t + φ) → 1` when `t > 0`: the inner argument tends to `+∞`. -/
theorem sigmoidal_tendsto_pos {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : 0 < t) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) Filter.atTop (𝓝 1) := by
  have hinner : Tendsto (fun m : ℕ => (m : ℝ) * t + φ) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Tendsto.atTop_mul_const ht tendsto_natCast_atTop_atTop
  exact hσ.atTop.comp hinner

/-- As `m → ∞`, `σ (m * t + φ) → 0` when `t < 0`: the inner argument tends to `-∞`. -/
theorem sigmoidal_tendsto_neg {σ : ℝ → ℝ} (hσ : Sigmoidal σ) {t : ℝ} (ht : t < 0) (φ : ℝ) :
    Tendsto (fun m : ℕ => σ (m * t + φ)) Filter.atTop (𝓝 0) := by
  have hinner : Tendsto (fun m : ℕ => (m : ℝ) * t + φ) Filter.atTop Filter.atBot := by
    apply Filter.tendsto_atBot_add_const_right
    exact Tendsto.atTop_mul_neg ht tendsto_natCast_atTop_atTop tendsto_const_nhds
  exact hσ.atBot.comp hinner

/-- The pointwise limit underlying the dominated-convergence step. For a fixed real `s` the
scaled-shifted sigmoid `m ↦ σ (m * s + φ)` converges to the *step value* `1` for `s > 0`,
`σ φ` for `s = 0`, and `0` for `s < 0`. We package the three cases as a single indicator
combination over the half-line `Ioi 0` and the singleton `{0}`. -/
private theorem sigmoidal_step_ptwise {σ : ℝ → ℝ} (hσ : Sigmoidal σ) (s φ : ℝ) :
    Tendsto (fun m : ℕ => σ ((m : ℝ) * s + φ)) Filter.atTop
      (𝓝 ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) s
          + σ φ * ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) s)) := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have h1 : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) s = 0 := by
      simp [not_lt.mpr (le_of_lt hs)]
    have h2 : ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) s = 0 := by simp [ne_of_lt hs]
    rw [h1, h2]; simp only [mul_zero, add_zero]
    exact sigmoidal_tendsto_neg hσ hs φ
  · subst hs
    have h1 : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (0 : ℝ) = 0 := by simp
    have h2 : ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) (0 : ℝ) = 1 := by simp
    rw [h1, h2]
    have heq : (fun m : ℕ => σ ((m : ℝ) * 0 + φ)) = (fun _ => σ φ) := by ext m; ring_nf
    rw [heq]; simp
  · have h1 : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) s = 1 := by simp [hs]
    have h2 : ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) s = 0 := by simp [ne_of_gt hs]
    rw [h1, h2]; simp only [mul_zero, add_zero]
    exact sigmoidal_tendsto_pos hσ hs φ

/-- **Dominated convergence on a finite measure.** As `m → ∞`, the integral of the
scaled-shifted sigmoid `x ↦ σ (m * (⟪w, x⟫ + b) + φ)` against a finite measure `ν` converges to
`ν P + σ φ • ν H`, where `P = {0 < ⟪w, x⟫ + b}` is the open half-space and
`H = {⟪w, x⟫ + b = 0}` the hyperplane. The sigmoid is bounded (`Sigmoidal.bounded`), so the
constant bound is `ν`-integrable; the pointwise limit is `sigmoidal_step_ptwise`, and the limit
integrand is evaluated by `integral_indicator_const`. -/
private theorem sigmoidal_step_integral_tendsto {σ : ℝ → ℝ} (hσ : Sigmoidal σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (ν : Measure ↥K) [IsFiniteMeasure ν]
    (w : EuclideanSpace ℝ (Fin n)) (b φ : ℝ) :
    Tendsto
      (fun m : ℕ => ∫ x : ↥K, σ ((m : ℝ) * (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) + φ) ∂ν)
      Filter.atTop
      (𝓝 ((ν {x : ↥K | 0 < ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b}).toReal
          + σ φ * (ν {x : ↥K | ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b = 0}).toReal)) := by
  obtain ⟨C, hC⟩ := hσ.bounded
  set g : ↥K → ℝ := fun x => ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b with hg
  have hgc : Continuous g := by fun_prop
  have hP : MeasurableSet {x : ↥K | 0 < g x} := hgc.measurable measurableSet_Ioi
  have hH : MeasurableSet {x : ↥K | g x = 0} := hgc.measurable (measurableSet_singleton 0)
  set f : ↥K → ℝ := fun x =>
    (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (g x)
    + σ φ * ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) (g x) with hf
  have hFc : ∀ m : ℕ, Continuous (fun x : ↥K => σ ((m : ℝ) * g x + φ)) :=
    fun m => hσ.continuous.comp (by fun_prop)
  have key := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun m : ℕ => fun x : ↥K => σ ((m : ℝ) * g x + φ))
    (f := f) (bound := fun _ => C)
    (fun m => (hFc m).aestronglyMeasurable)
    (integrable_const C)
    (fun m => Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC _))
    (Filter.Eventually.of_forall (fun x => sigmoidal_step_ptwise hσ (g x) φ))
  -- Identify the indicators of real sets with indicators of the corresponding subtype sets.
  have hf1 : (fun x : ↥K => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (g x))
           = {x : ↥K | 0 < g x}.indicator (fun _ => (1 : ℝ)) := by
    ext x; simp [Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
  have hf2 : (fun x : ↥K => ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) (g x))
           = {x : ↥K | g x = 0}.indicator (fun _ => (1 : ℝ)) := by
    ext x; simp [Set.indicator_apply, Set.mem_setOf_eq]
  have hf2smul : (fun x : ↥K => σ φ * ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) (g x))
           = fun x => σ φ • ({x : ↥K | g x = 0}.indicator (fun _ => (1 : ℝ)) x) := by
    rw [← hf2]; rfl
  -- Evaluate the limit integral via `integral_indicator_const`.
  have hint : ∫ x : ↥K, f x ∂ν
      = (ν {x : ↥K | 0 < g x}).toReal + σ φ * (ν {x : ↥K | g x = 0}).toReal := by
    rw [hf, integral_add]
    · rw [hf1, integral_indicator_const (1 : ℝ) hP]
      congr 1
      · simp [Measure.real]
      · rw [hf2smul, integral_smul, integral_indicator_const (1 : ℝ) hH]; simp [Measure.real]
    · rw [hf1]; exact (integrable_const (1 : ℝ)).indicator hP
    · rw [hf2smul]; exact ((integrable_const (1 : ℝ)).indicator hH).smul (σ φ)
  rw [← hint] at *
  exact key

/-- The signed measure of a measurable set, expressed through the Jordan decomposition:
`μ s = (μ⁺ s).toReal - (μ⁻ s).toReal`. -/
private theorem signedMeasure_apply_eq {α : Type*} [MeasurableSpace α] (μ : SignedMeasure α)
    {s : Set α} (hs : MeasurableSet s) :
    μ s = (μ.toJordanDecomposition.posPart s).toReal
        - (μ.toJordanDecomposition.negPart s).toReal := by
  conv_lhs => rw [← MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition μ]
  rw [MeasureTheory.JordanDecomposition.toSignedMeasure, sub_apply,
      Measure.toSignedMeasure_apply_measurable hs, Measure.toSignedMeasure_apply_measurable hs]
  rfl

variable {σ : ℝ → ℝ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- **Cybenko's analytic crux.** If a signed measure `μ` annihilates every affine
pre-composition `x ↦ σ (⟪w, x⟫ + b)` of a sigmoidal `σ`, then `μ` assigns measure `0` to every
open half-space `{0 < ⟪w, x⟫ + b}` and every hyperplane `{⟪w, x⟫ + b = 0}`.

The proof scales the direction: applying the hypothesis to `(m • w, m * b + φ)` gives, for every
`m` and `φ`, a vanishing signed integral of `x ↦ σ (m * (⟪w, x⟫ + b) + φ)`. Dominated convergence
on each Jordan part (`sigmoidal_step_integral_tendsto`) sends this to
`μ P + σ φ • μ H = 0` for all `φ`. Since `σ` takes two distinct values, the resulting linear
system forces `μ H = 0` and then `μ P = 0`. -/
theorem signed_halfspace_eq_zero (hσ : Sigmoidal σ) {μ : SignedMeasure ↥K}
    (H0 : ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0)
    (w : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    μ {x : ↥K | 0 < ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b} = 0 ∧
    μ {x : ↥K | ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b = 0} = 0 := by
  set P := {x : ↥K | 0 < ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b} with hPdef
  set Hy := {x : ↥K | ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b = 0} with hHdef
  have hgc : Continuous (fun x : ↥K => ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) := by fun_prop
  have hP : MeasurableSet P := hgc.measurable measurableSet_Ioi
  have hH : MeasurableSet Hy := hgc.measurable (measurableSet_singleton 0)
  -- Step (1)+(2)+(3): for every shift `φ`, `μ P + σ φ * μ Hy = 0`.
  have key : ∀ φ : ℝ, μ P + σ φ * μ Hy = 0 := by
    intro φ
    -- (1) Per-`m` vanishing via the hypothesis at `(m • w, m * b + φ)`.
    have hzero : ∀ m : ℕ, signedIntegral μ
        (fun x => σ ((m : ℝ) * (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) + φ)) = 0 := by
      intro m
      have h := H0 ((m : ℝ) • w) ((m : ℝ) * b + φ)
      have heq : (fun x : ↥K => σ ((m : ℝ) * (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) + φ))
               = (fun x : ↥K =>
                   σ (⟪(m : ℝ) • w, (x : EuclideanSpace ℝ (Fin n))⟫ + ((m : ℝ) * b + φ))) := by
        ext x; rw [real_inner_smul_left]; ring_nf
      rw [heq]; exact h
    -- (2) Dominated convergence on each Jordan part.
    have hpos := sigmoidal_step_integral_tendsto hσ μ.toJordanDecomposition.posPart w b φ
    have hneg := sigmoidal_step_integral_tendsto hσ μ.toJordanDecomposition.negPart w b φ
    have hsub := hpos.sub hneg
    -- The difference sequence is `signedIntegral`, identically `0`.
    have hseq : (fun m : ℕ =>
        (∫ x : ↥K, σ ((m : ℝ) * (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) + φ)
            ∂μ.toJordanDecomposition.posPart)
        - (∫ x : ↥K, σ ((m : ℝ) * (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b) + φ)
            ∂μ.toJordanDecomposition.negPart))
        = (fun _ : ℕ => (0 : ℝ)) := by
      ext m; exact hzero m
    rw [hseq] at hsub
    have hlim0 := tendsto_nhds_unique hsub tendsto_const_nhds
    -- (3) Translate the (toReal) Jordan-part limit into the signed measure.
    rw [signedMeasure_apply_eq μ hP, signedMeasure_apply_eq μ hH]
    rw [eq_comm] at hlim0
    linarith [hlim0]
  -- Step (4): two distinct values of `σ` solve the linear system.
  obtain ⟨φ₁, φ₂, hne⟩ : ∃ φ₁ φ₂ : ℝ, σ φ₁ ≠ σ φ₂ := by
    have hT : ∀ᶠ t in Filter.atTop, (1 : ℝ) / 2 < σ t :=
      hσ.atTop.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
    have hB : ∀ᶠ t in Filter.atBot, σ t < (1 : ℝ) / 2 :=
      hσ.atBot.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨t1, ht1⟩ := hT.exists
    obtain ⟨t2, ht2⟩ := hB.exists
    exact ⟨t1, t2, by intro h; rw [h] at ht1; linarith⟩
  have e1 := key φ₁
  have e2 := key φ₂
  have hdiff : (σ φ₁ - σ φ₂) * μ Hy = 0 := by ring_nf; linarith [e1, e2]
  have hHy : μ Hy = 0 := by
    rcases mul_eq_zero.mp hdiff with hz | hz
    · exact absurd (sub_eq_zero.mp hz) hne
    · exact hz
  refine ⟨?_, hHy⟩
  rw [hHy] at e1; simpa using e1

/-- **The characteristic function of `μ` vanishes.** If a signed measure `μ` annihilates every
affine pre-composition of a sigmoidal `σ`, then for every direction `w` both the cosine and sine
moments `signedIntegral μ (cos⟪w,·⟫)` and `signedIntegral μ (sin⟪w,·⟫)` vanish. -/
theorem charFun_eq_zero (hσ : Sigmoidal σ) {μ : SignedMeasure ↥K}
    (H0 : ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ),
        signedIntegral μ (fun x => σ (⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ + b)) = 0)
    (w : EuclideanSpace ℝ (Fin n)) :
    signedIntegral μ (fun x => Real.cos ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫) = 0 ∧
    signedIntegral μ (fun x => Real.sin ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫) = 0 := by
  -- The real-valued "score" `f x = ⟪w, x⟫`; push `μ`'s Jordan parts forward along `f`.
  set f : ↥K → ℝ := fun x => ⟪w, (x : EuclideanSpace ℝ (Fin n))⟫ with hfdef
  have hfc : Continuous f := by fun_prop
  have hfm : Measurable f := hfc.measurable
  set μp := μ.toJordanDecomposition.posPart with hμp
  set μn := μ.toJordanDecomposition.negPart with hμn
  -- (1) Every closed half-space `{f ≤ a}` has signed measure `0`: it is the disjoint union of
  -- the open half-space `{f < a}` and the hyperplane `{f = a}`, both of signed measure `0`.
  have hclosed : ∀ a : ℝ, μ {x : ↥K | f x ≤ a} = 0 := by
    intro a
    have hopen := signed_halfspace_eq_zero hσ H0 (-w) a
    -- `{0 < ⟪-w, x⟫ + a} = {f x < a}` and `{⟪-w, x⟫ + a = 0} = {f x = a}`.
    have hset1 : {x : ↥K | 0 < ⟪(-w), (x : EuclideanSpace ℝ (Fin n))⟫ + a}
               = {x : ↥K | f x < a} := by
      ext x
      simp only [Set.mem_setOf_eq, hfdef, inner_neg_left]
      constructor <;> intro h <;> linarith
    have hset2 : {x : ↥K | ⟪(-w), (x : EuclideanSpace ℝ (Fin n))⟫ + a = 0}
               = {x : ↥K | f x = a} := by
      ext x
      simp only [Set.mem_setOf_eq, hfdef, inner_neg_left]
      constructor <;> intro h <;> linarith
    rw [hset1, hset2] at hopen
    obtain ⟨hlt, heq⟩ := hopen
    have hmlt : MeasurableSet {x : ↥K | f x < a} := hfm measurableSet_Iio
    have hmeq : MeasurableSet {x : ↥K | f x = a} := hfm (measurableSet_singleton a)
    have hdisj : Disjoint {x : ↥K | f x < a} {x : ↥K | f x = a} := by
      rw [Set.disjoint_left]; intro x hx hx'; simp only [Set.mem_setOf_eq] at hx hx'; linarith
    have hunion : {x : ↥K | f x ≤ a} = {x : ↥K | f x < a} ∪ {x : ↥K | f x = a} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union]; exact le_iff_lt_or_eq
    rw [hunion, MeasureTheory.VectorMeasure.of_union hdisj hmlt hmeq, hlt, heq, add_zero]
  -- (2) On every closed half-space, the Jordan parts have equal mass (since the signed measure
  -- there is `0` and both parts are finite).
  have hagree : ∀ a : ℝ, μp (f ⁻¹' Set.Iic a) = μn (f ⁻¹' Set.Iic a) := by
    intro a
    have hms : MeasurableSet {x : ↥K | f x ≤ a} := hfm measurableSet_Iic
    have hpre : f ⁻¹' Set.Iic a = {x : ↥K | f x ≤ a} := by ext x; simp [Set.mem_Iic]
    have hz := signedMeasure_apply_eq μ hms
    rw [hclosed a, ← hμp, ← hμn] at hz
    have hreal : (μp {x : ↥K | f x ≤ a}).toReal = (μn {x : ↥K | f x ≤ a}).toReal := by linarith
    rw [hpre]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μp _) (measure_ne_top μn _)).mp hreal
  -- (3) The pushforwards `μp.map f` and `μn.map f` agree on all `Iic a`, hence are equal.
  have hmapeq : μp.map f = μn.map f := by
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.map_apply hfm measurableSet_Iic, Measure.map_apply hfm measurableSet_Iic]
    exact hagree a
  -- (4) Change of variables on each Jordan part turns the cos/sin moments into integrals against
  -- the pushforwards, which coincide.
  have hcos : StronglyMeasurable Real.cos := Real.continuous_cos.stronglyMeasurable
  have hsin : StronglyMeasurable Real.sin := Real.continuous_sin.stronglyMeasurable
  refine ⟨?_, ?_⟩
  · change signedIntegral μ (fun x => Real.cos (f x)) = 0
    rw [signedIntegral, ← integral_map_of_stronglyMeasurable hfm hcos,
        ← integral_map_of_stronglyMeasurable hfm hcos, hmapeq, sub_self]
  · change signedIntegral μ (fun x => Real.sin (f x)) = 0
    rw [signedIntegral, ← integral_map_of_stronglyMeasurable hfm hsin,
        ← integral_map_of_stronglyMeasurable hfm hsin, hmapeq, sub_self]

end UniversalApproximation
