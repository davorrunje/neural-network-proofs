/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib
import NeuralNetworkProofs.UniversalApproximation.Leshno.ClassM
import NeuralNetworkProofs.ForMathlib.IteratedDerivPolynomial

/-! # The univariate smooth derivative-trick engine for the Leshno UAT.

This file works abstractly on `C(↥I, ℝ)` for a compact real set `I`, with the (closed) span of
all dilated/translated copies of a fixed `g : ℝ → ℝ`. The univariate target of the Leshno (1993)
universal-approximation theorem, in its smooth-activation reduction, is the statement that the
closure of this span is everything (`⊤`) whenever `g` is smooth and not (everywhere) a polynomial.

* `Sg g I hg` — the `ℝ`-submodule of `C(↥I, ℝ)` spanned by `t ↦ g (λ t + b)` over all `(λ, b)`;
* `deriv_pow_mem` (B1, **leaf**) — `t ↦ tᵏ · g⁽ᵏ⁾(λ t + b)` lies in the closure of `Sg g`;
* `exists_deriv_ne` (B2) — a smooth non-polynomial has a nonzero `k`-th derivative for each `k`;
* `smooth_engine` (B3, glue) — the closed span is all of `C(↥I, ℝ)`.
-/

namespace UniversalApproximation.Leshno

open Topology IteratedDerivPolynomial
open scoped ContDiff

/-- The span of dilated/translated copies of `g`, inside `C(I,ℝ)` for a compact real set `I`. -/
def Sg (g : ℝ → ℝ) (I : Set ℝ) (hg : Continuous g) : Submodule ℝ C(↥I, ℝ) :=
  Submodule.span ℝ (Set.range fun lb : ℝ × ℝ =>
    (⟨fun t => g (lb.1 * (t : ℝ) + lb.2), by fun_prop⟩ : C(↥I, ℝ)))

/-- Per-point Taylor/MVT bound: if `‖G' − G' u‖ ≤ ε` along the whole segment from `u` to
`u + h`, then `‖G (u+h) − G u − h · G' u‖ ≤ ε · |h|`.  Here `G' = deriv G`. -/
private lemma taylor_seg_bound {G : ℝ → ℝ} (hG : Differentiable ℝ G) (u h ε : ℝ)
    (hseg : ∀ x ∈ segment ℝ u (u + h), |deriv G x - deriv G u| ≤ ε) :
    |G (u + h) - G u - h * deriv G u| ≤ ε * |h| := by
  -- Apply the convex mean-value bound to `f x = G x - x * deriv G u`,
  -- whose derivative is `deriv G x - deriv G u`.
  set f : ℝ → ℝ := fun x => G x - x * deriv G u with hf
  set f' : ℝ → ℝ := fun x => deriv G x - deriv G u with hf'
  have hderiv : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    have h1 : HasDerivAt G (deriv G x) x := (hG x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y * deriv G u) (deriv G u) x := by
      simpa using (hasDerivAt_id x).mul_const (deriv G u)
    exact h1.sub h2
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := segment ℝ u (u + h)) (C := ε)
    (fun x _ => (hderiv x).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hseg x hx)
    (convex_segment u (u + h)) (left_mem_segment ℝ u (u + h)) (right_mem_segment ℝ u (u + h))
  -- `f (u+h) - f u = G(u+h) - G u - h * deriv G u`.
  have hfe : f (u + h) - f u = G (u + h) - G u - h * deriv G u := by
    simp only [hf]; ring
  rw [hfe] at hbound
  calc |G (u + h) - G u - h * deriv G u| = ‖G (u + h) - G u - h * deriv G u‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ε * ‖(u + h) - u‖ := hbound
    _ = ε * |h| := by rw [Real.norm_eq_abs]; ring_nf

/-- B1 (leaf). For smooth `g`, the function `t ↦ tᵏ · g⁽ᵏ⁾(λt+b)` lies in the closure of `Sg g`.

Proved by induction on `k` (generalizing `λ, b`). The base case is a generator of `Sg g`. For the
step, with `G := g⁽ᵏ⁾`, the difference quotients `D_s := s⁻¹ · (Φ_{λ+s} − Φ_λ)`, where
`Φ_μ(t) = tᵏ · G(μ t + b)` is the `k`-case map (in `closure (Sg g)` by the IH at dilation `μ`), lie
in `closure (Sg g)` since it is a submodule. As `s → 0` they converge **uniformly on the compact
`I`** to `Ψ(t) = tᵏ⁺¹ · g⁽ᵏ⁺¹⁾(λt+b)`: a per-point Taylor/MVT bound (`taylor_seg_bound`, via
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) plus uniform continuity of `G'` on a compact
interval containing every `λt+b` give a uniform error estimate. As `closure (Sg g)` is closed
(`Submodule.isClosed_topologicalClosure`), the limit `Ψ` lies in it (`IsClosed.mem_of_tendsto`
along `sₙ = 1/(n+1)`). -/
theorem deriv_pow_mem {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (I : Set ℝ) (hI : IsCompact I)
    (k : ℕ) (lam b : ℝ) :
    (⟨fun t => (t : ℝ) ^ k * iteratedDeriv k g (lam * (t : ℝ) + b), by
        have := hg.continuous_iteratedDeriv k (by exact_mod_cast le_top); fun_prop⟩ : C(↥I, ℝ))
      ∈ (Sg g I hg.continuous).topologicalClosure := by
  haveI : CompactSpace (↥I) := isCompact_iff_compactSpace.mp hI
  induction k generalizing lam b with
  | zero =>
      have hmem : (⟨fun t => g (lam * (t : ℝ) + b), by fun_prop⟩ : C(↥I, ℝ))
          ∈ Sg g I hg.continuous :=
        Submodule.subset_span ⟨(lam, b), rfl⟩
      have heq : (⟨fun t => (t : ℝ) ^ 0 * iteratedDeriv 0 g (lam * (t : ℝ) + b), by
            have := hg.continuous_iteratedDeriv 0 (by exact_mod_cast le_top); fun_prop⟩ : C(↥I, ℝ))
          = (⟨fun t => g (lam * (t : ℝ) + b), by fun_prop⟩ : C(↥I, ℝ)) := by
        ext t; simp
      rw [heq]
      exact Submodule.le_topologicalClosure _ hmem
  | succ k ih =>
      -- Notation. `G = g⁽ᵏ⁾`; its derivative is `g⁽ᵏ⁺¹⁾`.
      set G : ℝ → ℝ := iteratedDeriv k g with hGdef
      have hGdiff : Differentiable ℝ G :=
        hg.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top k)
      have hG'cont : Continuous (deriv G) := by
        have : deriv G = iteratedDeriv (k + 1) g := (iteratedDeriv_succ).symm
        rw [this]
        exact hg.continuous_iteratedDeriv (k + 1) (by exact_mod_cast le_top)
      -- The target continuous map `Ψ`.
      set Ψ : C(↥I, ℝ) := ⟨fun t => (t : ℝ) ^ (k + 1) * iteratedDeriv (k + 1) g (lam * (t : ℝ) + b),
        by have := hg.continuous_iteratedDeriv (k + 1) (by exact_mod_cast le_top); fun_prop⟩ with hΨ
      -- A uniform bound `M ≥ 1` on `|t|` for `t ∈ I`.
      obtain ⟨M, hM1, hMbd⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ↥I, |(t : ℝ)| ≤ M := by
        obtain ⟨C, hC⟩ := (isCompact_range (f := fun t : ↥I => |(t : ℝ)|)
          (by fun_prop)).bddAbove
        refine ⟨max 1 C, le_max_left _ _, fun t => le_trans ?_ (le_max_right _ _)⟩
        exact hC ⟨t, rfl⟩
      -- A compact interval containing every segment endpoint `lam*t+b` and `(lam+s)*t+b`, |s|≤1.
      set R : ℝ := |lam| * M + |b| + M with hR
      have hRcont : ContinuousOn (deriv G) (Set.Icc (-R) R) := hG'cont.continuousOn
      have hUC : UniformContinuousOn (deriv G) (Set.Icc (-R) R) :=
        (isCompact_Icc).uniformContinuousOn_of_continuous hRcont
      -- The dilation/shift function from the inductive hypothesis, as a continuous map.
      set Φ : ℝ → C(↥I, ℝ) := fun s => ⟨fun t => (t : ℝ) ^ k * G (s * (t : ℝ) + b), by
        have := hg.continuous_iteratedDeriv k (by exact_mod_cast le_top); fun_prop⟩ with hΦ
      have hΦmem : ∀ s : ℝ, Φ s ∈ (Sg g I hg.continuous).topologicalClosure := fun s => ih s b
      -- Difference-quotient continuous map `D s` for `s ≠ 0`.
      set D : ℝ → C(↥I, ℝ) := fun s => s⁻¹ • (Φ (lam + s) - Φ lam) with hD
      have hDmem : ∀ s : ℝ, D s ∈ (Sg g I hg.continuous).topologicalClosure := by
        intro s
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hΦmem (lam + s)) (hΦmem lam))
      -- Pointwise value of `D s`.
      have hDval : ∀ (s : ℝ) (t : ↥I), D s t
          = (t : ℝ) ^ k * ((G ((lam + s) * (t : ℝ) + b) - G (lam * (t : ℝ) + b)) / s) := by
        intro s t
        simp only [hD, ContinuousMap.smul_apply, ContinuousMap.sub_apply, hΦ,
          ContinuousMap.coe_mk, smul_eq_mul]
        ring
      -- Pointwise value of `Ψ`, rewriting `g⁽ᵏ⁺¹⁾ = (g⁽ᵏ⁾)' = G'`.
      have hΨval : ∀ t : ↥I, Ψ t = (t : ℝ) ^ k * ((t : ℝ) * deriv G (lam * (t : ℝ) + b)) := by
        intro t
        simp only [hΨ, ContinuousMap.coe_mk, hGdef]
        rw [show iteratedDeriv (k + 1) g = deriv (iteratedDeriv k g) from iteratedDeriv_succ]
        ring
      -- The core uniform bound: `dist (D s) Ψ ≤ ε` for small enough `|s|`.
      have key : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : ℝ, 0 < |s| → |s| ≤ δ →
          dist (D s) Ψ ≤ ε := by
        intro ε hε
        -- Uniform continuity gives `δ₀` for the error tolerance `ε / M^(k+1)`.
        have hMk : (0:ℝ) < M ^ (k + 1) := by positivity
        set ε' : ℝ := ε / M ^ (k + 1) with hε'
        have hε'pos : 0 < ε' := by positivity
        obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
          (Metric.uniformContinuousOn_iff_le.mp hUC) ε' hε'pos
        -- Choose `δ = min (δ₀ / M) 1`, so that `|s| ≤ δ` controls both segment diameter and region.
        refine ⟨min (δ₀ / M) 1, by positivity, ?_⟩
        intro s hs0 hsδ
        have hsM : |s| ≤ 1 := le_trans hsδ (min_le_right _ _)
        have hsδ₀ : |s| * M ≤ δ₀ := by
          have : |s| ≤ δ₀ / M := le_trans hsδ (min_le_left _ _)
          calc |s| * M ≤ (δ₀ / M) * M := by gcongr
            _ = δ₀ := by field_simp
        rw [ContinuousMap.dist_le hε.le]
        intro t
        -- pointwise: write `u = lam*t+b`, `h = s*t`.
        set tv : ℝ := (t : ℝ) with htv
        set u : ℝ := lam * tv + b with hu
        have htvM : |tv| ≤ M := hMbd t
        -- segment endpoints in the region.
        have huabs : |u| ≤ |lam| * M + |b| := by
          calc |u| = |lam * tv + b| := by rw [hu]
            _ ≤ |lam * tv| + |b| := abs_add_le _ _
            _ = |lam| * |tv| + |b| := by rw [abs_mul]
            _ ≤ |lam| * M + |b| := by gcongr
        have hu_mem : u ∈ Set.Icc (-R) R := by
          rw [Set.mem_Icc, hR]
          rw [abs_le] at huabs
          constructor <;> [linarith [huabs.1]; linarith [huabs.2]]
        have huhabs : |u + s * tv| ≤ R := by
          calc |u + s * tv| ≤ |u| + |s * tv| := abs_add_le _ _
            _ = |u| + |s| * |tv| := by rw [abs_mul]
            _ ≤ (|lam| * M + |b|) + 1 * M := by gcongr
            _ = R := by rw [hR]; ring
        have huh : u + s * tv ∈ Set.Icc (-R) R := by
          rw [Set.mem_Icc]; rw [abs_le] at huhabs
          exact ⟨by linarith [huhabs.1], huhabs.2⟩
        have hseg_mem : ∀ x ∈ segment ℝ u (u + s * tv), x ∈ Set.Icc (-R) R :=
          fun x hx => (convex_Icc (-R) R).segment_subset hu_mem huh hx
        -- Apply the per-point Taylor bound with tolerance `ε'`.
        have hsegbound : ∀ x ∈ segment ℝ u (u + s * tv), |deriv G x - deriv G u| ≤ ε' := by
          intro x hx
          have hxIcc := hseg_mem x hx
          -- `x` lies in segment, so `|x-u| ≤ |(u+s tv)-u| = |s tv|`.
          have hxu : |x - u| ≤ |s * tv| := by
            obtain ⟨a, c, ha, hc, hac, rfl⟩ := hx
            have hxsub : a • u + c • (u + s * tv) - u = c * (s * tv) := by
              simp only [smul_eq_mul]; linear_combination u * hac
            rw [hxsub, abs_mul]
            calc |c| * |s * tv| ≤ 1 * |s * tv| := by
                  gcongr; rw [abs_of_nonneg hc]; linarith [hac]
              _ = |s * tv| := one_mul _
          have hdist : dist x u ≤ δ₀ := by
            calc dist x u = |x - u| := Real.dist_eq x u
              _ ≤ |s * tv| := hxu
              _ = |s| * |tv| := by rw [abs_mul]
              _ ≤ |s| * M := by gcongr
              _ ≤ δ₀ := hsδ₀
          have hduc := hδ₀ x hxIcc u hu_mem hdist
          rwa [Real.dist_eq] at hduc
        have htaylor := taylor_seg_bound hGdiff u (s * tv) ε' hsegbound
        -- Convert to a bound on the difference quotient.
        -- `|(G(u+s tv)-G u)/s - tv * G' u| ≤ ε' * |tv|`.
        have hquot : |(G (u + s * tv) - G u) / s - tv * deriv G u| ≤ ε' * |tv| := by
          have hs0' : s ≠ 0 := by
            intro h; rw [h, abs_zero] at hs0; exact lt_irrefl 0 hs0
          have : (G (u + s * tv) - G u) / s - tv * deriv G u
              = (G (u + s * tv) - G u - (s * tv) * deriv G u) / s := by
            field_simp
          rw [this, abs_div]
          rw [div_le_iff₀ (by positivity)]
          calc |G (u + s * tv) - G u - s * tv * deriv G u|
              ≤ ε' * |s * tv| := htaylor
            _ = ε' * (|s| * |tv|) := by rw [abs_mul]
            _ = ε' * |tv| * |s| := by ring
        -- Multiply through by `t^k` and bound by `ε`.
        rw [Real.dist_eq, hDval s t, hΨval t]
        -- restate using `tv`, `u`.
        rw [show ((lam + s) * (t : ℝ) + b) = u + s * tv by rw [hu, htv]; ring,
            show (lam * (t : ℝ) + b) = u by rw [hu, htv]]
        have hstep : |(t : ℝ) ^ k * ((G (u + s * tv) - G u) / s)
            - (t : ℝ) ^ k * (tv * deriv G u)|
            ≤ |tv| ^ k * (ε' * |tv|) := by
          rw [← mul_sub, abs_mul]
          have : |(t : ℝ) ^ k| = |tv| ^ k := by rw [htv, abs_pow]
          rw [this]
          gcongr
        calc |(t : ℝ) ^ k * ((G (u + s * tv) - G u) / s) - (t : ℝ) ^ k * (tv * deriv G u)|
            ≤ |tv| ^ k * (ε' * |tv|) := hstep
          _ = ε' * (|tv| ^ k * |tv|) := by ring
          _ = ε' * |tv| ^ (k + 1) := by rw [pow_succ]
          _ ≤ ε' * M ^ (k + 1) := by gcongr
          _ = ε := by rw [hε']; field_simp
      -- Conclude: `Ψ` is a limit of `D (1/(n+1)) ∈ closure`, and the closure is closed.
      have hclosed : IsClosed ((Sg g I hg.continuous).topologicalClosure : Set C(↥I, ℝ)) :=
        (Sg g I hg.continuous).isClosed_topologicalClosure
      have htend : Filter.Tendsto (fun n : ℕ => D (1 / ((n : ℝ) + 1))) Filter.atTop (𝓝 Ψ) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨δ, hδpos, hδ⟩ := key (ε / 2) (by positivity)
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
        refine ⟨N, fun n hn => ?_⟩
        have hspos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        have hsle : (1 : ℝ) / ((n : ℝ) + 1) ≤ δ := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hδpos] at hN
          have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [hN, hNn]
        have hb := hδ (1 / ((n : ℝ) + 1)) (by rwa [abs_of_pos hspos]) (by rwa [abs_of_pos hspos])
        have hb2 : dist (D (1 / ((n : ℝ) + 1))) Ψ ≤ ε / 2 := hb
        linarith
      have hev : ∀ᶠ n : ℕ in Filter.atTop, (fun n : ℕ => D (1 / ((n : ℝ) + 1))) n
          ∈ ((Sg g I hg.continuous).topologicalClosure : Set C(↥I, ℝ)) :=
        Filter.Eventually.of_forall (fun n => hDmem _)
      exact hclosed.mem_of_tendsto htend hev

/-- B2. A smooth non(everywhere-)polynomial has, for every order `k`, a point where the
`k`-th derivative is nonzero. This is the contrapositive of
`iteratedDeriv_eq_zero_imp_poly`: if `g⁽ᵏ⁾` vanished everywhere, `g` would be a polynomial. -/
theorem exists_deriv_ne {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hnp : ¬ IsPolynomialFun g) (k : ℕ) : ∃ b, iteratedDeriv k g b ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp, _⟩ :=
    iteratedDeriv_eq_zero_imp_poly (f := g) (n := k) (hg.of_le (by exact_mod_cast le_top)) h
  exact hnp ⟨p, funext hp⟩

/-- B3 (glue). For smooth non-polynomial `g`, the closed span of its dilations/translations is all
of `C(I,ℝ)` on every compact set `I`. -/
theorem smooth_engine {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hnp : ¬ IsPolynomialFun g)
    (I : Set ℝ) (hI : IsCompact I) :
    (Sg g I hg.continuous).topologicalClosure = ⊤ := by
  haveI : CompactSpace (↥I) := isCompact_iff_compactSpace.mp hI
  set C := (Sg g I hg.continuous).topologicalClosure with hC
  -- Step 1+2: every monomial `t ↦ tᵏ` lies in the closure `C`.
  have hmono : ∀ k : ℕ, (⟨fun t => (t : ℝ) ^ k, by fun_prop⟩ : C(↥I, ℝ)) ∈ C := by
    intro k
    obtain ⟨b, hb⟩ := exists_deriv_ne hg hnp k
    have hmem := deriv_pow_mem hg I hI k 0 b
    -- the generator `t ↦ tᵏ · g⁽ᵏ⁾(0·t+b) = (g⁽ᵏ⁾ b) • (t ↦ tᵏ)`.
    have hsmul : (⟨fun t => (t : ℝ) ^ k * iteratedDeriv k g (0 * (t : ℝ) + b), by
          have := hg.continuous_iteratedDeriv k (by exact_mod_cast le_top); fun_prop⟩ : C(↥I, ℝ))
        = iteratedDeriv k g b • (⟨fun t => (t : ℝ) ^ k, by fun_prop⟩ : C(↥I, ℝ)) := by
      ext t
      simp [mul_comm]
    rw [hsmul] at hmem
    have := C.smul_mem (iteratedDeriv k g b)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this
  -- Step 3: every polynomial function lies in `C` (by polynomial induction, `C` a submodule).
  have hpoly : ∀ p : Polynomial ℝ, p.toContinuousMapOn I ∈ C := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        have : (p + q).toContinuousMapOn I = p.toContinuousMapOn I + q.toContinuousMapOn I := by
          ext t; simp
        rw [this]; exact C.add_mem hp hq
    | monomial n a =>
        have : (Polynomial.monomial n a).toContinuousMapOn I
            = a • (⟨fun t => (t : ℝ) ^ n, by fun_prop⟩ : C(↥I, ℝ)) := by
          ext t; simp
        rw [this]; exact C.smul_mem a (hmono n)
  -- Step 4: polynomial functions are dense (Stone–Weierstrass); `C` is closed and contains them.
  -- It suffices that `C` (as a set) is all of `C(↥I,ℝ)`.
  rw [eq_top_iff]
  intro f _
  -- Polynomial functions are a dense subset, and `C` is a closed superset, so `C` contains `f`.
  have hSW : closure (polynomialFunctions I : Set C(↥I, ℝ)) = Set.univ := by
    have := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (polynomialFunctions I) (polynomialFunctions_separatesPoints I)
    have h2 := congrArg (fun s : Subalgebra ℝ C(↥I, ℝ) => (s : Set C(↥I, ℝ))) this
    rwa [Subalgebra.topologicalClosure_coe, Algebra.coe_top] at h2
  have hsub : (polynomialFunctions I : Set C(↥I, ℝ)) ⊆ (C : Set C(↥I, ℝ)) := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p, rfl⟩
    exact hpoly p
  have hclosed : closure (polynomialFunctions I : Set C(↥I, ℝ)) ⊆ (C : Set C(↥I, ℝ)) :=
    closure_minimal hsub (Sg g I hg.continuous).isClosed_topologicalClosure
  have : f ∈ (C : Set C(↥I, ℝ)) := hclosed (by rw [hSW]; trivial)
  exact this

end UniversalApproximation.Leshno
