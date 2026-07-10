/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
import Mathlib.Tactic
import NeuralNetworkProofs.UniversalApproximation.Monotone.Approximation
import NeuralNetworkProofs.UniversalApproximation.Runje.Defs
import NeuralNetworkProofs.UniversalApproximation.Runje.PartitionOfUnity
import NeuralNetworkProofs.UniversalApproximation.Runje.JointTarget
import NeuralNetworkProofs.UniversalApproximation.Runje.Embedding

/-!
# Partial-monotone universal approximation (Runje et al.)

Every jointly continuous `f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ` that is coordinatewise
monotone in its second (monotone) block on the unit cube is uniformly approximated by a
`PartMonoNet`: an unconstrained single-hidden-layer Leshno embedding of the non-monotone block,
clamped and concatenated with the monotone block, fed to a monotone network.

The proof follows Runje et al.: with a boundedness constant `C` and a joint uniform-continuity
modulus `δ`, choose a grid of resolution `m` with `1/m < δ`, sample `f` at the grid nodes to
build the jointly-monotone target `jointTarget g C`, apply Mikulincer–Reichman's
`monotone_approximation` to it, and realize the tent partition of unity through Leshno's
`exists_vector_embedding`.  A three-term triangle inequality (monotone-network error, embedding
error, and partition-of-unity collapse) closes the bound.

* `partial_monotone_approximation` — the headline.
-/

namespace UniversalApproximation.Runje

open UniversalApproximation.Monotone UniversalApproximation.Leshno

/-- Appending two cube points gives a cube point of the concatenated dimension. -/
private lemma append_mem_cube {N dm : ℕ} {z : Fin N → ℝ} {x : Fin dm → ℝ}
    (hz : z ∈ Set.Icc (0 : Fin N → ℝ) 1) (hx : x ∈ Set.Icc (0 : Fin dm → ℝ) 1) :
    Fin.append z x ∈ Set.Icc (0 : Fin (N + dm) → ℝ) 1 := by
  rw [Set.mem_Icc]
  refine ⟨fun k => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [Pi.zero_apply, Fin.append_left] using hz.1 i
    · simpa only [Pi.zero_apply, Fin.append_right] using hx.1 j
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa only [Pi.one_apply, Fin.append_left] using hz.2 i
    · simpa only [Pi.one_apply, Fin.append_right] using hx.2 j

theorem partial_monotone_approximation {df dm : ℕ}
    (σ : ℝ → ℝ) (hσ : ClassM σ) (hnp : ¬ IsAEPolynomial σ)
    (f : (Fin df → ℝ) → (Fin dm → ℝ) → ℝ)
    (hf : ContinuousOn (fun p => f p.1 p.2)
            (Set.Icc (0 : Fin df → ℝ) 1 ×ˢ Set.Icc (0 : Fin dm → ℝ) 1))
    (hmono : ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1,
        ∀ ⦃x y⦄, x ∈ Set.Icc (0 : Fin dm → ℝ) 1 → y ∈ Set.Icc (0 : Fin dm → ℝ) 1 →
          x ≤ y → f u x ≤ f u y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : PartMonoNet df dm, P.mono.IsMonotone ∧
      (∀ i, (fun u => P.emb u i) ∈ genSpanPi σ df) ∧
      ∀ u ∈ Set.Icc (0 : Fin df → ℝ) 1, ∀ x ∈ Set.Icc (0 : Fin dm → ℝ) 1,
        |P.toFun u x - f u x| ≤ ε := by
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- the two cubes and their compact product
  set cubeF := Set.Icc (0 : Fin df → ℝ) 1 with hcubeF
  set cubeM := Set.Icc (0 : Fin dm → ℝ) 1 with hcubeM
  have hKf : IsCompact cubeF := isCompact_Icc
  have hKfne : cubeF.Nonempty := Set.nonempty_Icc.mpr fun _ => zero_le_one
  have hKmne : cubeM.Nonempty := Set.nonempty_Icc.mpr fun _ => zero_le_one
  set cubeP := cubeF ×ˢ cubeM with hcubeP
  have hK : IsCompact cubeP := hKf.prod isCompact_Icc
  have hPne : cubeP.Nonempty := hKfne.prod hKmne
  -- boundedness constant `C`
  obtain ⟨p0, -, hp0max⟩ := hK.exists_isMaxOn hPne hf.abs
  have hp0 : ∀ q ∈ cubeP, |f q.1 q.2| ≤ |f p0.1 p0.2| := isMaxOn_iff.mp hp0max
  obtain ⟨M0, hM0nonneg, hbound⟩ :
      ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ u ∈ cubeF, ∀ x ∈ cubeM, |f u x| ≤ M0 :=
    ⟨|f p0.1 p0.2|, abs_nonneg _,
      fun u hu x hx => hp0 (u, x) (Set.mem_prod.mpr ⟨hu, hx⟩)⟩
  set C := M0 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith
  -- joint uniform continuity
  have hunif : ∀ ε' > 0, ∃ δ > 0, ∀ u ∈ cubeF, ∀ u' ∈ cubeF, ∀ x ∈ cubeM,
      dist u u' ≤ δ → |f u x - f u' x| ≤ ε' := by
    intro ε' hε'
    have huc : UniformContinuousOn (fun p => f p.1 p.2) cubeP :=
      hK.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hδ'⟩ := huc ε' hε'
    refine ⟨δ / 2, by positivity, fun u hu u' hu' x hx hle => ?_⟩
    have hpmem : ((u, x) : (Fin df → ℝ) × (Fin dm → ℝ)) ∈ cubeP := Set.mem_prod.mpr ⟨hu, hx⟩
    have hqmem : ((u', x) : (Fin df → ℝ) × (Fin dm → ℝ)) ∈ cubeP := Set.mem_prod.mpr ⟨hu', hx⟩
    have hdd : dist ((u, x) : (Fin df → ℝ) × (Fin dm → ℝ)) (u', x) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; linarith
    have hfd := hδ' (u, x) hpmem (u', x) hqmem hdd
    rw [Real.dist_eq] at hfd
    exact le_of_lt hfd
  obtain ⟨δ, hδ, hdunif⟩ := hunif (ε / 3) hε3
  -- grid resolution `m` with `1/m < δ`
  obtain ⟨m0, hm0⟩ := exists_nat_one_div_lt hδ
  set m := m0 + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hmδ : 1 / (m : ℝ) < δ := by
    have hcast : (m : ℝ) = (m0 : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    rw [hcast]; exact hm0
  -- reindex the multi-index grid `Fin df → Fin (m+1)` to `Fin embWidth`
  set embWidth := Fintype.card (Fin df → Fin (m + 1)) with hembdef
  have hembpos : 0 < embWidth := by
    rw [hembdef]; exact Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hembR : (0 : ℝ) < embWidth := by exact_mod_cast hembpos
  let eN : (Fin df → Fin (m + 1)) ≃ Fin embWidth := Fintype.equivFin _
  have hg_node_mem : ∀ i, tentNode m (eN.symm i) ∈ cubeF :=
    fun i => tentNode_mem_Icc m (eN.symm i)
  -- the grid-sampled, nonnegative, monotone-in-`x` targets `g`
  set g : Fin embWidth → (Fin dm → ℝ) → ℝ :=
    fun i x => f (tentNode m (eN.symm i)) x + C with hg
  have hg_nonneg : ∀ i, ∀ x ∈ cubeM, 0 ≤ g i x := by
    intro i x hx
    have hb := hbound (tentNode m (eN.symm i)) (hg_node_mem i) x hx
    rw [abs_le] at hb
    simp only [hg]; linarith [hb.1]
  have hg_mono : ∀ i, ∀ ⦃x y⦄, x ∈ cubeM → y ∈ cubeM → x ≤ y → g i x ≤ g i y := by
    intro i x y hx hy hxy
    simp only [hg]
    have := hmono (tentNode m (eN.symm i)) (hg_node_mem i) hx hy hxy
    linarith
  have hg_cont : ∀ i, ContinuousOn (g i) cubeM := by
    intro i
    simp only [hg]
    have hpc : Continuous fun x : Fin dm → ℝ =>
        ((tentNode m (eN.symm i), x) : (Fin df → ℝ) × (Fin dm → ℝ)) := by fun_prop
    have hmaps : Set.MapsTo
        (fun x : Fin dm → ℝ => ((tentNode m (eN.symm i), x) : (Fin df → ℝ) × (Fin dm → ℝ)))
        cubeM cubeP := fun x hx => Set.mem_prod.mpr ⟨hg_node_mem i, hx⟩
    exact (hf.comp hpc.continuousOn hmaps).add continuousOn_const
  -- the monotone network approximating `jointTarget g C`
  obtain ⟨Mnet, hM_mono, -, hM_approx⟩ :=
    monotone_approximation (jointTarget g C)
      (jointTarget_continuousOn g C hg_cont)
      (jointTarget_mono g C hg_nonneg hg_mono) hε3
  -- the Leshno embedding realizing the tent partition of unity
  have hden : (0 : ℝ) < 3 * embWidth * (2 * C) :=
    mul_pos (mul_pos (by norm_num) hembR) (by linarith)
  set η := ε / (3 * embWidth * (2 * C)) with hηdef
  have hηpos : 0 < η := div_pos hε hden
  have hΨ_cont : ∀ i, ContinuousOn (fun u => psi m (eN.symm i) u) cubeF :=
    fun i => psi_continuousOn hm (eN.symm i)
  obtain ⟨φ, hφmem, hφε⟩ :=
    exists_vector_embedding (leshno_dense hσ hnp) hKf
      (fun i u => psi m (eN.symm i) u) hΨ_cont hηpos
  -- assemble the partial-monotone network and prove the uniform bound
  refine ⟨⟨embWidth, fun u i => φ i u, Mnet⟩, hM_mono, fun i => hφmem i, ?_⟩
  intro u hu x hx
  set z : Fin embWidth → ℝ := fun i => clamp01 (φ i u) with hz
  set zΨ : Fin embWidth → ℝ := fun i => psi m (eN.symm i) u with hzΨ
  have htoFun : (⟨embWidth, fun u i => φ i u, Mnet⟩ : PartMonoNet df dm).toFun u x
      = Mnet.toFun (Fin.append z x) := rfl
  rw [htoFun]
  have hz_mem : z ∈ Set.Icc (0 : Fin embWidth → ℝ) 1 := by
    rw [Set.mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [hz, Pi.zero_apply]; exact clamp01_nonneg _
    · simp only [hz, Pi.one_apply]; exact clamp01_le_one _
  have hzΨ_mem : zΨ ∈ Set.Icc (0 : Fin embWidth → ℝ) 1 := by
    rw [Set.mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [hzΨ, Pi.zero_apply]; exact psi_nonneg m (eN.symm i) u
    · simp only [hzΨ, Pi.one_apply]; exact psi_le_one hm (eN.symm i) hu
  have hazx : Fin.append z x ∈ Set.Icc (0 : Fin (embWidth + dm) → ℝ) 1 :=
    append_mem_cube hz_mem hx
  have hazΨx : Fin.append zΨ x ∈ Set.Icc (0 : Fin (embWidth + dm) → ℝ) 1 :=
    append_mem_cube hzΨ_mem hx
  have hsum1 : (∑ i, psi m (eN.symm i) u) = 1 :=
    (Equiv.sum_comp eN.symm fun k => psi m k u).trans (sum_psi_eq_one hm hu)
  have hgbound : ∀ i, |g i x| ≤ 2 * C := by
    intro i
    have hb := hbound (tentNode m (eN.symm i)) (hg_node_mem i) x hx
    rw [abs_le] at hb
    rw [abs_le]; simp only [hg]
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- Term A: monotone-network approximation error
  have hA : |Mnet.toFun (Fin.append z x) - jointTarget g C (Fin.append z x)| ≤ ε / 3 :=
    hM_approx (Fin.append z x) hazx
  -- Term B: embedding error, weighted by the target magnitude
  have hB : |jointTarget g C (Fin.append z x) - jointTarget g C (Fin.append zΨ x)| ≤ ε / 3 := by
    refine (jointTarget_diff_bound g C z zΨ x).trans ?_
    have hterm : ∀ i, |z i - zΨ i| * |g i x| ≤ η * (2 * C) := by
      intro i
      refine mul_le_mul ?_ (hgbound i) (abs_nonneg _) hηpos.le
      have hpsi_mem : psi m (eN.symm i) u ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨psi_nonneg m (eN.symm i) u, psi_le_one hm (eN.symm i) hu⟩
      have h1 : z i - zΨ i = clamp01 (φ i u) - clamp01 (psi m (eN.symm i) u) := by
        simp only [hz, hzΨ, clamp01_eq_self hpsi_mem]
      rw [h1]
      refine (abs_clamp01_sub_le _ _).trans ?_
      rw [abs_sub_comm]; exact (hφε i u hu).le
    calc ∑ i, |z i - zΨ i| * |g i x|
        ≤ ∑ _i : Fin embWidth, η * (2 * C) := Finset.sum_le_sum fun i _ => hterm i
      _ = embWidth * (η * (2 * C)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ε / 3 := by rw [hηdef]; field_simp
  -- Term C: partition-of-unity collapse via uniform continuity
  have hFzΨ : jointTarget g C (Fin.append zΨ x)
      = ∑ i, psi m (eN.symm i) u * f (tentNode m (eN.symm i)) x := by
    have e1 : (∑ i, psi m (eN.symm i) u * g i x)
        = (∑ i, psi m (eN.symm i) u * f (tentNode m (eN.symm i)) x) + C := by
      have hpt : ∀ i, psi m (eN.symm i) u * g i x
          = psi m (eN.symm i) u * f (tentNode m (eN.symm i)) x + psi m (eN.symm i) u * C := by
        intro i; simp only [hg]; ring
      rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, ← Finset.sum_mul,
        hsum1, one_mul]
    simp only [jointTarget, zpart_append, xpart_append, hzΨ]
    rw [e1]; ring
  have hC_term : |jointTarget g C (Fin.append zΨ x) - f u x| ≤ ε / 3 := by
    rw [hFzΨ]
    have hfux : (∑ i, psi m (eN.symm i) u * f u x) = f u x := by
      rw [← Finset.sum_mul, hsum1, one_mul]
    rw [← hfux, ← Finset.sum_sub_distrib]
    calc |∑ i, (psi m (eN.symm i) u * f (tentNode m (eN.symm i)) x
            - psi m (eN.symm i) u * f u x)|
        ≤ ∑ i, |psi m (eN.symm i) u * f (tentNode m (eN.symm i)) x
            - psi m (eN.symm i) u * f u x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, psi m (eN.symm i) u * (ε / 3) := Finset.sum_le_sum fun i _ => ?_
      _ = ε / 3 := by rw [← Finset.sum_mul, hsum1, one_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg (psi_nonneg m (eN.symm i) u)]
    rcases eq_or_ne (psi m (eN.symm i) u) 0 with h0 | h0
    · rw [h0]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (psi_nonneg m (eN.symm i) u)
      exact hdunif (tentNode m (eN.symm i)) (hg_node_mem i) u hu x hx
        (le_trans (psi_support hm (eN.symm i) h0) hmδ.le)
  -- combine the three terms via the triangle inequality
  have t1 := abs_sub_le (Mnet.toFun (Fin.append z x))
    (jointTarget g C (Fin.append zΨ x)) (f u x)
  have t2 := abs_sub_le (Mnet.toFun (Fin.append z x)) (jointTarget g C (Fin.append z x))
    (jointTarget g C (Fin.append zΨ x))
  linarith [hA, hB, hC_term, t1, t2]

end UniversalApproximation.Runje
