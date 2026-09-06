/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.BlockPlan

/-!
# Correctness and budget of the block algorithm (Theorem 7, upper bound)

* `BlockParam.regret_le`: if every block estimate is within `ε/4` of the norm of the block and
  the empirical mean vector of the second phase is within `ε/4` of `θ^(î)`, the simple regret
  of the recommendation is at most `ε` (blueprint `lem:block_selection` and the correctness
  part of `thm:separation`).
* `BlockParam.one_sub_le_seedMeasure_real_output`: on the seed space, the recommendation has
  simple regret at most `ε` with probability at least `1 - δ` (`7δ/16` for the norm estimates,
  by the accuracy of the meta-algorithm on each block and a union bound, `δ/2` for the second
  phase, by the chi-square tail bound).
* `BlockParam.T_le`: the budget is at most `2·10⁶ (kd log(8k/δ) + d²) / ε²`.
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- The regret of the normalized estimate `v / ‖v‖` of a direction `ϑ` is at most `2 ‖v - ϑ‖`. -/
lemma norm_sub_inner_normalizeBall_le (ϑ v : EuclideanSpace ℝ ι) :
    ‖ϑ‖ - ⟪(normalizeBall v : EuclideanSpace ℝ ι), ϑ⟫ ≤ 2 * ‖v - ϑ‖ := by
  rw [coe_normalizeBall]
  have h3 : ‖ϑ‖ ≤ ‖v‖ + ‖v - ϑ‖ := by
    have := norm_sub_le v (v - ϑ)
    rwa [sub_sub_cancel] at this
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [norm_zero, inv_zero, zero_smul, inner_zero_left, sub_zero, zero_sub, norm_neg]
    linarith [norm_nonneg ϑ]
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    rw [real_inner_smul_left]
    have h1 : ⟪v, ϑ⟫ = ‖v‖ ^ 2 - ⟪v, v - ϑ⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    have h2 : ⟪v, v - ϑ⟫ ≤ ‖v‖ * ‖v - ϑ‖ := real_inner_le_norm _ _
    have h4 : ‖v‖ - ‖v - ϑ‖ ≤ ‖v‖⁻¹ * ⟪v, ϑ⟫ := by
      rw [h1, ← sub_nonneg]
      have : ‖v‖⁻¹ * (‖v‖ ^ 2 - ⟪v, v - ϑ⟫) - (‖v‖ - ‖v - ϑ‖)
          = ‖v‖⁻¹ * (‖v‖ * ‖v - ϑ‖ - ⟪v, v - ϑ⟫) := by
        field_simp
        ring
      rw [this]
      exact mul_nonneg (inv_nonneg.2 hn.le) (by linarith)
    linarith

/-- **Chi-square tail for the noise average of a basis window**: if `2 d + 12 log(1/δ') ≤ n c²`
then `‖Δ‖ > c` with probability at most `δ'`. -/
lemma lnNoise_real_norm_lnDelta_gt_le {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : 0 < n) {δ' : ℝ}
    (hδ : δ' ∈ Set.Ioo 0 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 2 * d + 12 * log (1 / δ') ≤ n * c ^ 2) :
    (lnNoise (Fin d) n).real {e | c < ‖lnDelta n e‖} ≤ δ' := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hn' : (0 : ℝ) < n := by positivity
  have hlaw := hasLaw_lnG (ι := Fin d) hn
  -- `‖Δ‖² = (∑ g_i²) / n`
  have hnorm : ∀ e : Fin d → Fin n → ℝ, ‖lnDelta n e‖ ^ 2 = (1 / n) * ∑ i, lnG n e i ^ 2 := by
    intro e
    have h := norm_lnDelta_sq_sub_eq (ι := Fin d) hn e
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    field_simp
    ring
  have hsub : {e : Fin d → Fin n → ℝ | c < ‖lnDelta n e‖}
      ⊆ lnG n ⁻¹' {g : Fin d → ℝ | 2 * d + 12 * log (1 / δ') ≤ ∑ i, g i ^ 2} := by
    intro e he
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at he ⊢
    have h1 : c ^ 2 < ‖lnDelta n e‖ ^ 2 := by gcongr
    rw [hnorm e] at h1
    have h2 : n * c ^ 2 < ∑ i, lnG n e i ^ 2 := by
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hn'] at h1
      linarith
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hS : MeasurableSet {g : Fin d → ℝ | 2 * d + 12 * log (1 / δ') ≤ ∑ i, g i ^ 2} :=
    measurableSet_le measurable_const
      (Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).pow_const 2)
  rw [measureReal_def, ← Measure.map_apply_of_aemeasurable hlaw.aemeasurable hS, hlaw.map_eq,
    ← measureReal_def]
  have hstd := measureReal_norm_sq_ge_le_stdGaussian (ι := Fin d) hδ
  rw [← map_pi_eq_stdGaussian, measureReal_def,
    Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
      (measurableSet_le measurable_const (measurable_norm.pow_const 2)), ← measureReal_def] at hstd
  have hset : (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹'
      {v | 2 * (Fintype.card (Fin d)) + 12 * log (1 / δ') ≤ ‖v‖ ^ 2}
      = {g | 2 * d + 12 * log (1 / δ') ≤ ∑ i, g i ^ 2} := by
    ext g
    simp [EuclideanSpace.real_norm_sq_eq]
  rwa [hset] at hstd

namespace BlockParam

variable {d : ℕ} (Q : BlockParam)

/-- **Deterministic correctness**: if every block estimate is within `ε/4` of the norm of the
block and the empirical mean vector is within `ε/4` of `θ^(î)`, the recommendation has simple
regret at most `ε` (blueprint `lem:block_selection` and `thm:separation`). -/
lemma regret_le (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (y : ℕ → ℝ)
    (hest : ∀ i : Fin Q.k, |Q.estN d i y - ‖blockProj i θ‖| ≤ Q.ε / 4)
    (hΔ : ‖Q.thetaHat d y - blockProj (Q.iHat d y) θ‖ ≤ Q.ε / 4) :
    simpleRegret (blockBallSet Q.k d) θ (Q.recommend d y) ≤ Q.ε := by
  have : Nonempty (Fin Q.k) := ⟨⟨0, Q.hk⟩⟩
  change supportFn (blockBallSet Q.k d) θ
    - ⟪(Q.recommend d y : EuclideanSpace ℝ (Fin Q.k × Fin d)), θ⟫ ≤ Q.ε
  rw [supportFn_blockBallSet, recommend, coe_blockEmbBall, inner_blockEmb_left]
  have h1 : (⨆ i, ‖blockProj i θ‖) ≤ ‖blockProj (Q.iHat d y) θ‖ + Q.ε / 2 := by
    refine ciSup_le fun i ↦ ?_
    have := abs_le.1 (hest i)
    have := abs_le.1 (hest (Q.iHat d y))
    have := Q.estN_le_iHat (d := d) y i
    linarith
  have h2 := norm_sub_inner_normalizeBall_le (blockProj (Q.iHat d y) θ) (Q.thetaHat d y)
  linarith

/-- **Correctness of the block algorithm** on the seed space, in the form required by the seeded
PAC guarantee: the recommendation has simple regret at most `ε` with probability at least
`1 - δ`. -/
theorem one_sub_le_seedMeasure_real_output (hd : 0 < d) (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) :
    1 - Q.δ ≤ ((Q.alg d).seedMeasure (gaussianReal 0 1)).real
      {ω | simpleRegret (blockBallSet Q.k d) θ (Q.output d ((Q.alg d).seedFinHist
        (fun (x : blockBallSet Q.k d) (e : ℝ) ↦
          inner ℝ (x : EuclideanSpace ℝ (Fin Q.k × Fin d)) θ + e) (Q.T d) ω)) ≤ Q.ε} := by
  have hd' : 0 < Fintype.card (Fin d) := by simpa using hd
  have hε0 := Q.hε.1
  have hδ0 := Q.hδ.1
  have hδ1 := Q.hδ.2
  have hε' : Q.ε ≠ 0 := hε0.ne'
  have hk : (1 : ℝ) ≤ Q.k := Nat.one_le_cast.2 Q.hk
  have hout : ∀ ω, Q.output d ((Q.alg d).seedFinHist
      (fun (x : blockBallSet Q.k d) (e : ℝ) ↦
        inner ℝ (x : EuclideanSpace ℝ (Fin Q.k × Fin d)) θ + e) (Q.T d) ω)
      = Q.recommend d (Q.yω θ ω) := fun ω ↦ Q.recommend_yOf_seedFinHist θ ω
  simp_rw [hout]
  change 1 - Q.δ ≤ (nsMeasure (Fin d)).real _
  -- the failure events: some norm estimate is off by more than `ε/4`, or the noise average of
  -- the basis window has norm more than `ε/4`
  set S : Fin Q.k → Set (ℕ → (Fin d → Bool) × ℝ) := fun i ↦
    {ω' | Q.P.ε < |Q.P.estimate (Fin d) (Q.P.yω (blockProj i θ) ω') - ‖blockProj i θ‖|} with hS_def
  have hS : ∀ i, MeasurableSet (S i) := fun i ↦ measurableSet_lt measurable_const
    (continuous_abs.measurable.comp
      (((Q.P.measurable_estimate).comp (Q.P.measurable_yω (blockProj i θ))).sub_const _))
  set E₁ : Set (ℕ → (Fin d → Bool) × ℝ) := ⋃ i : Fin Q.k, shiftSeq ((i : ℕ) * Q.N d) ⁻¹' S i
    with hE₁
  set S₂ : Set (Fin d → Fin (Q.n₂ d) → ℝ) := {e | Q.ε / 4 < ‖lnDelta (Q.n₂ d) e‖} with hS₂
  have hS₂m : MeasurableSet S₂ := measurableSet_lt measurable_const (measurable_lnDelta _).norm
  set E₂ : Set (ℕ → (Fin d → Bool) × ℝ) := lnProj (Q.T₂ d) (Q.n₂ d) ⁻¹' S₂ with hE₂
  have hE : MeasurableSet (E₁ ∪ E₂) :=
    (MeasurableSet.iUnion fun i : Fin Q.k ↦ (measurable_shiftSeq ((i : ℕ) * Q.N d)) (hS i)).union
      (measurable_lnProj hS₂m)
  -- outside the failure events, the recommendation is good
  have hgood : (E₁ ∪ E₂)ᶜ
      ⊆ {ω | simpleRegret (blockBallSet Q.k d) θ (Q.recommend d (Q.yω θ ω)) ≤ Q.ε} := by
    intro ω hω
    simp only [hE₁, hE₂, hS_def, hS₂, Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_iUnion,
      not_exists, Set.mem_preimage, Set.mem_ofPred_eq, not_lt] at hω
    refine Q.regret_le θ _ (fun i ↦ ?_) ?_
    · rw [Q.estN_eq hd θ ω i]
      exact hω.1 i
    · rw [Q.thetaHat_eq hd θ ω, add_sub_cancel_left]
      exact hω.2
  -- the probabilities of the failure events
  have h1 : (nsMeasure (Fin d)).real E₁ ≤ 7 * Q.δ / 16 := by
    refine (measureReal_iUnion_fintype_le fun i : Fin Q.k ↦
      shiftSeq ((i : ℕ) * Q.N d) ⁻¹' S i).trans ?_
    have hi : ∀ i : Fin Q.k, (nsMeasure (Fin d)).real (shiftSeq ((i : ℕ) * Q.N d) ⁻¹' S i)
        ≤ 7 * Q.P.δ / 8 := fun i ↦ by
      rw [nsMeasure_real_shiftSeq_preimage _ (hS i)]
      exact Q.P.nsMeasure_real_estimate_fail_le hd' (blockProj i θ)
    refine (Finset.sum_le_sum fun i _ ↦ hi i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, P_δ]
    field_simp
    ring
  have h2 : (nsMeasure (Fin d)).real E₂ ≤ Q.δ / 2 := by
    rw [hE₂, NormEstParam.nsMeasure_real_lnProj_preimage hS₂m]
    refine lnNoise_real_norm_lnDelta_gt_le hd Q.n₂_pos ⟨by positivity, by linarith⟩
      (by positivity) ?_
    have hceil : (4 * (8 * d + 48 * log (2 / Q.δ)) / Q.ε ^ 2 : ℝ) ≤ Q.n₂ d := Nat.le_ceil _
    rw [one_div_div]
    have hmul := mul_le_mul_of_nonneg_right hceil (sq_nonneg (Q.ε / 4))
    have e : (4 * (8 * d + 48 * log (2 / Q.δ)) / Q.ε ^ 2) * (Q.ε / 4) ^ 2
        = 2 * d + 12 * log (2 / Q.δ) := by
      field_simp
      ring
    linarith
  calc 1 - Q.δ ≤ 1 - (nsMeasure (Fin d)).real (E₁ ∪ E₂) := by
        have := measureReal_union_le (μ := nsMeasure (Fin d)) E₁ E₂
        linarith
    _ = (nsMeasure (Fin d)).real (E₁ ∪ E₂)ᶜ := (probReal_compl_eq_one_sub hE).symm
    _ ≤ _ := measureReal_mono hgood (measure_ne_top _ _)

/-- **Budget of the block algorithm**: `T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²`. -/
theorem T_le (hd : 0 < d) :
    (Q.T d : ℝ) ≤ 2000000 * (Q.k * d * log (8 * Q.k / Q.δ) + (d : ℝ) ^ 2) / Q.ε ^ 2 := by
  have hd' : 0 < Fintype.card (Fin d) := by simpa using hd
  have hε := Q.hε
  have hε0 := Q.hε.1
  have hδ := Q.hδ
  have hk : (1 : ℝ) ≤ Q.k := Nat.one_le_cast.2 Q.hk
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have hL2 : 0 ≤ log (2 / Q.δ) := Q.log_two_div_pos.le
  have hδ0 := Q.hδ.1
  have hL8 : log (2 / Q.δ) ≤ log (8 * Q.k / Q.δ) :=
    Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hδ0]; linarith)
  have hL80 : 0 ≤ log (8 * Q.k / Q.δ) := hL2.trans hL8
  -- phase 1: `k` runs of the meta-algorithm with parameters `(ε/4, δ/(2k))`
  have hN := Q.P.T_le hd'
  rw [Fintype.card_fin, P_ε, P_δ] at hN
  have hlog : log (4 / (Q.δ / (2 * Q.k))) = log (8 * Q.k / Q.δ) := by
    congr 1
    rw [div_div_eq_mul_div]
    ring
  rw [hlog] at hN
  have hN' : (Q.N d : ℝ) ≤ 1600000 * d * log (8 * Q.k / Q.δ) / Q.ε ^ 2 := by
    refine hN.trans (le_of_eq ?_)
    field_simp
    ring
  -- phase 2: `d n₂` rounds
  have hn2 : (Q.n₂ d : ℝ) < 4 * (8 * d + 48 * log (2 / Q.δ)) / Q.ε ^ 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (by positivity) (mul_nonneg (by norm_num) hL2))) (sq_nonneg _))
  have hε1 := Q.hε.2
  have hε2 : Q.ε ^ 2 ≤ 1 := by nlinarith
  have hdd : (d : ℝ) ≤ d ^ 2 / Q.ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (d : ℝ) * Q.ε ^ 2 ≤ d * 1 := by gcongr
      _ = d := mul_one _
      _ ≤ d ^ 2 := by nlinarith
  have hXY : (d : ℝ) * log (2 / Q.δ) / Q.ε ^ 2 ≤ Q.k * d * log (8 * Q.k / Q.δ) / Q.ε ^ 2 := by
    gcongr ?_ / _
    calc (d : ℝ) * log (2 / Q.δ) ≤ d * log (8 * Q.k / Q.δ) := by gcongr
      _ = 1 * (d * log (8 * Q.k / Q.δ)) := by ring
      _ ≤ Q.k * (d * log (8 * Q.k / Q.δ)) := by gcongr
      _ = Q.k * d * log (8 * Q.k / Q.δ) := by ring
  have hT : (Q.T d : ℝ) = Q.k * Q.N d + d * Q.n₂ d := by simp [T, T₂]
  rw [hT]
  set X := (Q.k : ℝ) * d * log (8 * Q.k / Q.δ) / Q.ε ^ 2 with hX
  set Y := (d : ℝ) ^ 2 / Q.ε ^ 2 with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have e : 2000000 * (Q.k * d * log (8 * Q.k / Q.δ) + (d : ℝ) ^ 2) / Q.ε ^ 2
      = 2000000 * X + 2000000 * Y := by
    rw [hX, hY]
    ring
  rw [e]
  have h1 : (Q.k : ℝ) * Q.N d ≤ 1600000 * X := by
    calc (Q.k : ℝ) * Q.N d ≤ Q.k * (1600000 * d * log (8 * Q.k / Q.δ) / Q.ε ^ 2) := by gcongr
      _ = 1600000 * X := by rw [hX]; ring
  have h2 : (d : ℝ) * Q.n₂ d ≤ 33 * Y + 192 * X := by
    calc (d : ℝ) * Q.n₂ d ≤ d * (4 * (8 * d + 48 * log (2 / Q.δ)) / Q.ε ^ 2 + 1) := by gcongr
      _ = 32 * Y + 192 * (d * log (2 / Q.δ) / Q.ε ^ 2) + d := by rw [hY]; ring
      _ ≤ 32 * Y + 192 * X + Y := by linarith
      _ = 33 * Y + 192 * X := by ring
  linarith

end BlockParam

end COLT83
