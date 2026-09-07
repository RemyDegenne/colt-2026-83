/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.RademacherStat

/-!
# Additive norm estimation from a constant-factor estimate (Algorithm 1 of the paper)

With the parameters `s = ⌈4 d / r₀²⌉` and `K = ⌈4096 r₀² log(4/δ) / ε²⌉` of Algorithm 1, if
`ε ≤ r₀`, `r / 2 < r₀ ≤ 2 r` (`r = ‖θ‖`), the squared statistic satisfies
`|rbStat - r²| ≤ r ε / 2` with probability at least `1 - 3δ/8`, hence
`|√(max rbStat 0) - r| ≤ ε / 2`.

Blueprint: `def:additive_algorithm`, `thm:additive_estimation`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι] {s K : ℕ} {θ : EuclideanSpace ℝ ι}

section Helpers

lemma exp_neg_two_mul_log_four_div {δ : ℝ} (hδ : 0 < δ) :
    exp (-(2 * log (4 / δ))) = δ ^ 2 / 16 := by
  have h4 : 0 < 4 / δ := by positivity
  rw [exp_neg, show (2 : ℝ) * log (4 / δ) = ((2 : ℕ) : ℝ) * log (4 / δ) by norm_num,
    Real.exp_nat_mul, Real.exp_log h4]
  field_simp
  norm_num

/-- `2 exp (-x) ≤ δ / 8` when `x ≥ 2 log (4 / δ)`. -/
lemma two_mul_exp_neg_le_div_eight {δ x : ℝ} (hδ : δ ∈ Set.Ioo 0 1) (hx : 2 * log (4 / δ) ≤ x) :
    2 * exp (-x) ≤ δ / 8 := by
  have h1 : exp (-x) ≤ exp (-(2 * log (4 / δ))) := exp_le_exp.2 (neg_le_neg hx)
  rw [exp_neg_two_mul_log_four_div hδ.1] at h1
  have h2 : δ ^ 2 ≤ δ := by nlinarith [hδ.1, hδ.2]
  linarith

lemma le_mul_min {K A B c : ℝ} (hA : c ≤ K * A) (hB : c ≤ K * B) : c ≤ K * min A B := by
  rcases min_choice A B with h | h <;> rw [h] <;> assumption

end Helpers

/-- Union bound for the two terms of the statistic (blueprint `thm:additive_estimation`, first
step): `P(|Z̄ - r²| > 2a) ≤ P(|T₁| > a) + P(V̄ > τ) + 2 exp (-K min (a²/(2τ)) (a/(2b)))`. -/
lemma rbMeasure_real_abs_rbStat_sub_gt_le (hd : 0 < Fintype.card ι) (hs : 0 < s) (hK : 0 < K)
    {a τ : ℝ} (ha : 0 ≤ a) :
    (rbMeasure ι s K).real {p | 2 * a < |rbStat s K θ p - ‖θ‖ ^ 2|}
      ≤ (rbMeasure ι s K).real {p | a < |(∑ k, rbX K θ p.1 k) / K|}
        + ((rbMeasure ι s K).real {p | τ < rbVbar s K θ p.1}
          + 2 * exp (-(K * min (a ^ 2 / (2 * τ))
            (a / (2 * (4 * ((Fintype.card ι : ℝ) / s))))))) := by
  have hsub : {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | 2 * a < |rbStat s K θ p - ‖θ‖ ^ 2|}
      ⊆ {p | a < |(∑ k, rbX K θ p.1 k) / K|} ∪ {p | a < |(∑ k, rbW s K θ p k) / K|} := by
    intro p hp
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hp ⊢
    rw [rbStat_sub_sq_eq hK] at hp
    by_contra hcon
    push Not at hcon
    have := abs_add_le ((∑ k, rbX K θ p.1 k) / K) ((∑ k, rbW s K θ p k) / K)
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans ?_)
  gcongr
  exact rbMeasure_real_avg_rbW_gt_le hd hs hK ha

/-- The block length of Algorithm 1: `⌈4 d / r₀²⌉`. -/
noncomputable def addS (d : ℕ) (r₀ : ℝ) : ℕ := ⌈4 * d / r₀ ^ 2⌉₊

/-- The number of blocks of Algorithm 1: `⌈4096 r₀² log(4/δ) / ε²⌉`. -/
noncomputable def addK (r₀ ε δ : ℝ) : ℕ := ⌈4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2⌉₊

/-- **Additive estimation with a constant-factor estimate** (blueprint `thm:additive_estimation`,
squared form): with the parameters of Algorithm 1, if `ε ≤ r₀` and `r/2 < r₀ ≤ 2r`, then
`|Z̄ - r²| > r ε / 2` with probability at most `3δ/8`. -/
theorem rbMeasure_real_addEst_gt_le (hd : 0 < Fintype.card ι) {ε δ r₀ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) (hεr : ε ≤ r₀) (hr1 : ‖θ‖ / 2 < r₀) (hr2 : r₀ ≤ 2 * ‖θ‖) :
    (rbMeasure ι (addS (Fintype.card ι) r₀) (addK r₀ ε δ)).real
      {p | ‖θ‖ * ε / 2 < |rbStat (addS (Fintype.card ι) r₀) (addK r₀ ε δ) θ p - ‖θ‖ ^ 2|}
      ≤ 3 * δ / 8 := by
  have hd' : (0 : ℝ) < Fintype.card ι := by positivity
  have hL : 0 < log (4 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ.1]; linarith [hδ.2])
  have hr : 0 < ‖θ‖ := by linarith [hε.1]
  have hr₀ : 0 < r₀ := lt_of_lt_of_le hε.1 hεr
  have hε0 : ε ≠ 0 := hε.1.ne'
  have hε0' : 0 < ε := hε.1
  have hr0 : ‖θ‖ ≠ 0 := hr.ne'
  have hr₀0 : r₀ ≠ 0 := hr₀.ne'
  have hKge : 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 ≤ addK r₀ ε δ := Nat.le_ceil _
  have hKpos : 0 < addK r₀ ε δ :=
    Nat.ceil_pos.2 (div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hr₀ 2)) hL) (pow_pos hε.1 2))
  have hsge : 4 * (Fintype.card ι : ℝ) / r₀ ^ 2 ≤ addS (Fintype.card ι) r₀ := Nat.le_ceil _
  have hspos : 0 < addS (Fintype.card ι) r₀ := Nat.ceil_pos.2 (by positivity)
  set s : ℕ := addS (Fintype.card ι) r₀ with hs_def
  set K : ℕ := addK r₀ ε δ with hK_def
  clear_value s K
  have hspos' : (0 : ℝ) < s := by positivity
  have hKpos' : (0 : ℝ) < K := by positivity
  have hds : (Fintype.card ι : ℝ) / s ≤ r₀ ^ 2 / 4 := by
    rw [div_le_iff₀ hspos']
    calc (Fintype.card ι : ℝ) = r₀ ^ 2 / 4 * (4 * Fintype.card ι / r₀ ^ 2) := by field_simp
      _ ≤ r₀ ^ 2 / 4 * s := by gcongr
  have hds0 : (0 : ℝ) ≤ Fintype.card ι / s := by positivity
  set a : ℝ := ‖θ‖ * ε / 4 with ha_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    positivity
  set τ : ℝ := 8 * (((Fintype.card ι : ℝ) / s) ^ 2 + 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s))
    with hτ_def
  have hτ0 : 0 < τ := by
    rw [hτ_def]
    positivity
  clear_value a τ
  have key := rbMeasure_real_abs_rbStat_sub_gt_le (θ := θ) (τ := τ) hd hspos hKpos ha
  rw [show ‖θ‖ * ε / 2 = 2 * a by rw [ha_def]; ring]
  refine key.trans ?_
  have hr4 : ‖θ‖ ^ 2 < 4 * r₀ ^ 2 := by nlinarith
  have hr₀4 : ‖θ‖ ^ 2 / 4 < r₀ ^ 2 := by nlinarith
  -- Term 1
  have hb1 : (rbMeasure ι s K).real {p | a < |(∑ k, rbX K θ p.1 k) / K|} ≤ δ / 8 := by
    refine (rbMeasure_real_avg_rbX_gt_le hKpos ha).trans (two_mul_exp_neg_le_div_eight hδ ?_)
    have e1 : a ^ 2 / (32 * ‖θ‖ ^ 4) = ε ^ 2 / (512 * ‖θ‖ ^ 2) := by
      rw [ha_def]
      field_simp
      ring
    have e2 : a / (8 * ‖θ‖ ^ 2) = ε / (32 * ‖θ‖) := by
      rw [ha_def]
      field_simp
      ring
    rw [e1, e2]
    refine le_mul_min ?_ ?_
    · calc 2 * log (4 / δ)
          ≤ 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε ^ 2 / (512 * ‖θ‖ ^ 2)) := by
            rw [show 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε ^ 2 / (512 * ‖θ‖ ^ 2))
                = 8 * log (4 / δ) * (r₀ ^ 2 / ‖θ‖ ^ 2) by field_simp; ring]
            have h1 : 1 / 4 ≤ r₀ ^ 2 / ‖θ‖ ^ 2 := by
              rw [le_div_iff₀ (pow_pos hr 2)]
              linarith
            have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * log (4 / δ))
            linarith
        _ ≤ K * (ε ^ 2 / (512 * ‖θ‖ ^ 2)) := by gcongr
    · calc 2 * log (4 / δ)
          ≤ 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε / (32 * ‖θ‖)) := by
            rw [show 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε / (32 * ‖θ‖))
                = 128 * log (4 / δ) * (r₀ ^ 2 / (ε * ‖θ‖)) by field_simp; ring]
            have h5 : ε * ‖θ‖ ≤ r₀ * (2 * r₀) :=
              mul_le_mul hεr (by linarith) (norm_nonneg θ) hr₀.le
            have h1 : 1 / 64 ≤ r₀ ^ 2 / (ε * ‖θ‖) := by
              rw [le_div_iff₀ (mul_pos hε.1 hr)]
              nlinarith [h5]
            have h2 := mul_le_mul_of_nonneg_left h1
              (by positivity : (0 : ℝ) ≤ 128 * log (4 / δ))
            linarith
        _ ≤ K * (ε / (32 * ‖θ‖)) := by gcongr
  -- variance proxy
  have hb2 : (rbMeasure ι s K).real {p | τ < rbVbar s K θ p.1} ≤ δ / 8 := by
    rw [hτ_def]
    refine (rbMeasure_real_rbVbar_gt_le hKpos).trans (two_mul_exp_neg_le_div_eight hδ ?_)
    calc 2 * log (4 / δ) ≤ 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 / 128 := by
          rw [show 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 / 128
              = 32 * log (4 / δ) * (r₀ ^ 2 / ε ^ 2) by field_simp; ring]
          have h1 : 1 ≤ r₀ ^ 2 / ε ^ 2 := by
            rw [le_div_iff₀ (pow_pos hε.1 2), one_mul]
            exact pow_le_pow_left₀ hε.1.le hεr 2
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 32 * log (4 / δ))
          linarith
      _ ≤ K / 128 := by gcongr
  -- Term 2
  have hb3 : 2 * exp (-(K * min (a ^ 2 / (2 * τ))
      (a / (2 * (4 * ((Fintype.card ι : ℝ) / s)))))) ≤ δ / 8 := by
    refine two_mul_exp_neg_le_div_eight hδ ?_
    have hτle : τ ≤ 25 * r₀ ^ 4 / 2 := by
      rw [hτ_def]
      have h1 : ((Fintype.card ι : ℝ) / s) ^ 2 ≤ (r₀ ^ 2 / 4) ^ 2 := pow_le_pow_left₀ hds0 hds 2
      have h2 : 3 * (Fintype.card ι : ℝ) * ‖θ‖ ^ 2 / (2 * s)
          = 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s) := by ring
      have h3a : 3 * ‖θ‖ ^ 2 / 2 ≤ 3 * (4 * r₀ ^ 2) / 2 := by linarith
      have h3 : 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s)
          ≤ 3 * (4 * r₀ ^ 2) / 2 * (r₀ ^ 2 / 4) :=
        mul_le_mul h3a hds hds0 (by positivity)
      rw [h2]
      linarith
    have hb : 4 * ((Fintype.card ι : ℝ) / s) ≤ r₀ ^ 2 := by linarith
    have hbpos : 0 < 4 * ((Fintype.card ι : ℝ) / s) := by positivity
    refine le_mul_min ?_ ?_
    · calc 2 * log (4 / δ)
          ≤ 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε ^ 2 / (1600 * r₀ ^ 2)) := by
            rw [show 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε ^ 2 / (1600 * r₀ ^ 2))
                = 4096 / 1600 * log (4 / δ) by field_simp]
            linarith
        _ ≤ K * (ε ^ 2 / (1600 * r₀ ^ 2)) := by gcongr
        _ ≤ K * (a ^ 2 / (2 * τ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos'.le
            rw [ha_def, div_le_div_iff₀ (by positivity) (by positivity)]
            calc ε ^ 2 * (2 * τ) ≤ ε ^ 2 * (2 * (25 * r₀ ^ 4 / 2)) := by gcongr
              _ = 25 * r₀ ^ 4 * ε ^ 2 := by ring
              _ ≤ (‖θ‖ * ε / 4) ^ 2 * (1600 * r₀ ^ 2) := by
                  have h4 : r₀ ^ 2 ≤ 4 * ‖θ‖ ^ 2 := by nlinarith
                  have h5 : 0 ≤ r₀ ^ 2 * ε ^ 2 := by positivity
                  have h6 := mul_le_mul_of_nonneg_left h4 h5
                  linarith
    · calc 2 * log (4 / δ)
          ≤ 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε / (16 * r₀)) := by
            rw [show 4096 * r₀ ^ 2 * log (4 / δ) / ε ^ 2 * (ε / (16 * r₀))
                = 256 * log (4 / δ) * (r₀ / ε) by field_simp; ring]
            have h1 : 1 ≤ r₀ / ε := by
              rw [le_div_iff₀ hε.1, one_mul]
              exact hεr
            have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 256 * log (4 / δ))
            linarith
        _ ≤ K * (ε / (16 * r₀)) := by gcongr
        _ ≤ K * (a / (2 * (4 * ((Fintype.card ι : ℝ) / s)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos'.le
            rw [ha_def, div_le_div_iff₀ (by positivity) (by positivity)]
            calc ε * (2 * (4 * ((Fintype.card ι : ℝ) / s))) ≤ ε * (2 * r₀ ^ 2) := by gcongr
              _ ≤ ‖θ‖ * ε / 4 * (16 * r₀) := by
                  have h6 := mul_le_mul_of_nonneg_left hr2 (mul_pos hε.1 hr₀).le
                  linarith
  linarith

/-- **Additive estimation with a constant-factor estimate** (blueprint `thm:additive_estimation`):
the estimate `√(max Z̄ 0)` is within `ε / 2` of `‖θ‖` with probability at least `1 - 3δ/8`. -/
theorem rbMeasure_real_sqrt_addEst_gt_le (hd : 0 < Fintype.card ι) {ε δ r₀ : ℝ}
    (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) (hεr : ε ≤ r₀) (hr1 : ‖θ‖ / 2 < r₀)
    (hr2 : r₀ ≤ 2 * ‖θ‖) :
    (rbMeasure ι (addS (Fintype.card ι) r₀) (addK r₀ ε δ)).real
      {p | ε / 2 < |√(max (rbStat (addS (Fintype.card ι) r₀) (addK r₀ ε δ) θ p) 0) - ‖θ‖|}
      ≤ 3 * δ / 8 := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (rbMeasure_real_addEst_gt_le hd hε hδ hεr hr1 hr2)
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  by_contra hcon
  rw [not_lt, abs_le] at hcon
  have hr : 0 < ‖θ‖ := by linarith [hε.1]
  set Z := rbStat (addS (Fintype.card ι) r₀) (addK r₀ ε δ) θ p with hZ
  have hεr' : ε / 2 ≤ ‖θ‖ := by linarith
  have hZnn : 0 ≤ Z := by nlinarith
  rw [max_eq_left hZnn] at hp
  have hsq : √Z ^ 2 = Z := Real.sq_sqrt hZnn
  have hsqrt0 : 0 ≤ √Z := Real.sqrt_nonneg Z
  -- |√Z - r| = |Z - r²| / (√Z + r) ≤ (r ε / 2) / r = ε / 2
  have hfac : (√Z - ‖θ‖) * (√Z + ‖θ‖) = Z - ‖θ‖ ^ 2 := by nlinarith
  have hpos : 0 < √Z + ‖θ‖ := add_pos_of_nonneg_of_pos hsqrt0 hr
  have h1 : |√Z - ‖θ‖| * (√Z + ‖θ‖) ≤ ‖θ‖ * ε / 2 := by
    rw [← abs_of_pos hpos, ← abs_mul, hfac]
    exact abs_le.2 hcon
  have h2 : |√Z - ‖θ‖| * ‖θ‖ ≤ |√Z - ‖θ‖| * (√Z + ‖θ‖) := by
    gcongr
    linarith
  have h3 : |√Z - ‖θ‖| ≤ ε / 2 := by
    have := h2.trans h1
    rw [mul_comm, show ‖θ‖ * ε / 2 = ‖θ‖ * (ε / 2) by ring] at this
    exact le_of_mul_le_mul_left this hr
  linarith

end Maiti2026Power
