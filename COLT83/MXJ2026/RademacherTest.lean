/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.RademacherEst

/-!
# The scale test (norm estimation, Section 3 of the paper)

The test at scale `t` with confidence `δ'` runs the Rademacher block sampling rule with
`s = ⌈4 d / t²⌉` and `K = ⌈5120 log(1/δ')⌉` and returns `H₁` if `Z̄ ≥ 3t²/2`, `H₀` otherwise.
Under `H₀ : r ≤ t` it returns `H₁` with probability at most `3δ'/4`; under `H₁ : r ≥ 2t` it
returns `H₀` with probability at most `3δ'/4`.

Blueprint: `def:scale_test`, `lem:test_error_h0`, `lem:test_error_h1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace COLT83

variable {ι : Type*} [Fintype ι] {θ : EuclideanSpace ℝ ι}

/-- The block length of the scale test at scale `t`: `⌈4 d / t²⌉`. -/
noncomputable def testS (d : ℕ) (t : ℝ) : ℕ := ⌈4 * d / t ^ 2⌉₊

/-- The number of blocks of the scale test with confidence `δ'`: `⌈5120 log(1/δ')⌉`. -/
noncomputable def testK (δ' : ℝ) : ℕ := ⌈5120 * log (1 / δ')⌉₊

/-- `6 exp (-x) ≤ 3 δ' / 4` when `2048 x ≥ 5120 log (1 / δ')` and `δ' ≤ 1/4`. -/
lemma six_mul_exp_neg_le {δ' x : ℝ} (hδ : δ' ∈ Set.Ioc 0 (1 / 4))
    (hx : 5120 * log (1 / δ') ≤ 2048 * x) : 6 * exp (-x) ≤ 3 * δ' / 4 := by
  set L := log (1 / δ') with hL
  have hδ1 : δ' ≤ 1 := hδ.2.trans (by norm_num)
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_one_div hδ.1 hδ1)
  have h1 : exp (-x) ≤ exp (-(2 * L)) * exp (-(L / 2)) := by
    rw [← exp_add]
    exact exp_le_exp.2 (by linarith)
  have h2 : exp (-(2 * L)) = δ' ^ 2 := by
    rw [exp_neg, show (2 : ℝ) * L = ((2 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul, hL,
      Real.exp_log (one_div_pos.2 hδ.1)]
    field_simp
  have h3 : exp (-(L / 2)) ≤ 1 / 2 := by
    have h4 : log 4 ≤ L := by
      rw [hL]
      exact Real.log_le_log (by norm_num) ((le_one_div (by norm_num) hδ.1).2 hδ.2)
    have h5 : exp (-(L / 2)) ≤ exp (-(log 4 / 2)) := exp_le_exp.2 (by linarith)
    have h6 : exp (-(log 4 / 2)) = 1 / 2 := by
      rw [exp_neg, show log 4 / 2 = log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring, Real.exp_log (by norm_num)]
      norm_num
    linarith
  have h7 : exp (-x) ≤ δ' ^ 2 * (1 / 2) := by
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  nlinarith [hδ.1, hδ.2]

/-- Common facts on the parameters of the scale test. -/
lemma testS_facts (hd : 0 < Fintype.card ι) {t : ℝ} (ht : 0 < t) :
    0 < testS (Fintype.card ι) t ∧ (Fintype.card ι : ℝ) / testS (Fintype.card ι) t ≤ t ^ 2 / 4 := by
  have hsge : 4 * (Fintype.card ι : ℝ) / t ^ 2 ≤ testS (Fintype.card ι) t := Nat.le_ceil _
  have hspos : 0 < testS (Fintype.card ι) t := Nat.ceil_pos.2 (by positivity)
  refine ⟨hspos, ?_⟩
  have hspos' : (0 : ℝ) < testS (Fintype.card ι) t := by positivity
  rw [div_le_iff₀ hspos']
  calc (Fintype.card ι : ℝ) = t ^ 2 / 4 * (4 * Fintype.card ι / t ^ 2) := by field_simp
    _ ≤ t ^ 2 / 4 * testS (Fintype.card ι) t := by gcongr

lemma testK_facts {δ' : ℝ} (hδ : δ' ∈ Set.Ioc 0 (1 / 4)) :
    0 < testK δ' ∧ 5120 * log (1 / δ') ≤ testK δ' := by
  have hL : 0 < log (1 / δ') :=
    Real.log_pos (by rw [lt_one_div one_pos hδ.1]; linarith [hδ.2])
  exact ⟨Nat.ceil_pos.2 (by positivity), Nat.le_ceil _⟩

/-- The three terms of the union bound are each at most `2 exp (-K/2048)` when the minimum in the
exponent is at least `1/2048`. -/
lemma two_mul_exp_neg_mul_min_le {K A B : ℝ} (hK : 0 ≤ K) (hA : 1 / 2048 ≤ A) (hB : 1 / 2048 ≤ B) :
    2 * exp (-(K * min A B)) ≤ 2 * exp (-(K / 2048)) := by
  gcongr
  rw [show K / 2048 = K * (1 / 2048) by ring]
  exact le_mul_min (by gcongr) (by gcongr)

/-- **Error of the scale test under `H₀`** (blueprint `lem:test_error_h0`): if `‖θ‖ ≤ t`, the test
returns `H₁` (`Z̄ ≥ 3t²/2`) with probability at most `3δ'/4`. -/
theorem rbMeasure_real_test_h0_le (hd : 0 < Fintype.card ι) {t δ' : ℝ} (ht : 0 < t)
    (hδ : δ' ∈ Set.Ioc 0 (1 / 4)) (hθ : ‖θ‖ ≤ t) :
    (rbMeasure ι (testS (Fintype.card ι) t) (testK δ')).real
      {p | 3 * t ^ 2 / 2 ≤ rbStat (testS (Fintype.card ι) t) (testK δ') θ p} ≤ 3 * δ' / 4 := by
  obtain ⟨hspos, hds⟩ := testS_facts hd ht
  obtain ⟨hKpos, hKge⟩ := testK_facts hδ
  have hd' : (0 : ℝ) < Fintype.card ι := by positivity
  set s : ℕ := testS (Fintype.card ι) t with hs_def
  set K : ℕ := testK δ' with hK_def
  clear_value s K
  have hspos' : (0 : ℝ) < s := by positivity
  have hK' : (0 : ℝ) ≤ K := by positivity
  have hds0 : (0 : ℝ) ≤ Fintype.card ι / s := by positivity
  have hr0 : 0 ≤ ‖θ‖ := norm_nonneg θ
  set a : ℝ := t ^ 2 / 8 with ha_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    positivity
  set τ : ℝ := 8 * (((Fintype.card ι : ℝ) / s) ^ 2 + 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s))
    with hτ_def
  have hτ0 : 0 < τ := by
    rw [hτ_def]
    positivity
  clear_value a τ
  -- the error event is contained in `{2a < |Z̄ - r²|}`
  have hsub : {p | 3 * t ^ 2 / 2 ≤ rbStat s K θ p}
      ⊆ {p | 2 * a < |rbStat s K θ p - ‖θ‖ ^ 2|} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    have : ‖θ‖ ^ 2 ≤ t ^ 2 := by nlinarith
    rw [ha_def, lt_abs]
    left
    nlinarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (rbMeasure_real_abs_rbStat_sub_gt_le (θ := θ) (τ := τ) hd hspos hKpos ha).trans ?_
  -- Term 1
  have hb1 : (rbMeasure ι s K).real {p | a < |(∑ k, rbX K θ p.1 k) / K|}
      ≤ 2 * exp (-(K / 2048)) := by
    rcases eq_or_lt_of_le hr0 with hr | hr
    · have hθ0 : θ = 0 := norm_eq_zero.1 hr.symm
      subst hθ0
      have hapos : 0 < a := by
        rw [ha_def]
        positivity
      have : {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | a < |(∑ k, rbX K 0 p.1 k) / K|}
          = ∅ := by
        ext p
        simp [rbX_eq_zero_of_eq_zero, hapos.le]
      rw [this, measureReal_empty]
      positivity
    · refine (rbMeasure_real_avg_rbX_gt_le hr hKpos ha).trans
        (two_mul_exp_neg_mul_min_le hK' ?_ ?_)
      · rw [ha_def, le_div_iff₀ (by positivity)]
        have : ‖θ‖ ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ hr0 hθ 4
        nlinarith
      · rw [ha_def, le_div_iff₀ (by positivity)]
        nlinarith
  -- variance proxy
  have hb2 : (rbMeasure ι s K).real {p | τ < rbVbar s K θ p.1} ≤ 2 * exp (-(K / 2048)) := by
    rw [hτ_def]
    refine (rbMeasure_real_rbVbar_gt_le hKpos).trans ?_
    gcongr
    linarith
  -- Term 2
  have hb3 : 2 * exp (-(K * min (a ^ 2 / (2 * τ)) (a / (2 * (4 * ((Fintype.card ι : ℝ) / s))))))
      ≤ 2 * exp (-(K / 2048)) := by
    have hτle : τ ≤ 7 * t ^ 4 / 2 := by
      rw [hτ_def]
      have h1 : ((Fintype.card ι : ℝ) / s) ^ 2 ≤ (t ^ 2 / 4) ^ 2 := pow_le_pow_left₀ hds0 hds 2
      have h2 : 3 * (Fintype.card ι : ℝ) * ‖θ‖ ^ 2 / (2 * s)
          = 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s) := by ring
      have h3 : 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s) ≤ 3 * t ^ 2 / 2 * (t ^ 2 / 4) :=
        mul_le_mul (by nlinarith) hds hds0 (by positivity)
      rw [h2]
      nlinarith
    have hb : 4 * ((Fintype.card ι : ℝ) / s) ≤ t ^ 2 := by linarith
    have hbpos : 0 < 4 * ((Fintype.card ι : ℝ) / s) := by positivity
    refine two_mul_exp_neg_mul_min_le hK' ?_ ?_
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
  have hfinal : 6 * exp (-(K / 2048)) ≤ 3 * δ' / 4 :=
    six_mul_exp_neg_le hδ (by linarith)
  linarith

/-- **Error of the scale test under `H₁`** (blueprint `lem:test_error_h1`): if `2t ≤ ‖θ‖`, the test
returns `H₀` (`Z̄ < 3t²/2`) with probability at most `3δ'/4`. -/
theorem rbMeasure_real_test_h1_le (hd : 0 < Fintype.card ι) {t δ' : ℝ} (ht : 0 < t)
    (hδ : δ' ∈ Set.Ioc 0 (1 / 4)) (hθ : 2 * t ≤ ‖θ‖) :
    (rbMeasure ι (testS (Fintype.card ι) t) (testK δ')).real
      {p | rbStat (testS (Fintype.card ι) t) (testK δ') θ p < 3 * t ^ 2 / 2} ≤ 3 * δ' / 4 := by
  obtain ⟨hspos, hds⟩ := testS_facts hd ht
  obtain ⟨hKpos, hKge⟩ := testK_facts hδ
  have hd' : (0 : ℝ) < Fintype.card ι := by positivity
  set s : ℕ := testS (Fintype.card ι) t with hs_def
  set K : ℕ := testK δ' with hK_def
  clear_value s K
  have hspos' : (0 : ℝ) < s := by positivity
  have hK' : (0 : ℝ) ≤ K := by positivity
  have hds0 : (0 : ℝ) ≤ Fintype.card ι / s := by positivity
  have hr : 0 < ‖θ‖ := by linarith
  have ht2 : t ^ 2 ≤ ‖θ‖ ^ 2 / 4 := by nlinarith
  set a : ℝ := ‖θ‖ ^ 2 / 8 with ha_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    positivity
  set τ : ℝ := 8 * (((Fintype.card ι : ℝ) / s) ^ 2 + 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s))
    with hτ_def
  have hτ0 : 0 < τ := by
    rw [hτ_def]
    positivity
  clear_value a τ
  have hsub : {p | rbStat s K θ p < 3 * t ^ 2 / 2}
      ⊆ {p | 2 * a < |rbStat s K θ p - ‖θ‖ ^ 2|} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [ha_def, lt_abs]
    right
    nlinarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (rbMeasure_real_abs_rbStat_sub_gt_le (θ := θ) (τ := τ) hd hspos hKpos ha).trans ?_
  have hb1 : (rbMeasure ι s K).real {p | a < |(∑ k, rbX K θ p.1 k) / K|}
      ≤ 2 * exp (-(K / 2048)) := by
    refine (rbMeasure_real_avg_rbX_gt_le hr hKpos ha).trans
      (two_mul_exp_neg_mul_min_le hK' ?_ ?_)
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
  have hb2 : (rbMeasure ι s K).real {p | τ < rbVbar s K θ p.1} ≤ 2 * exp (-(K / 2048)) := by
    rw [hτ_def]
    refine (rbMeasure_real_rbVbar_gt_le hKpos).trans ?_
    gcongr
    linarith
  have hb3 : 2 * exp (-(K * min (a ^ 2 / (2 * τ)) (a / (2 * (4 * ((Fintype.card ι : ℝ) / s))))))
      ≤ 2 * exp (-(K / 2048)) := by
    have hds' : (Fintype.card ι : ℝ) / s ≤ ‖θ‖ ^ 2 / 16 := by linarith
    have hτle : τ ≤ 25 * ‖θ‖ ^ 4 / 32 := by
      rw [hτ_def]
      have h1 : ((Fintype.card ι : ℝ) / s) ^ 2 ≤ (‖θ‖ ^ 2 / 16) ^ 2 := pow_le_pow_left₀ hds0 hds' 2
      have h2 : 3 * (Fintype.card ι : ℝ) * ‖θ‖ ^ 2 / (2 * s)
          = 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s) := by ring
      have h3 : 3 * ‖θ‖ ^ 2 / 2 * ((Fintype.card ι : ℝ) / s) ≤ 3 * ‖θ‖ ^ 2 / 2 * (‖θ‖ ^ 2 / 16) :=
        mul_le_mul_of_nonneg_left hds' (by positivity)
      rw [h2]
      nlinarith
    have hb : 4 * ((Fintype.card ι : ℝ) / s) ≤ ‖θ‖ ^ 2 / 4 := by linarith
    have hbpos : 0 < 4 * ((Fintype.card ι : ℝ) / s) := by positivity
    refine two_mul_exp_neg_mul_min_le hK' ?_ ?_
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [ha_def, le_div_iff₀ (by positivity)]
      nlinarith
  have hfinal : 6 * exp (-(K / 2048)) ≤ 3 * δ' / 4 :=
    six_mul_exp_neg_le hδ (by linarith)
  linarith

end COLT83
