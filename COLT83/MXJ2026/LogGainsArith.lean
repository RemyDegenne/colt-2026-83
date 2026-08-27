/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Arithmetic of the constants in the log-gains theorem

Two purely real-arithmetic lemmas used by the region algorithm and the log-gains theorem.

* `region_phase1_arith`: the numeric condition of the first phase of the region algorithm
  (blueprint `lem:region_phase1`, "Arithmetic" step): with the variance proxy `σ² = 4 d / T₁` and
  `T₁ ≥ 640 (w² + d log(4/δ)) / ε²`, the deviation bound
  `2 (2 w / √T₁) + 2 σ √(2 c_G log(2/δ))` is at most `ε / 2`.
* `logGains_budget_arith`: the budget arithmetic of the log-gains theorem
  (blueprint `thm:log_gains` (ii)): `T₁ + N ≤ 97281 d (log((m/d)₊) + log(4/δ)) / ε²`.
-/

@[expose] public section

open Real

namespace COLT83

/-- The numeric condition of the first phase of the region algorithm: with the width bound
`w`, the variance proxy `σ² = 4 d / T₁` and `T₁ ≥ 640 (w² + d log(4/δ)) / ε²`, the deviation
bound `2 · (2 w / √T₁) + 2 σ √(2 c_G log(2/δ))` is at most `ε / 2` (for `c_G ≤ 5/2`). -/
lemma region_phase1_arith {w d T₁ ε δ σ cG : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) (hT₁ : 0 < T₁)
    (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (hσ0 : 0 ≤ σ) (hσ : σ ^ 2 = 4 * d / T₁)
    (hcG0 : 0 ≤ cG) (hcG : cG ≤ 5 / 2)
    (hT : 640 * (w ^ 2 + d * Real.log (4 / δ)) / ε ^ 2 ≤ T₁) :
    2 * (2 / √T₁ * w) + 2 * σ * √(2 * cG * Real.log (1 / (δ / 2))) ≤ ε / 2 := by
  have hδ0 : 0 < δ := hδ.1
  set L := log (1 / (δ / 2)) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_one_div (by positivity) (by linarith [hδ.2]))
  have hLle : L ≤ log (4 / δ) := by
    refine Real.log_le_log (by positivity) ?_
    rw [one_div_div]
    exact div_le_div_of_nonneg_right (by norm_num) hδ0.le
  set a := 2 * (2 / √T₁ * w) with ha
  set b := 2 * σ * √(2 * cG * L) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 = 16 * w ^ 2 / T₁ := by
    rw [ha, mul_pow, mul_pow, div_pow, Real.sq_sqrt hT₁.le]
    ring
  have hb2 : b ^ 2 = 32 * cG * d * L / T₁ := by
    rw [hb, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hσ]
    ring
  have hsum : (a + b) ^ 2 ≤ (ε / 2) ^ 2 := by
    have h1 : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have h3 : 64 * cG * d * L ≤ 160 * d * log (4 / δ) := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul hcG hLle hL0 (by norm_num)) hd
      linarith
    have h2 : 32 * w ^ 2 + 64 * cG * d * L ≤ 160 * (w ^ 2 + d * log (4 / δ)) := by
      linarith [sq_nonneg w]
    have h5 : (w ^ 2 + d * log (4 / δ)) / T₁ ≤ ε ^ 2 / 640 := by
      rw [div_le_iff₀ (by positivity)] at hT
      rw [div_le_div_iff₀ hT₁ (by norm_num)]
      linarith
    calc (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := h1
      _ = (32 * w ^ 2 + 64 * cG * d * L) / T₁ := by rw [ha2, hb2]; ring
      _ ≤ 160 * (w ^ 2 + d * log (4 / δ)) / T₁ := div_le_div_of_nonneg_right h2 hT₁.le
      _ = 160 * ((w ^ 2 + d * log (4 / δ)) / T₁) := by ring
      _ ≤ 160 * (ε ^ 2 / 640) := by gcongr
      _ = (ε / 2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsum

/-- The budget arithmetic of the log-gains theorem:
`T₁ + N ≤ 97281 d (log((m/d)₊) + log(4/δ)) / ε²` where `(u)₊ = max 1 u`, from
`T₁ ≤ 640 (w² + d log(4/δ))/ε² + 1` with `w² ≤ 2 d log(m/d + 1)` (natural division `m / d`
inside the log) and the Median Elimination budget `N ≤ 16000 d log(3/(δ/2)) / (ε/2)²`. -/
lemma logGains_budget_arith {d m : ℕ} (hd : 1 ≤ d) (hdm : d ≤ m) {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) {w : ℝ} (hw : w ^ 2 ≤ 2 * d * Real.log (((m / d : ℕ) : ℝ) + 1))
    {T₁ N : ℝ} (hT₁ : T₁ ≤ 640 * (w ^ 2 + d * Real.log (4 / δ)) / ε ^ 2 + 1)
    (hN : N ≤ 16000 * d * Real.log (3 / (δ / 2)) / (ε / 2) ^ 2) :
    T₁ + N ≤ 97281 * d * (Real.log (max 1 ((m : ℝ) / d)) + Real.log (4 / δ)) / ε ^ 2 := by
  have hε0 : 0 < ε := hε.1
  have hδ0 : 0 < δ := hδ.1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set P := max 1 ((m : ℝ) / d) with hP
  have hP1 : 1 ≤ P := le_max_left _ _
  have hP0 : 0 ≤ log P := Real.log_nonneg hP1
  -- `log (m / d + 1) ≤ log 2 + log P`
  have hq : ((m / d : ℕ) : ℝ) + 1 ≤ 2 * P := by
    have h1 : (1 : ℝ) ≤ ((m / d : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hdm hd
    have h2 : ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d := Nat.cast_div_le
    have h3 : (m : ℝ) / d ≤ P := le_max_right _ _
    linarith
  have hlogq : log (((m / d : ℕ) : ℝ) + 1) ≤ log 2 + log P := by
    rw [← Real.log_mul two_ne_zero (by linarith)]
    exact Real.log_le_log (by positivity) hq
  -- `log 4 = 2 log 2 ≤ log (4 / δ)` and `1 < log (4 / δ)`
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
    ring
  have hL4 : log 4 ≤ log (4 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith [hδ.2])
  have hL1 : 1 < log (4 / δ) := by linarith [Real.log_two_gt_d9]
  -- the width term
  have hw' : w ^ 2 ≤ 2 * d * log P + d * log (4 / δ) := by
    have h1 := mul_le_mul_of_nonneg_left hlogq (by positivity : (0 : ℝ) ≤ 2 * d)
    have h2 := mul_le_mul_of_nonneg_left hL4 hd0.le
    rw [hlog4] at h2
    linarith
  -- `1 ≤ d log (4 / δ) / ε ^ 2`
  have h1 : 1 ≤ d * log (4 / δ) / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have := pow_le_one₀ hε0.le hε.2 (n := 2)
    have := one_le_mul_of_one_le_of_one_le hd1 hL1.le
    linarith
  have hdP : 0 ≤ (d : ℝ) * log P := mul_nonneg hd0.le hP0
  -- the two budgets
  have hT₁' : T₁ ≤ 1281 * d * (log P + log (4 / δ)) / ε ^ 2 := by
    calc T₁ ≤ 640 * (w ^ 2 + d * log (4 / δ)) / ε ^ 2 + 1 := hT₁
      _ ≤ 640 * (2 * d * log P + 2 * d * log (4 / δ)) / ε ^ 2 + d * log (4 / δ) / ε ^ 2 :=
          add_le_add (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) (by positivity)) h1
      _ = (640 * (2 * d * log P + 2 * d * log (4 / δ)) + d * log (4 / δ)) / ε ^ 2 := by ring
      _ ≤ 1281 * d * (log P + log (4 / δ)) / ε ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  have hlog6 : log (3 / (δ / 2)) ≤ 3 / 2 * log (4 / δ) := by
    have h : (3 : ℝ) / (δ / 2) = 4 / δ * (3 / 2) := by
      field_simp
      ring
    rw [h, Real.log_mul (by positivity) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have hN' : N ≤ 96000 * d * (log P + log (4 / δ)) / ε ^ 2 := by
    calc N ≤ 16000 * d * log (3 / (δ / 2)) / (ε / 2) ^ 2 := hN
      _ = 64000 * d * log (3 / (δ / 2)) / ε ^ 2 := by ring
      _ ≤ 64000 * d * (3 / 2 * log (4 / δ)) / ε ^ 2 := by gcongr
      _ ≤ 96000 * d * (log P + log (4 / δ)) / ε ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  calc T₁ + N ≤ 1281 * d * (log P + log (4 / δ)) / ε ^ 2
      + 96000 * d * (log P + log (4 / δ)) / ε ^ 2 := add_le_add hT₁' hN'
    _ = 97281 * d * (log P + log (4 / δ)) / ε ^ 2 := by ring

end COLT83
