/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The binary Kullback-Leibler divergence

The Kullback-Leibler divergence between two Bernoulli distributions with parameters `p` and `q`
is the real number
`klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`.
This file defines it and proves its basic properties.

## Main definitions

* `InformationTheory.klBerReal`: the binary Kullback-Leibler divergence.

## TODO

When `q` is `0` or `1`, the divergence should be infinite, but the formula above is real-valued
and gives `0`.

-/

@[expose] public section

open Real
open scoped ENNReal

namespace InformationTheory

variable {p q : ℝ}

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. -/
noncomputable def klBerReal (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

lemma klBerReal_apply (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

lemma klBerReal_zero_left :
    klBerReal 0 q = log (1 / (1 - q)) := by simp [klBerReal]

lemma klBerReal_one_left :
    klBerReal 1 q = log (1 / q) := by simp [klBerReal]

lemma klBerReal_zero_right :
    klBerReal p 0 = (1 - p) * log (1 - p) := by simp [klBerReal]

lemma klBerReal_one_right :
    klBerReal p 1 = p * log p := by simp [klBerReal]

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
in `ℝ≥0∞`: it is `ENNReal.ofReal (klBerReal p q)`, except that it is infinite when `q ∈ {0, 1}`
and `p ≠ q`, where the Bernoulli measures are not absolutely continuous. -/
noncomputable def klBer (p q : ℝ) : ℝ≥0∞ :=
  if q = 0 then
    if p = 0 then 0 else ∞
  else
    if q = 1 then (if p = 1 then 0 else ∞) else ENNReal.ofReal (klBerReal p q)

lemma klBer_zero_left_of_ne (hq : q ≠ 0) :
    klBer 0 q = if q = 1 then ∞ else ENNReal.ofReal (log (1 / (1 - q))) := by
  simp [klBer, hq]
  split_ifs with hq1 <;> simp [klBerReal_zero_left]

lemma klBer_one_left_of_ne (hq : q ≠ 1) :
    klBer 1 q = if q = 0 then ∞ else ENNReal.ofReal (log (1 / q)) := by
  simp [klBer, hq]
  split_ifs with hq0 <;> simp [klBerReal_one_left]

lemma klBer_zero_right :
    klBer p 0 = if p = 0 then 0 else ∞ := by simp [klBer]

lemma klBer_one_right :
    klBer p 1 = if p = 1 then 0 else ∞ := by simp [klBer]

lemma klBer_eq_ofReal (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBer p q = ENNReal.ofReal (klBerReal p q) := by
  simp [klBer, hq, hq1]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  simp only [klBerReal, sub_sub_cancel]
  ring

lemma klBer_one_sub (p q : ℝ) : klBer (1 - p) (1 - q) = klBer p q := by
  simp only [klBer, klBerReal_one_sub]
  by_cases hq : q = 0
  · grind
  by_cases hq1 : q = 1 <;> grind

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [klBerReal]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klBerReal]
  simp [klBerReal, div_self hp, sub_ne_zero.2 hp1.symm]

@[simp] lemma klBer_self (p : ℝ) : klBer p p = 0 := by
  simp [klBer]
  split_ifs <;> simp

/-- `a * log (a / b) = a * (log a - log b)`, also when `a = 0` thanks to `log 0 = 0`. -/
lemma mul_log_div_eq_mul_sub {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * (log a - log b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBerReal_eq_of_ne {p q : ℝ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBerReal, mul_log_div_eq_mul_sub hq, mul_log_div_eq_mul_sub (sub_ne_zero.2 hq1.symm)]

end InformationTheory
