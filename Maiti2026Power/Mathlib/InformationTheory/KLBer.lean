/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The binary Kullback-Leibler divergence

The Kullback-Leibler divergence between two Bernoulli distributions with parameters `p` and `q`
is `p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))` for `q ∈ (0, 1)`, and it is infinite
when `q ∈ {0, 1}` and `p ≠ q`. This file defines it, first as the real-valued function `klBerReal`
given by that formula, then as the `ℝ≥0∞`-valued function `klBer` which also has the right values
at the boundary, and proves their basic properties. The identification with the divergence of two
Bernoulli measures is `InformationTheory.klDiv_bernoulliMeasure`.

## Main definitions

* `InformationTheory.klBerReal`: the binary Kullback-Leibler divergence, as a real number.
* `InformationTheory.klBer`: the binary Kullback-Leibler divergence, in `ℝ≥0∞`.
-/

@[expose] public section

open Real
open scoped ENNReal

namespace InformationTheory

variable {p q : ℝ}

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. The formula is only meaningful for
`q ∈ (0, 1)`: see `klBer` for the `ℝ≥0∞`-valued version, which is infinite when `q ∈ {0, 1}`
and `p ≠ q`. -/
noncomputable def klBerReal (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

lemma klBerReal_apply (p q : ℝ) :
    klBerReal p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

@[simp] lemma klBerReal_zero_left : klBerReal 0 q = -log (1 - q) := by simp [klBerReal]

@[simp] lemma klBerReal_one_left : klBerReal 1 q = -log q := by simp [klBerReal]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBerReal_one_sub (p q : ℝ) : klBerReal (1 - p) (1 - q) = klBerReal p q := by
  simp only [klBerReal, sub_sub_cancel]
  ring

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBerReal_self (p : ℝ) : klBerReal p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  simp [klBerReal, div_self hp, sub_ne_zero.2 hp1.symm]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBerReal_eq_of_ne (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBerReal p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBerReal, mul_log_div hq, mul_log_div (sub_ne_zero.2 hq1.symm)]

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
in `ℝ≥0∞`: it is `ENNReal.ofReal (klBerReal p q)`, except that it is infinite when `q ∈ {0, 1}`
and `p ≠ q`, where the Bernoulli measures are not absolutely continuous. -/
noncomputable def klBer (p q : ℝ) : ℝ≥0∞ :=
  if q = 0 then (if p = 0 then 0 else ∞)
  else if q = 1 then (if p = 1 then 0 else ∞)
  else ENNReal.ofReal (klBerReal p q)

lemma klBer_zero_right : klBer p 0 = if p = 0 then 0 else ∞ := by simp [klBer]

lemma klBer_one_right : klBer p 1 = if p = 1 then 0 else ∞ := by simp [klBer]

lemma klBer_eq_ofReal (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBer p q = ENNReal.ofReal (klBerReal p q) := by
  simp [klBer, hq, hq1]

lemma klBer_eq_top_iff : klBer p q = ∞ ↔ (q = 0 ∧ p ≠ 0) ∨ (q = 1 ∧ p ≠ 1) := by
  unfold klBer
  split_ifs <;> simp_all

lemma klBer_zero_left (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBer 0 q = ENNReal.ofReal (-log (1 - q)) := by
  rw [klBer_eq_ofReal hq hq1, klBerReal_zero_left]

lemma klBer_one_left (hq : q ≠ 0) (hq1 : q ≠ 1) : klBer 1 q = ENNReal.ofReal (-log q) := by
  rw [klBer_eq_ofReal hq hq1, klBerReal_one_left]

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBer_one_sub (p q : ℝ) : klBer (1 - p) (1 - q) = klBer p q := by
  simp only [klBer, klBerReal_one_sub]
  by_cases hq : q = 0
  · grind
  by_cases hq1 : q = 1 <;> grind

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBer_self (p : ℝ) : klBer p p = 0 := by
  simp [klBer]
  split_ifs <;> simp

end InformationTheory
