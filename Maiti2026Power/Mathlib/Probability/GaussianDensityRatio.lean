/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Density of a shifted Gaussian with respect to the standard Gaussian

* `gaussianPDFReal_eq_mul_exp`: the pointwise identity
  `gaussianPDFReal m 1 y = gaussianPDFReal 0 1 y * exp (y m - m² / 2)`;
* `gaussianReal_eq_withDensity_exp`: `N(m, 1) = N(0, 1).withDensity (y ↦ exp (y m - m² / 2))`;
* `measurable_gaussianDensityRatio`: joint measurability of the density ratio in `(m, y)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Pointwise identity between the densities of `N(m, 1)` and `N(0, 1)`:
`gaussianPDFReal m 1 y = gaussianPDFReal 0 1 y * exp (y m - m² / 2)`. -/
lemma gaussianPDFReal_eq_mul_exp (m y : ℝ) :
    gaussianPDFReal m 1 y = gaussianPDFReal 0 1 y * rexp (y * m - m ^ 2 / 2) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The density of `N(m, 1)` with respect to `N(0, 1)`: `y ↦ exp (y m - m² / 2)`. -/
lemma gaussianReal_eq_withDensity_exp (m : ℝ) :
    gaussianReal m 1 =
      (gaussianReal 0 1).withDensity (fun y ↦ ENNReal.ofReal (rexp (y * m - m ^ 2 / 2))) := by
  have hg : Measurable fun y : ℝ ↦ ENNReal.ofReal (rexp (y * m - m ^ 2 / 2)) := by fun_prop
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul volume (measurable_gaussianPDF 0 1) hg]
  congr 1
  ext y
  rw [Pi.mul_apply, gaussianPDF, gaussianPDF, gaussianPDFReal_eq_mul_exp m y,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]

/-- Joint measurability of the density ratio in `(m, y)`. -/
lemma measurable_gaussianDensityRatio :
    Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (rexp (p.2 * p.1 - p.1 ^ 2 / 2)) := by
  fun_prop

end ProbabilityTheory
