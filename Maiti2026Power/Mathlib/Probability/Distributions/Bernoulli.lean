/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals and densities of Bernoulli measures

For the Bernoulli measure `Ber(x, y, p) = p δₓ + (1 - p) δ_y` of Mathlib
(`ProbabilityTheory.bernoulliMeasure`, `p : unitInterval`):

* `lintegral_bernoulliMeasure`: `∫⁻ f ∂Ber(x, y, p) = p f x + (1 - p) f y`;
* `bernoulliMeasure_eq_withDensity`: for `x ≠ y` and `0 < q < 1`, `Ber(x, y, p)` has density
  `p / q` at `x` and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`; hence
  `Ber(x, y, p) ≪ Ber(x, y, q)` (`bernoulliMeasure_absolutelyContinuous`) and the
  Radon–Nikodym derivative is that density (`rnDeriv_bernoulliMeasure`);
* `bernoulliMeasure_apply_singleton_left`, `bernoulliMeasure_apply_singleton_right`: the masses
  of the two atoms.
-/

@[expose] public section

open MeasureTheory unitInterval
open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A density with respect to a Dirac measure only matters through its value at the atom. -/
lemma withDensity_dirac (a : α) (f : α → ℝ≥0∞) :
    (Measure.dirac a).withDensity f = f a • Measure.dirac a := by
  classical
  ext s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, MeasureTheory.restrict_dirac,
    Measure.dirac_apply' _ hs]
  split_ifs with h
  · rw [lintegral_dirac, Set.indicator_of_mem h, Pi.one_apply, mul_one]
  · rw [lintegral_zero_measure, Set.indicator_of_notMem h, mul_zero]

end MeasureTheory

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X} {p q : I}

/-- The coercion `unitInterval → ℝ≥0 → ℝ≥0∞` is `ENNReal.ofReal`. -/
lemma coe_toNNReal_eq_ofReal (p : I) : ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg p.2.1]
  rfl

lemma bernoulliMeasure_apply_singleton_left (hxy : x ≠ y) (p : I) :
    Ber(x, y, p) {x} = ENNReal.ofReal p := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton x) (Set.mem_singleton x)
    (by simpa using hxy.symm), coe_toNNReal_eq_ofReal]

lemma bernoulliMeasure_apply_singleton_right (hxy : x ≠ y) (p : I) :
    Ber(x, y, p) {y} = ENNReal.ofReal (1 - p) := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton y) (by simpa using hxy)
    (Set.mem_singleton y), coe_toNNReal_eq_ofReal, coe_symm_eq]

/-- The Lebesgue integral of a function against a Bernoulli measure. -/
lemma lintegral_bernoulliMeasure (x y : X) (p : I) (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  rw [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.smul_def, ENNReal.smul_def, coe_toNNReal_eq_ofReal,
    coe_toNNReal_eq_ofReal, coe_symm_eq, smul_eq_mul, smul_eq_mul]

/-- For `x ≠ y` and `0 < q < 1`, the Bernoulli measure `Ber(x, y, p)` has density `p / q` at `x`
and `(1 - p) / (1 - q)` at `y` with respect to `Ber(x, y, q)`. -/
lemma bernoulliMeasure_eq_withDensity [DecidableEq X] (hxy : x ≠ y) (p : I) (hq : (q : ℝ) ≠ 0)
    (hq1 : (q : ℝ) ≠ 1) :
    Ber(x, y, p) = Ber(x, y, q).withDensity
      (fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  have hq0 : (0 : ℝ) < q := lt_of_le_of_ne q.2.1 hq.symm
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (lt_of_le_of_ne q.2.2 hq1)
  have hq1'' : (1 : ℝ) - q ≠ 0 := hq1'.ne'
  rw [bernoulliMeasure_def, bernoulliMeasure_def, withDensity_add_measure]
  simp_rw [ENNReal.smul_def]
  rw [withDensity_smul_measure, withDensity_smul_measure, withDensity_dirac, withDensity_dirac,
    ite_eq_left rfl, ite_eq_right hxy.symm, smul_smul, smul_smul, coe_toNNReal_eq_ofReal,
    coe_toNNReal_eq_ofReal, coe_toNNReal_eq_ofReal, coe_toNNReal_eq_ofReal, coe_symm_eq,
    coe_symm_eq]
  congr 1 <;> congr 1
  · rw [← ENNReal.ofReal_mul hq0.le]
    congr 1
    field_simp
  · rw [← ENNReal.ofReal_mul hq1'.le]
    congr 1
    field_simp

/-- For `x ≠ y` and `0 < q < 1`, `Ber(x, y, p) ≪ Ber(x, y, q)`. -/
lemma bernoulliMeasure_absolutelyContinuous (hxy : x ≠ y) (p : I) (hq : (q : ℝ) ≠ 0)
    (hq1 : (q : ℝ) ≠ 1) :
    Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon–Nikodym derivative of `Ber(x, y, p)` with respect to `Ber(x, y, q)`. -/
lemma rnDeriv_bernoulliMeasure [DecidableEq X] (hxy : x ≠ y) (p : I) (hq : (q : ℝ) ≠ 0)
    (hq1 : (q : ℝ) ≠ 1) :
    Ber(x, y, p).rnDeriv Ber(x, y, q) =ᵐ[Ber(x, y, q)]
      fun z ↦ if z = x then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q)) := by
  rw [bernoulliMeasure_eq_withDensity hxy p hq hq1]
  exact Measure.rnDeriv_withDensity _
    (Measurable.ite (measurableSet_singleton x) measurable_const measurable_const)

end ProbabilityTheory
