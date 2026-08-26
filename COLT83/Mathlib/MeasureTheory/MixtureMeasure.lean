/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite mixtures of measures

* `MeasureTheory.isProbabilityMeasure_finsetSum_smul`, `isProbabilityMeasure_sum_smul`: a finite
  mixture `∑ i, c i • ν i` of probability measures with weights summing to `1` is a probability
  measure;
* `MeasureTheory.Measure.rnDeriv_finsetSum`, `rnDeriv_finsetSum_smul`: the Radon–Nikodym
  derivative of a finite mixture is the mixture of the Radon–Nikodym derivatives.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

section probability

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ν : ι → Measure Ω} {c : ι → ℝ≥0}

/-- A finite mixture of probability measures, with weights summing to `1`, is a probability
measure. -/
lemma isProbabilityMeasure_finsetSum_smul [∀ i, IsProbabilityMeasure (ν i)] {s : Finset ι}
    (hc : ∑ i ∈ s, c i = 1) :
    IsProbabilityMeasure (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) where
  measure_univ := by
    simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, hc, ENNReal.coe_one]

/-- A finite mixture of probability measures, with weights summing to `1`, is a probability
measure. -/
lemma isProbabilityMeasure_sum_smul [Fintype ι] [∀ i, IsProbabilityMeasure (ν i)]
    (hc : ∑ i, c i = 1) :
    IsProbabilityMeasure (∑ i, (c i : ℝ≥0∞) • ν i) :=
  isProbabilityMeasure_finsetSum_smul hc

end probability

namespace Measure

variable {α ι : Type*} {mα : MeasurableSpace α}

/-- The Radon–Nikodym derivative of a finite sum of finite measures is the sum of the
Radon–Nikodym derivatives. -/
lemma rnDeriv_finsetSum (s : Finset ι) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)]
    (μ : Measure α) [SigmaFinite μ] :
    (∑ i ∈ s, ν i).rnDeriv μ =ᵐ[μ] ∑ i ∈ s, (ν i).rnDeriv μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (rnDeriv_add' _ _ _).trans (Filter.EventuallyEq.rfl.add ih)

/-- The Radon–Nikodym derivative of a finite mixture `∑ i ∈ s, c i • ν i` of finite measures
with respect to `μ` is the mixture of the Radon–Nikodym derivatives. -/
lemma rnDeriv_finsetSum_smul (s : Finset ι) (c : ι → ℝ≥0) (ν : ι → Measure α)
    [∀ i, IsFiniteMeasure (ν i)] (μ : Measure α) [SigmaFinite μ] :
    (∑ i ∈ s, (c i : ℝ≥0∞) • ν i).rnDeriv μ
      =ᵐ[μ] fun x ↦ ∑ i ∈ s, (c i : ℝ≥0∞) * (ν i).rnDeriv μ x := by
  have : ∀ i, IsFiniteMeasure ((c i : ℝ≥0∞) • ν i) :=
    fun i ↦ Measure.smul_finite _ ENNReal.coe_ne_top
  filter_upwards [rnDeriv_finsetSum s (fun i ↦ (c i : ℝ≥0∞) • ν i) μ,
    (Filter.eventually_all_finset s).mpr
      fun i _ ↦ rnDeriv_smul_left_of_ne_top (ν i) μ (ENNReal.coe_ne_top (r := c i))]
    with x hx hx_smul
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hx_smul i hi, Pi.smul_apply, smul_eq_mul]

end Measure

end MeasureTheory
