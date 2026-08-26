/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Probability.CondDistrib
public import LeanMachineLearning.SequentialLearning.Means
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditionally sub-Gaussian variables from constant conditional laws

`HasCondDistrib.hasCondSubgaussianMGF_of_const`: if the conditional distribution of `W` given
`Z` is a constant law `ν` which is sub-Gaussian with variance proxy `c`, then `W` is conditionally
sub-Gaussian given `σ(Z)` with variance proxy `c` (uses `HasCondDistrib.condExp_comp_eq` from
LeanMachineLearning).
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- If the conditional distribution of `W` given `Z` is a constant law `ν` which is sub-Gaussian
with variance proxy `c`, then `W` is conditionally sub-Gaussian given `σ(Z)` with variance
proxy `c`. -/
lemma HasCondDistrib.hasCondSubgaussianMGF_of_const [StandardBorelSpace Ω] {W : Ω → ℝ}
    {Z : Ω → 𝓧} {ν : Measure ℝ} [IsFiniteMeasure ν] (h : HasCondDistrib W Z (Kernel.const 𝓧 ν) P)
    (hW : Measurable W) (hZ : Measurable Z) {c : ℝ≥0} (hν : HasSubgaussianMGF (fun x ↦ x) c ν) :
    HasCondSubgaussianMGF (m𝓧.comap Z) hZ.comap_le W c P := by
  have hW : HasLaw W ν P := h.hasLaw_of_const
  have hint : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * W ω)) P := fun t ↦ by
    have := hν.integrable_exp_mul t
    rw [← hW.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hW.aemeasurable).1 this
  refine Kernel.HasSubgaussianMGF.of_rat (fun t ↦ ?_) fun q ↦ ?_
  · rw [condExpKernel_comp_trim]
    exact hint t
  · have hm : m𝓧.comap Z ≤ mΩ := hZ.comap_le
    have h1 := condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
      (f := fun ω ↦ exp ((q : ℝ) * W ω)) (by fun_prop) (hint q)
    have h2 : P[fun ω ↦ exp ((q : ℝ) * W ω) | m𝓧.comap Z] =ᵐ[P] fun _ ↦ mgf (fun x ↦ x) ν q := by
      have := h.condExp_comp_eq hZ (g := fun x ↦ exp ((q : ℝ) * x)) (by fun_prop) (hint q)
      filter_upwards [this] with ω hω
      rw [hω, Kernel.const_apply]
      rfl
    have h2' : P[fun ω ↦ exp ((q : ℝ) * W ω) | m𝓧.comap Z] =ᵐ[P.trim hm]
        fun _ ↦ mgf (fun x ↦ x) ν q :=
      (StronglyMeasurable.ae_eq_trim_iff hm stronglyMeasurable_condExp
        stronglyMeasurable_const).2 h2
    filter_upwards [h1, h2'] with ω hω1 hω2
    change ∫ y, exp ((q : ℝ) * W y) ∂condExpKernel P (m𝓧.comap Z) ω ≤ _
    rw [← hω1, hω2]
    exact hν.mgf_le q

end ProbabilityTheory
