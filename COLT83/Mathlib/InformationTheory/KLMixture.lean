/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Convexity of the Kullback–Leibler divergence in its second argument

For a finite measure `μ`, probability measures `ν i` and weights `c i ≥ 0` summing to `1`,
the Kullback–Leibler divergence is convex in its second argument:
`klDiv μ (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv μ (ν i)`.

The proof follows the concavity of the logarithm: on the set where all the Radon–Nikodym
derivatives `(ν i).rnDeriv μ` are finite and positive, `llr μ (∑ i, c i • ν i)` is bounded above
by `∑ i, c i * llr μ (ν i)` by Jensen's inequality.

## Main statements

* `MeasureTheory.Measure.rnDeriv_finsetSum`: the Radon–Nikodym derivative of a finite sum of finite
  measures is the sum of the Radon–Nikodym derivatives;
* `InformationTheory.isProbabilityMeasure_sum_smul`: a finite mixture of probability measures is a
  probability measure;
* `InformationTheory.klDiv_sum_smul_le`: convexity of `klDiv` in its second argument, for finite
  mixtures indexed by a `Fintype`;
* `InformationTheory.klDiv_finsetSum_smul_le`: the same statement, for sums over a `Finset`.
-/

set_option autoImplicit false

@[expose] public section

open Real MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

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

end MeasureTheory.Measure

namespace InformationTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ν : ι → Measure Ω} {c : ι → ℝ≥0}

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

/-- Auxiliary version of `klDiv_finsetSum_smul_le`, in which all the weights are nonzero. -/
lemma klDiv_finsetSum_smul_le_of_ne_zero [IsFiniteMeasure μ] [∀ i, IsProbabilityMeasure (ν i)]
    {s : Finset ι} (hc : ∑ i ∈ s, c i = 1) (hc0 : ∀ i ∈ s, c i ≠ 0) :
    klDiv μ (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i) := by
  classical
  -- if one of the divergences is infinite, the right-hand side is infinite
  by_cases h_top : ∃ i ∈ s, klDiv μ (ν i) = ∞
  · obtain ⟨i, hi, hi_top⟩ := h_top
    refine le_of_le_of_eq le_top (ENNReal.sum_eq_top.mpr ⟨i, hi, ?_⟩).symm
    rw [hi_top, ENNReal.mul_top (by simpa using hc0 i hi)]
  push Not at h_top
  have h_ac : ∀ i ∈ s, μ ≪ ν i := fun i hi ↦ (klDiv_ne_top_iff.mp (h_top i hi)).1
  have h_int : ∀ i ∈ s, Integrable (llr μ (ν i)) μ :=
    fun i hi ↦ (klDiv_ne_top_iff.mp (h_top i hi)).2
  set ξ : Measure Ω := ∑ i ∈ s, (c i : ℝ≥0∞) • ν i
  have : IsProbabilityMeasure ξ := isProbabilityMeasure_finsetSum_smul hc
  -- `μ` is absolutely continuous with respect to the mixture
  obtain ⟨i₀, hi₀⟩ : s.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hc]; exact one_ne_zero)
  have hμξ : μ ≪ ξ := by
    refine ((h_ac i₀ hi₀).smul_right (c := (c i₀ : ℝ≥0∞)) (by simpa using hc0 i₀ hi₀)).trans
      (Measure.absolutelyContinuous_of_le ?_)
    exact Finset.single_le_sum (f := fun i ↦ (c i : ℝ≥0∞) • ν i) (fun i _ ↦ bot_le) hi₀
  -- pointwise inequality, from the concavity of the logarithm
  have h_le : ∀ᵐ x ∂μ, llr μ ξ x ≤ ∑ i ∈ s, (c i : ℝ) * llr μ (ν i) x := by
    filter_upwards [Measure.rnDeriv_finsetSum_smul s c ν μ, neg_llr hμξ,
      (Filter.eventually_all_finset s).mpr fun i hi ↦ neg_llr (h_ac i hi),
      (Filter.eventually_all_finset s).mpr fun i hi ↦ Measure.rnDeriv_pos' (h_ac i hi),
      (Filter.eventually_all_finset s).mpr fun i _ ↦ Measure.rnDeriv_ne_top (ν i) μ]
      with x hx hx_neg hx_neg_i hx_pos hx_top
    have h_sum : (ξ.rnDeriv μ x).toReal = ∑ i ∈ s, (c i : ℝ) * ((ν i).rnDeriv μ x).toReal := by
      rw [hx, ENNReal.toReal_sum fun i hi ↦ ENNReal.mul_ne_top ENNReal.coe_ne_top (hx_top i hi)]
      simp [ENNReal.toReal_mul]
    have h_jensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := s)
      (w := fun i ↦ (c i : ℝ)) (p := fun i ↦ ((ν i).rnDeriv μ x).toReal)
      (fun i _ ↦ (c i).coe_nonneg) (by exact_mod_cast hc)
      (fun i hi ↦ ENNReal.toReal_pos (hx_pos i hi).ne' (hx_top i hi))
    simp only [smul_eq_mul] at h_jensen
    rw [← h_sum] at h_jensen
    have h1 : llr μ ξ x = -llr ξ μ x := by rw [← hx_neg, Pi.neg_apply, neg_neg]
    have h2 : ∀ i ∈ s, llr μ (ν i) x = -llr (ν i) μ x := fun i hi ↦ by
      rw [← hx_neg_i i hi, Pi.neg_apply, neg_neg]
    rw [h1, Finset.sum_congr rfl fun i hi ↦ by rw [h2 i hi]]
    simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff]
    exact h_jensen
  -- integrability of the log-likelihood ratio with respect to the mixture
  have h_int_sum : Integrable (fun x ↦ ∑ i ∈ s, (c i : ℝ) * llr μ (ν i) x) μ :=
    integrable_finsetSum s fun i hi ↦ (h_int i hi).const_mul _
  have h_int_ξ : Integrable (llr μ ξ) μ := by
    refine Integrable.mono'
      (h_int_sum.abs.add (Measure.integrable_toReal_rnDeriv (μ := ξ) (ν := μ)))
      (measurable_llr _ _).aestronglyMeasurable ?_
    filter_upwards [h_le, neg_llr hμξ] with x hx hx_neg
    have h1 : -llr μ ξ x = log (ξ.rnDeriv μ x).toReal := by rw [← Pi.neg_apply, hx_neg]; rfl
    have h2 := Real.log_le_self (ENNReal.toReal_nonneg (a := ξ.rnDeriv μ x))
    rw [Pi.add_apply, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [abs_nonneg (∑ i ∈ s, (c i : ℝ) * llr μ (ν i) x)]
    · linarith [le_abs_self (∑ i ∈ s, (c i : ℝ) * llr μ (ν i) x),
        ENNReal.toReal_nonneg (a := ξ.rnDeriv μ x)]
  -- conclusion
  have hc' : ∑ i ∈ s, (c i : ℝ) = 1 := by exact_mod_cast hc
  have h_klDiv_ξ : klDiv μ ξ = ENNReal.ofReal (∫ x, llr μ ξ x ∂μ + 1 - μ.real univ) := by
    rw [klDiv_of_ac_of_integrable hμξ h_int_ξ, probReal_univ]
  have h_klDiv_i : ∀ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i)
      = ENNReal.ofReal ((c i : ℝ) * (∫ x, llr μ (ν i) x ∂μ + 1 - μ.real univ)) := fun i hi ↦ by
    rw [klDiv_of_ac_of_integrable (h_ac i hi) (h_int i hi), probReal_univ,
      ENNReal.ofReal_mul (c i).coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have h_nonneg : ∀ i ∈ s, 0 ≤ (c i : ℝ) * (∫ x, llr μ (ν i) x ∂μ + 1 - μ.real univ) := by
    intro i hi
    refine mul_nonneg (c i).coe_nonneg ?_
    have := integral_llr_add_sub_measure_univ_nonneg (h_ac i hi) (h_int i hi)
    rwa [probReal_univ] at this
  have h_rhs : ∑ i ∈ s, (c i : ℝ) * (∫ x, llr μ (ν i) x ∂μ + 1 - μ.real univ)
      = ∑ i ∈ s, (c i : ℝ) * ∫ x, llr μ (ν i) x ∂μ + 1 - μ.real univ := by
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hc', one_mul]
  rw [h_klDiv_ξ, Finset.sum_congr rfl h_klDiv_i, ← ENNReal.ofReal_sum_of_nonneg h_nonneg, h_rhs]
  refine ENNReal.ofReal_le_ofReal ?_
  gcongr
  calc ∫ x, llr μ ξ x ∂μ ≤ ∫ x, ∑ i ∈ s, (c i : ℝ) * llr μ (ν i) x ∂μ :=
        integral_mono_ae h_int_ξ h_int_sum h_le
    _ = ∑ i ∈ s, (c i : ℝ) * ∫ x, llr μ (ν i) x ∂μ := by
        rw [integral_finsetSum s fun i hi ↦ (h_int i hi).const_mul _]
        simp_rw [integral_const_mul]

/-- **Convexity of the Kullback–Leibler divergence in its second argument**, for a finite mixture
indexed by a `Finset`: for a finite measure `μ`, probability measures `ν i` and nonnegative weights
`c i` summing to `1`, `klDiv μ (∑ i ∈ s, c i • ν i) ≤ ∑ i ∈ s, c i * klDiv μ (ν i)`. -/
lemma klDiv_finsetSum_smul_le [IsFiniteMeasure μ] [∀ i, IsProbabilityMeasure (ν i)]
    {s : Finset ι} (hc : ∑ i ∈ s, c i = 1) :
    klDiv μ (∑ i ∈ s, (c i : ℝ≥0∞) • ν i) ≤ ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i) := by
  classical
  have h1 : ∑ i ∈ s, (c i : ℝ≥0∞) • ν i = ∑ i ∈ s with c i ≠ 0, (c i : ℝ≥0∞) • ν i := by
    refine (Finset.sum_filter_of_ne (p := fun i ↦ c i ≠ 0) fun i _ h hci ↦ h ?_).symm
    simp [hci]
  have h2 : ∑ i ∈ s, (c i : ℝ≥0∞) * klDiv μ (ν i)
      = ∑ i ∈ s with c i ≠ 0, (c i : ℝ≥0∞) * klDiv μ (ν i) := by
    refine (Finset.sum_filter_of_ne (p := fun i ↦ c i ≠ 0) fun i _ h hci ↦ h ?_).symm
    simp [hci]
  rw [h1, h2]
  refine klDiv_finsetSum_smul_le_of_ne_zero ?_ fun i hi ↦ (Finset.mem_filter.mp hi).2
  rw [Finset.sum_filter_ne_zero, hc]

/-- **Convexity of the Kullback–Leibler divergence in its second argument**: for a finite measure
`μ`, probability measures `ν i` and nonnegative weights `c i` summing to `1`,
`klDiv μ (∑ i, c i • ν i) ≤ ∑ i, c i * klDiv μ (ν i)`. -/
theorem klDiv_sum_smul_le [Fintype ι] [IsFiniteMeasure μ] [∀ i, IsProbabilityMeasure (ν i)]
    (hc : ∑ i, c i = 1) :
    klDiv μ (∑ i, (c i : ℝ≥0∞) • ν i) ≤ ∑ i, (c i : ℝ≥0∞) * klDiv μ (ν i) :=
  klDiv_finsetSum_smul_le hc

end InformationTheory
