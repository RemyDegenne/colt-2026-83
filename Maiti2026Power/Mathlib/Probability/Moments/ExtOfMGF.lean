/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.ComplexMGF

/-!
# Moment generating functions determine distributions

If two random variables have the same moment generating function, and that function is finite in a
neighbourhood of `0`, then they have the same law. This closes the TODO of Mathlib's
`Mathlib/Probability/Moments/ComplexMGF.lean` ("Prove that if two random variables have the same
`mgf`, then they have the same `complexMGF`"), which only proves the equality of the `complexMGF`
on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}` (`eqOn_complexMGF_of_mgf`).

The observation is that no analytic continuation beyond that strip is needed: as soon as the strip
contains the imaginary axis, which is exactly the hypothesis that the mgf is finite in a
neighbourhood of `0`, the equality of the `complexMGF` there is the equality of the characteristic
functions, and `Measure.ext_of_charFun` concludes.

## Main results

* `MeasureTheory.Measure.ext_of_eqOn_mgf`: if the moment generating functions of `X` and `Y` are
  finite in a neighbourhood of `0` and `mgf X μ =ᶠ[𝓝 0] mgf Y μ'`, then `μ.map X = μ'.map Y`.
  Agreeing near `0` is enough: the analytic continuation only has to reach the imaginary axis.
* `MeasureTheory.Measure.ext_of_mgf_eq`: the version with `mgf X μ = mgf Y μ'` everywhere.
* `MeasureTheory.Measure.ext_of_mgf_id_eq`: the version for two measures on `ℝ`.
-/

@[expose] public section

open MeasureTheory Complex

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

/-- **Moment generating functions determine distributions**, local form: if the moment generating
functions of `X` and `Y` are finite in a neighbourhood of `0` and agree near `0`, then `X` and `Y`
have the same law. -/
theorem _root_.MeasureTheory.Measure.ext_of_eqOn_mgf [IsProbabilityMeasure μ] [IsFiniteMeasure μ']
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (hX0 : 0 ∈ interior (integrableExpSet X μ)) (hY0 : 0 ∈ interior (integrableExpSet Y μ'))
    (h : mgf X μ =ᶠ[nhds 0] mgf Y μ') :
    μ.map X = μ'.map Y := by
  have : IsProbabilityMeasure (μ.map X) := inferInstance
  have : IsFiniteMeasure (μ'.map Y) := by
    constructor
    rw [Measure.map_apply_of_aemeasurable hY MeasurableSet.univ]
    exact measure_lt_top _ _
  -- the common vertical strip on which both `complexMGF` are analytic
  set S : Set ℝ := interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ') with hS
  set T : Set ℂ := {z : ℂ | z.re ∈ S} with hT
  have hS0 : (0 : ℝ) ∈ S := ⟨hX0, hY0⟩
  have hSconv : Convex ℝ S :=
    convex_integrableExpSet.interior.inter convex_integrableExpSet.interior
  have hTconn : IsPreconnected T := (hSconv.linear_preimage Complex.reLm).isPreconnected
  have hXan : AnalyticOnNhd ℂ (complexMGF X μ) T :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hz.1
  have hYan : AnalyticOnNhd ℂ (complexMGF Y μ') T :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hz.2
  -- the two functions agree frequently near `0`, along the real axis
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, complexMGF X μ z = complexMGF Y μ' z := by
    have hreal : ∃ᶠ x : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ, complexMGF X μ x = complexMGF Y μ' x := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [h.filter_mono nhdsWithin_le_nhds] with x hx
      rw [complexMGF_ofReal, complexMGF_ofReal, hx]
    rw [Filter.frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ by simp [hx_eq n]⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    refine ⟨?_, by simpa using hx_tendsto.2⟩
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx_tendsto.1
    simpa [Function.comp_def] using this
  have hEqOn : Set.EqOn (complexMGF X μ) (complexMGF Y μ') T :=
    hXan.eqOn_of_preconnected_of_frequently_eq hYan hTconn (z₀ := 0) (by simp [hT, hS0]) hfreq
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  exact hEqOn (by simp [hT, hS0])

/-- **Moment generating functions determine distributions**: if two random variables have the same
moment generating function, and it is finite in a neighbourhood of `0`, then they have the same
law. -/
theorem _root_.MeasureTheory.Measure.ext_of_mgf_eq [IsProbabilityMeasure μ] [IsFiniteMeasure μ']
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (h0 : 0 ∈ interior (integrableExpSet X μ)) (h : mgf X μ = mgf Y μ') :
    μ.map X = μ'.map Y :=
  Measure.ext_of_eqOn_mgf hX hY h0 (by rwa [← integrableExpSet_eq_of_mgf h])
    (Filter.Eventually.of_forall fun x ↦ congrFun h x)

/-- **Moment generating functions determine distributions**, for two measures on `ℝ`. -/
theorem _root_.MeasureTheory.Measure.ext_of_mgf_id_eq {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsFiniteMeasure μ'] (h0 : 0 ∈ interior (integrableExpSet id μ))
    (h : mgf id μ = mgf id μ') :
    μ = μ' := by
  simpa using Measure.ext_of_mgf_eq aemeasurable_id aemeasurable_id h0 h

end ProbabilityTheory
