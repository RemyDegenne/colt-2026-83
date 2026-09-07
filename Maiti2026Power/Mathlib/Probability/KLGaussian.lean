/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Kullback-Leibler divergence between two real Gaussian measures with the same variance

We compute the Radon-Nikodym derivative, the log-likelihood ratio and the Kullback-Leibler
divergence between `gaussianReal m₁ v` and `gaussianReal m₂ v` for `v ≠ 0`.

## Main results

* `llr_gaussianReal`: the log-likelihood ratio of `gaussianReal m₁ v` with respect to
  `gaussianReal m₂ v` is almost everywhere equal to `y ↦ (m₁ - m₂) / v * (y - (m₁ + m₂) / 2)`.
* `klDiv_gaussianReal`: `klDiv (gaussianReal m₁ v) (gaussianReal m₂ v)
  = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * v))`.
-/

@[expose] public section

open MeasureTheory InformationTheory Real

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {m₁ m₂ : ℝ} {v : ℝ≥0}

/-- Two Gaussian measures with the same nonzero variance are mutually absolutely continuous. -/
lemma gaussianReal_absolutelyContinuous_gaussianReal (hv : v ≠ 0) :
    gaussianReal m₁ v ≪ gaussianReal m₂ v :=
  (gaussianReal_absolutelyContinuous m₁ hv).trans (gaussianReal_absolutelyContinuous' m₂ hv)

/-- The Radon-Nikodym derivative of a Gaussian measure with respect to another one with the same
nonzero variance is the ratio of the densities. -/
lemma rnDeriv_gaussianReal_gaussianReal (hv : v ≠ 0) :
    ∂(gaussianReal m₁ v)/∂(gaussianReal m₂ v)
      =ᵐ[gaussianReal m₁ v] fun y ↦ gaussianPDF m₁ v y / gaussianPDF m₂ v y := by
  refine (gaussianReal_absolutelyContinuous m₁ hv).ae_eq ?_
  have h := Measure.rnDeriv_withDensity_right (gaussianReal m₁ v) volume
    (measurable_gaussianPDF m₂ v).aemeasurable (ae_of_all _ fun x ↦ (gaussianPDF_pos _ hv x).ne')
    (ae_of_all _ fun _ ↦ gaussianPDF_ne_top)
  rw [← gaussianReal_of_var_ne_zero m₂ hv] at h
  filter_upwards [h, rnDeriv_gaussianReal m₁ v] with y hy₁ hy₂
  rw [hy₁, hy₂, ENNReal.div_eq_inv_mul]

/-- The log-likelihood ratio of a Gaussian measure with respect to another one with the same
nonzero variance is an affine function. -/
lemma llr_gaussianReal (hv : v ≠ 0) :
    llr (gaussianReal m₁ v) (gaussianReal m₂ v)
      =ᵐ[gaussianReal m₁ v] fun y ↦ (m₁ - m₂) / v * (y - (m₁ + m₂) / 2) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr hv.bot_lt
  filter_upwards [rnDeriv_gaussianReal_gaussianReal (m₁ := m₁) (m₂ := m₂) hv] with y hy
  rw [llr, hy, ENNReal.toReal_div, gaussianPDF, gaussianPDF,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal, gaussianPDFReal,
    mul_div_mul_left _ _ (by positivity), ← Real.exp_sub, Real.log_exp]
  field_simp
  ring

/-- The log-likelihood ratio between two Gaussian measures with the same nonzero variance is
integrable. -/
lemma integrable_llr_gaussianReal (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m₁ v) (gaussianReal m₂ v)) (gaussianReal m₁ v) := by
  refine Integrable.congr ?_ (llr_gaussianReal hv).symm
  have h_id : Integrable (fun y ↦ y) (gaussianReal m₁ v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  exact (h_id.sub (integrable_const ((m₁ + m₂) / 2))).const_mul _

/-- The Kullback-Leibler divergence between two Gaussian measures with the same nonzero
variance `v` and means `m₁`, `m₂` is `(m₁ - m₂) ^ 2 / (2 * v)`. -/
lemma klDiv_gaussianReal (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * v)) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_absolutelyContinuous_gaussianReal hv)
    (integrable_llr_gaussianReal hv), integral_congr_ae (llr_gaussianReal hv)]
  have h_id : Integrable (fun y ↦ y) (gaussianReal m₁ v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  rw [integral_const_mul, integral_sub h_id (integrable_const _), integral_id_gaussianReal,
    integral_const]
  simp only [probReal_univ, one_smul, add_sub_cancel_right]
  congr 1
  ring

/-- The Kullback-Leibler divergence between two standard Gaussian measures with means `m₁`, `m₂`
is `(m₁ - m₂) ^ 2 / 2`. -/
lemma klDiv_gaussianReal_one :
    klDiv (gaussianReal m₁ 1) (gaussianReal m₂ 1) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / 2) := by
  rw [klDiv_gaussianReal one_ne_zero]
  simp

end ProbabilityTheory
