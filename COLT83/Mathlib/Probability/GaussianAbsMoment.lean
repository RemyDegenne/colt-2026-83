/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import COLT83.Mathlib.Probability.MultivariateGaussian

/-!
# The absolute moment of a Gaussian and a lower bound on the expected norm of a Gaussian vector

* `integral_abs_gaussianReal`: `E|Z| = √(2 v / π)` for `Z ~ N(0, v)`;
* `sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian`: for `Y ~ N(0, S)` and nonnegative
  weights `c` with `∑ cᵢ² ≤ 1`, `E‖Y‖ ≥ ∑ cᵢ E|Yᵢ| = √(2/π) ∑ cᵢ √(Sᵢᵢ)`, by the pointwise
  Cauchy–Schwarz inequality `∑ cᵢ |yᵢ| ≤ ‖y‖`.
-/

@[expose] public section

open MeasureTheory Real Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

/-- `∫_0^∞ x e^{-b x²} dx = 1 / (2 b)`. -/
lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * rexp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun x ↦ -(2 * b)⁻¹ * rexp (-b * x ^ 2)) (x * rexp (-b * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ ↦ -b * x ^ 2) (-b * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (-b)
    have h2 : HasDerivAt (fun x ↦ -(2 * b)⁻¹ * rexp (-b * x ^ 2))
        (-(2 * b)⁻¹ * (rexp (-b * x ^ 2) * (-b * (2 * x)))) x :=
      h1.exp.const_mul (-(2 * b)⁻¹)
    refine h2.congr_deriv ?_
    field_simp
  have hint : IntegrableOn (fun x : ℝ ↦ x * rexp (-b * x ^ 2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have hlim : Tendsto (fun x : ℝ ↦ -(2 * b)⁻¹ * rexp (-b * x ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ -b * x ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop two_ne_zero).const_mul_atTop hb
      simpa [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp this
    have := (Real.tendsto_exp_atBot.comp h1).const_mul (-(2 * b)⁻¹)
    simpa [Function.comp_def] using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp

/-- `E|Z| = √(2 v / π)` for `Z ~ N(0, v)`. -/
lemma integral_abs_gaussianReal (v : ℝ≥0) : ∫ x, |x| ∂gaussianReal 0 v = √(2 * v / π) := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var]
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hfun : ∀ x : ℝ, gaussianPDFReal 0 v x • |x| =
      (fun y ↦ (√(2 * π * v))⁻¹ * (y * rexp (-(2 * (v : ℝ))⁻¹ * y ^ 2))) |x| := by
    intro x
    simp only [gaussianPDFReal_def, sub_zero, smul_eq_mul, sq_abs]
    rw [show -x ^ 2 / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * x ^ 2 by ring]
    ring
  simp_rw [hfun]
  rw [integral_comp_abs (f := fun y ↦ (√(2 * π * v))⁻¹ * (y * rexp (-(2 * (v : ℝ))⁻¹ * y ^ 2))),
    integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq (by positivity)]
  have h2v : (2 * (2 * (v : ℝ))⁻¹)⁻¹ = v := by field_simp
  rw [h2v, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  field_simp
  exact Real.sq_sqrt (by positivity)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- `E|Yᵢ| = √(2 Sᵢᵢ / π)` for `Y ~ N(0, S)`. -/
lemma integral_abs_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    ∫ x, |x i| ∂multivariateGaussian 0 S = √(2 * S i i / π) := by
  have h : MeasurePreserving (fun x : EuclideanSpace ℝ ι ↦ x i) (multivariateGaussian 0 S)
      (gaussianReal 0 (S i i).toNNReal) := by
    simpa using measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := i)
  have := integral_map (μ := multivariateGaussian 0 S) h.measurable.aemeasurable
    (f := fun y : ℝ ↦ |y|) (by fun_prop)
  rw [← this, h.map_eq, integral_abs_gaussianReal]
  simp [Real.coe_toNNReal _ hS.diag_nonneg]

/-- **Lower bound on the expected norm of a Gaussian vector**: for `Y ~ N(0, S)` and
nonnegative weights `c` with `∑ cᵢ² ≤ 1`, `√(2/π) ∑ cᵢ √(Sᵢᵢ) = ∑ cᵢ E|Yᵢ| ≤ E‖Y‖`. -/
lemma sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian (hS : S.PosSemidef) {c : ι → ℝ}
    (hc0 : ∀ i, 0 ≤ c i) (hc : ∑ i, c i ^ 2 ≤ 1) :
    √(2 / π) * ∑ i, c i * √(S i i) ≤ ∫ x, ‖x‖ ∂multivariateGaussian 0 S := by
  have hpt : ∀ x : EuclideanSpace ℝ ι, ∑ i, c i * |x i| ≤ ‖x‖ := by
    intro x
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c fun i ↦ |x i|
    have h2 : ∑ i, |x i| ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [sq_abs]
    have h3 : (∑ i, c i * |x i|) ^ 2 ≤ ‖x‖ ^ 2 := by
      calc (∑ i, c i * |x i|) ^ 2 ≤ (∑ i, c i ^ 2) * ∑ i, |x i| ^ 2 := h1
        _ ≤ 1 * ‖x‖ ^ 2 := by rw [h2]; gcongr
        _ = ‖x‖ ^ 2 := one_mul _
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hc0 i) (abs_nonneg _))
      (norm_nonneg _) two_ne_zero).1 h3
  have hint : ∀ i, Integrable (fun x : EuclideanSpace ℝ ι ↦ |x i|) (multivariateGaussian 0 S) :=
    fun i ↦ ((memLp_two_eval_multivariateGaussian 0 S i).integrable one_le_two).abs
  calc √(2 / π) * ∑ i, c i * √(S i i)
      = ∑ i, c i * ∫ x, |x i| ∂multivariateGaussian 0 S := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [integral_abs_eval_multivariateGaussian hS i, show 2 * S i i / π = 2 / π * S i i by ring,
          Real.sqrt_mul (by positivity)]
        ring
    _ = ∫ x, ∑ i, c i * |x i| ∂multivariateGaussian 0 S := by
        rw [integral_finsetSum _ fun i _ ↦ (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∫ x, ‖x‖ ∂multivariateGaussian 0 S :=
        integral_mono (integrable_finsetSum _ fun i _ ↦ (hint i).const_mul _)
          IsGaussian.integrable_id.norm hpt

end ProbabilityTheory
