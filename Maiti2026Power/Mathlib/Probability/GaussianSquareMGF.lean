/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubExponential

/-!
# The moment generating function of the square of a Gaussian variable

* `integral_exp_quadratic`: `∫ exp (b x² + c x + d) dx = √(π / -b) exp (d - c² / (4b))` for `b < 0`.
* `integral_exp_mul_sq_gaussianReal`: for `X ~ N(m, v)` and `2 v a < 1`,
  `E[exp (a X²)] = (1 - 2 v a)^(-1/2) exp (m² a / (1 - 2 v a))`.
* `hasSubexponentialMGF_sq_sub_gaussianReal`: `X² - (m² + v)` is sub-exponential with parameters
  `(8 (v² + m² v), 4 v)`.
* `hasSubexponentialMGF_norm_sq_sub_stdGaussian`: for a standard Gaussian vector `g` in `ℝ^d`,
  `‖g‖² - d` is sub-exponential with parameters `(8 d, 4)`, and the chi-square tail bounds
  `measureReal_norm_sq_sub_ge_le_stdGaussian`, `measureReal_norm_sq_ge_le_stdGaussian`.
* `Real.exp_le_one_add_add_sq_div_two_of_nonpos`: `exp x ≤ 1 + x + x² / 2` for `x ≤ 0`.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal NNReal

/-- For `x ≤ 0`, `exp x ≤ 1 + x + x ^ 2 / 2`. -/
lemma Real.exp_le_one_add_add_sq_div_two_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    exp x ≤ 1 + x + x ^ 2 / 2 := by
  have h1 : 1 + (-x) + (-x) ^ 2 / 2 ≤ exp (-x) := quadratic_le_exp_of_nonneg (by linarith)
  have h2 : 0 < 1 + x + x ^ 2 / 2 := by nlinarith [sq_nonneg (1 + x)]
  have h3 : 0 < 1 + (-x) + (-x) ^ 2 / 2 := by nlinarith [sq_nonneg (1 - x)]
  rw [exp_neg] at h1
  have h4 : exp x ≤ (1 + (-x) + (-x) ^ 2 / 2)⁻¹ := by
    rw [le_inv_comm₀ (exp_pos x) h3]
    exact h1
  refine h4.trans ?_
  rw [inv_le_iff_one_le_mul₀ h3]
  nlinarith [pow_nonneg (sq_nonneg x) 2]

section Quadratic

lemma exp_quadratic_eq {b : ℝ} (hb : b ≠ 0) (c d x : ℝ) :
    exp (b * x ^ 2 + c * x + d)
      = exp (-(-b) * (x + c / (2 * b)) ^ 2) * exp (d - c ^ 2 / (4 * b)) := by
  rw [← exp_add]
  congr 1
  field_simp
  ring

lemma integrable_exp_quadratic {b : ℝ} (hb : b < 0) (c d : ℝ) :
    Integrable fun x : ℝ ↦ exp (b * x ^ 2 + c * x + d) := by
  have h := ((integrable_exp_neg_mul_sq (neg_pos.2 hb)).comp_add_right (c / (2 * b))).mul_const
    (exp (d - c ^ 2 / (4 * b)))
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  exact (exp_quadratic_eq hb.ne c d x).symm

/-- The Gaussian integral of a quadratic exponent. -/
lemma integral_exp_quadratic {b : ℝ} (hb : b < 0) (c d : ℝ) :
    ∫ x : ℝ, exp (b * x ^ 2 + c * x + d) = √(π / -b) * exp (d - c ^ 2 / (4 * b)) := by
  simp_rw [exp_quadratic_eq hb.ne c d]
  rw [integral_mul_const]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun y ↦ exp (-(-b) * y ^ 2))
    (c / (2 * b))
  rw [this, integral_gaussian]

end Quadratic

namespace ProbabilityTheory

section GaussianSquare

lemma integrable_exp_mul_sq_gaussianReal (m : ℝ) (v : ℝ≥0) {a : ℝ} (ha : 2 * v * a < 1) :
    Integrable (fun x ↦ exp (a * x ^ 2)) (gaussianReal m v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var]
    exact integrable_dirac (by simp)
  rw [gaussianReal_of_var_ne_zero m hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF m v) (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF, gaussianPDFReal, smul_eq_mul]
  have hv' : (0 : ℝ) < v := by positivity
  have hb : a - 1 / (2 * v) < 0 := by
    rw [sub_neg, lt_div_iff₀ (by positivity)]
    linarith
  have := (integrable_exp_quadratic hb (m / v) (-(m ^ 2 / (2 * v)))).const_mul (√(2 * π * v))⁻¹
  refine this.congr (ae_of_all _ fun x ↦ ?_)
  simp only
  rw [mul_assoc ((√(2 * π * (v : ℝ)))⁻¹), ← exp_add]
  congr 2
  field_simp
  ring

/-- **MGF of the square of a Gaussian variable**: for `X ~ N(m, v)` and `2 v a < 1`,
`E[exp (a X²)] = (1 - 2 v a)^(-1/2) exp (m² a / (1 - 2 v a))`. -/
lemma integral_exp_mul_sq_gaussianReal (m : ℝ) (v : ℝ≥0) {a : ℝ} (ha : 2 * v * a < 1) :
    ∫ x, exp (a * x ^ 2) ∂gaussianReal m v
      = (√(1 - 2 * v * a))⁻¹ * exp (m ^ 2 * a / (1 - 2 * v * a)) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac]
    simp only [NNReal.coe_zero, mul_zero, zero_mul, sub_zero, Real.sqrt_one, inv_one, one_mul,
      div_one]
    ring_nf
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [gaussianPDFReal, smul_eq_mul]
  have hv' : (0 : ℝ) < v := by positivity
  have hb : a - 1 / (2 * v) < 0 := by
    rw [sub_neg, lt_div_iff₀ (by positivity)]
    linarith
  have hb' : 0 < -(a - 1 / (2 * v)) := by linarith
  have h1v : 0 < 1 - 2 * v * a := by linarith
  have hne : 1 - 2 * v * a ≠ 0 := h1v.ne'
  have hb2 : -(a - 1 / (2 * v)) = (1 - 2 * v * a) / (2 * v) := by
    field_simp
    ring
  have hb3 : a - 1 / (2 * v) = -((1 - 2 * v * a) / (2 * v)) := by
    field_simp
    ring
  have h1 : ∀ x, (√(2 * π * v))⁻¹ * exp (-(x - m) ^ 2 / (2 * v)) * exp (a * x ^ 2)
      = (√(2 * π * v))⁻¹
        * exp ((a - 1 / (2 * v)) * x ^ 2 + (m / v) * x + (-(m ^ 2 / (2 * v)))) := by
    intro x
    rw [mul_assoc, ← exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_exp_quadratic hb]
  have h2 : (√(2 * π * v))⁻¹ * √(π / -(a - 1 / (2 * v))) = (√(1 - 2 * v * a))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
    congr 1
    rw [hb2, div_div_eq_mul_div]
    field_simp
  have h3 : -(m ^ 2 / (2 * v)) - (m / v) ^ 2 / (4 * (a - 1 / (2 * v)))
      = m ^ 2 * a / (1 - 2 * v * a) := by
    rw [hb3]
    field_simp
    ring
  rw [← mul_assoc, h2, h3]

/-- For `|ν| ≤ 1 / 2`, `-log (1 - ν) / 2 - ν / 2 ≤ ν ^ 2`. -/
lemma neg_log_one_sub_div_two_sub_le_sq {ν : ℝ} (hν : |ν| ≤ 1 / 2) :
    -log (1 - ν) / 2 - ν / 2 ≤ ν ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := ν) (by linarith [abs_nonneg ν]) 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one, Nat.reduceAdd] at h
  have h2 : |ν| ^ 2 / (1 - |ν|) ≤ 2 * ν ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_abs ν, mul_nonneg (sq_nonneg ν) (by linarith : (0 : ℝ) ≤ 1 - 2 * |ν|)]
  have h3 := (neg_le_abs _).trans (h.trans h2)
  linarith

/-- For `|ν| ≤ 1 / 2`, `1 / (1 - ν) ≤ 2`. -/
lemma one_div_one_sub_le_two {ν : ℝ} (hν : |ν| ≤ 1 / 2) : 1 / (1 - ν) ≤ 2 := by
  have := (le_abs_self ν).trans hν
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **The centered square of a Gaussian variable is sub-exponential**: for `X ~ N(m, v)`,
`X² - (m² + v)` has sub-exponential parameters `(8 (v² + m² v), 4 v)`. -/
lemma hasSubexponentialMGF_sq_sub_gaussianReal (m : ℝ) (v : ℝ≥0) :
    HasSubexponentialMGF (fun x ↦ x ^ 2 - (m ^ 2 + v)) (8 * (v ^ 2 + m ^ 2 * v)) (4 * v)
      (gaussianReal m v) := by
  have hv := v.coe_nonneg
  have key : ∀ a : ℝ, 4 * v * |a| ≤ 1 → 2 * v * a < 1 := by
    intro a ha
    nlinarith [le_abs_self a, abs_nonneg a]
  constructor
  · intro a ha
    have := (integrable_exp_mul_sq_gaussianReal m v (key a ha)).const_mul (exp (-(a * (m ^ 2 + v))))
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only
    rw [← exp_add]
    congr 1
    ring
  · intro a ha
    have hν : |2 * v * a| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      linarith
    have h1 : 0 < 1 - 2 * v * a := by linarith [key a ha]
    have hne : 1 - 2 * v * a ≠ 0 := h1.ne'
    have hmgf : mgf (fun x ↦ x ^ 2 - (m ^ 2 + v)) (gaussianReal m v) a
        = exp (-(a * (m ^ 2 + v)))
          * ((√(1 - 2 * v * a))⁻¹ * exp (m ^ 2 * a / (1 - 2 * v * a))) := by
      rw [mgf, ← integral_exp_mul_sq_gaussianReal m v (key a ha), ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only
      rw [← exp_add]
      congr 1
      ring
    have hsqrt : (√(1 - 2 * v * a))⁻¹ = exp (-(log (1 - 2 * v * a) / 2)) := by
      rw [exp_neg, ← Real.log_sqrt h1.le, exp_log (Real.sqrt_pos.2 h1)]
    rw [hmgf, hsqrt, ← exp_add, ← exp_add, exp_le_exp]
    have hi := neg_log_one_sub_div_two_sub_le_sq hν
    have h3 : m ^ 2 * a / (1 - 2 * v * a) - a * m ^ 2 ≤ 4 * m ^ 2 * v * a ^ 2 := by
      have e : m ^ 2 * a / (1 - 2 * v * a) - a * m ^ 2
          = 2 * m ^ 2 * v * a ^ 2 / (1 - 2 * v * a) := by
        rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
        ring
      rw [e, div_le_iff₀ h1]
      have h4 : 0 ≤ 1 - 2 * (2 * v * a) := by linarith [le_abs_self (2 * v * a)]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * m ^ 2 * v * a ^ 2) h4]
    nlinarith [hi, h3]

end GaussianSquare

section ChiSquare

variable {ι : Type*} [Fintype ι]

/-- **Chi-square variables are sub-exponential**, coordinate form: for i.i.d. standard Gaussian
coordinates `g i`, `∑ i, (g i ^ 2 - 1)` has sub-exponential parameters `(8 d, 4)`. -/
lemma hasSubexponentialMGF_sum_sq_sub_one_pi_gaussianReal :
    HasSubexponentialMGF (fun g : ι → ℝ ↦ ∑ i, (g i ^ 2 - 1)) (8 * Fintype.card ι) 4
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  have h_indep : iIndepFun (fun i (g : ι → ℝ) ↦ g i ^ 2 - 1)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ x ↦ x ^ 2 - 1) fun i ↦ by fun_prop
  have h := HasSubexponentialMGF.fun_sum_of_iIndepFun h_indep
    (V := fun _ ↦ 8) (b := 4) fun i ↦ ?_
  · simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h
  · have := hasSubexponentialMGF_sq_sub_gaussianReal 0 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, NNReal.coe_one, zero_add,
      one_pow, add_zero, mul_one] at this
    have hmap : (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun g : ι → ℝ ↦ g i)
        = gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).map_eq
    have h8 := HasSubexponentialMGF.of_map (X := fun x : ℝ ↦ x ^ 2 - 1) (Y := fun g : ι → ℝ ↦ g i)
      (μ := Measure.pi fun _ : ι ↦ gaussianReal 0 1) (V := 8) (b := 4)
      (measurable_pi_apply i).aemeasurable (by rw [hmap]; exact this)
    exact h8

/-- **Chi-square variables are sub-exponential**: for a standard Gaussian vector `g` in `ℝ^d`,
`‖g‖ ^ 2 - d` has sub-exponential parameters `(8 d, 4)`. -/
lemma hasSubexponentialMGF_norm_sq_sub_stdGaussian :
    HasSubexponentialMGF (fun g : EuclideanSpace ℝ ι ↦ ‖g‖ ^ 2 - Fintype.card ι)
      (8 * Fintype.card ι) 4 (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← map_pi_eq_stdGaussian, HasSubexponentialMGF.map_iff (by fun_prop) (by fun_prop)]
  refine hasSubexponentialMGF_sum_sq_sub_one_pi_gaussianReal.congr (ae_of_all _ fun g ↦ ?_)
  simp [Function.comp, EuclideanSpace.real_norm_sq_eq, Finset.sum_sub_distrib]

/-- **Chi-square tail bound**: for a standard Gaussian vector `g` in `ℝ^d` and `t ≥ 0`,
`P(‖g‖² - d ≥ t) ≤ exp (-min (t² / (16 d)) (t / 8))`. -/
lemma measureReal_norm_sq_sub_ge_le_stdGaussian [Nonempty ι] {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {g | t ≤ ‖g‖ ^ 2 - Fintype.card ι}
      ≤ exp (-min (t ^ 2 / (16 * Fintype.card ι)) (t / 8)) := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    positivity
  have := hasSubexponentialMGF_norm_sq_sub_stdGaussian (ι := ι).measure_ge_le ht
  refine this.trans (le_of_eq ?_)
  congr 3 <;> ring

/-- **Chi-square tail bound**, explicit form: for a standard Gaussian vector `g` in `ℝ^d` and
`δ ∈ (0, 1)`, `P(‖g‖² ≥ 2 d + 12 log (1 / δ)) ≤ δ`. -/
lemma measureReal_norm_sq_ge_le_stdGaussian [Nonempty ι] {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {g | 2 * Fintype.card ι + 12 * log (1 / δ) ≤ ‖g‖ ^ 2} ≤ δ := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 < d := by
    have := Fintype.card_pos (α := ι)
    positivity
  set L := log (1 / δ) with hL
  have hL0 : 0 < L := Real.log_pos (one_lt_one_div hδ.1 hδ.2)
  set t := max (4 * √(d * L)) (8 * L) with ht
  have ht0 : 0 ≤ t := le_max_of_le_right (by positivity)
  have hsub : {g : EuclideanSpace ℝ ι | 2 * d + 12 * L ≤ ‖g‖ ^ 2} ⊆ {g | t ≤ ‖g‖ ^ 2 - d} := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 : 4 * √(d * L) ≤ d + 4 * L := by
      rw [Real.sqrt_mul hd0.le]
      nlinarith [sq_nonneg (√d - 2 * √L), Real.sq_sqrt hd0.le, Real.sq_sqrt hL0.le,
        Real.sqrt_nonneg d, Real.sqrt_nonneg L]
    have : t ≤ d + 12 * L := max_le (by linarith) (by linarith)
    linarith
  calc (stdGaussian (EuclideanSpace ℝ ι)).real {g | 2 * d + 12 * L ≤ ‖g‖ ^ 2}
      ≤ (stdGaussian (EuclideanSpace ℝ ι)).real {g | t ≤ ‖g‖ ^ 2 - d} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ exp (-min (t ^ 2 / (16 * d)) (t / 8)) := measureReal_norm_sq_sub_ge_le_stdGaussian ht0
    _ ≤ exp (-L) := by
        gcongr
        refine le_min ?_ ?_
        · rw [le_div_iff₀ (mul_pos (by norm_num) hd0)]
          calc L * (16 * d) = (4 * √(d * L)) ^ 2 := by
                rw [mul_pow, Real.sq_sqrt (mul_nonneg hd0.le hL0.le)]
                ring
            _ ≤ t ^ 2 := by
                gcongr
                exact le_max_left _ _
        · rw [le_div_iff₀ (by norm_num)]
          linarith [le_max_right (4 * √(d * L)) (8 * L)]
    _ = δ := by rw [hL, exp_neg, exp_log (one_div_pos.2 hδ.1), one_div, inv_inv]

end ChiSquare

end ProbabilityTheory
