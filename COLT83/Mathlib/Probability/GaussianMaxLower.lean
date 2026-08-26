/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import COLT83.Mathlib.Probability.GaussianMGF
public import COLT83.Mathlib.Order.CiSupFinite

/-!
# Lower bound on the expected maximum of i.i.d. standard Gaussians

* `mul_gaussianPDFReal_le_measureReal_Ici`: the Mills-ratio lower bound
  `t / (1 + t²) φ(t) ≤ P(ξ ≥ t)` for a standard Gaussian `ξ` and `t > 0`.
* `integral_posPart_gaussianReal_zero_one`: `E[max ξ 0] = 1 / √(2π)`.
* `integral_max_pi_gaussianReal`: `E[max ξ_i ξ_j] = 1 / √π` for two distinct coordinates of a
  product of standard Gaussians.
* `sqrt_log_div_four_le_integral_iSup_pi_gaussianReal`: for `m ≥ 2` i.i.d. standard Gaussians,
  `E[max_i ξ_i] ≥ √(log m) / 4`.
-/

@[expose] public section

open MeasureTheory Real Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

/-! ### The standard Gaussian density -/

/-- The standard Gaussian density: `φ x = exp (-x² / 2) / √(2π)`. -/
lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The standard Gaussian density is bounded by `1 / √(2π)`. -/
lemma gaussianPDFReal_zero_one_le (x : ℝ) : gaussianPDFReal 0 1 x ≤ (√(2 * π))⁻¹ := by
  rw [gaussianPDFReal_zero_one]
  calc (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) ≤ (√(2 * π))⁻¹ * 1 := by
        gcongr
        exact exp_le_one_iff.2 (by linarith [sq_nonneg x])
    _ = (√(2 * π))⁻¹ := mul_one _

/-- Derivative of the standard Gaussian density: `φ' x = -x φ x`. -/
lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun x ↦ -x ^ 2 / 2) (-(↑(2 : ℕ) * x ^ (2 - 1)) / 2) x :=
    ((hasDerivAt_pow 2 x).neg).div_const 2
  have hfun : gaussianPDFReal 0 1 = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) :=
    funext gaussianPDFReal_zero_one
  rw [hfun]
  exact (h.exp.const_mul (√(2 * π))⁻¹).congr_deriv (by push_cast; ring)

/-- The standard Gaussian density tends to `0` at `+∞`. -/
lemma tendsto_gaussianPDFReal_zero_one_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have := (tendsto_exp_neg_atTop_nhds_zero.comp h).const_mul (√(2 * π))⁻¹
  rw [mul_zero] at this
  refine this.congr fun x ↦ ?_
  simp only [Function.comp_apply, gaussianPDFReal_zero_one, neg_div]

/-! ### The Mills-ratio lower bound -/

/-- The Gaussian tail probability as an integral of the density over `Ioi t`. -/
lemma measureReal_Ici_gaussianReal_zero_one (t : ℝ) :
    (gaussianReal 0 1).real (Ici t) = ∫ x in Ioi t, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg 0 1)),
    restrict_Ioi_eq_restrict_Ici]

/-- Derivative of `-φ x / x` for `x > 0`: it equals `φ x (1 + 1 / x²)`. -/
lemma hasDerivAt_neg_gaussianPDFReal_div {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x / x)
      (gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)) x := by
  refine (((hasDerivAt_gaussianPDFReal_zero_one x).neg).div (hasDerivAt_id x)
    hx.ne').congr_deriv ?_
  simp only [id, Pi.neg_apply]
  field_simp
  ring

/-- `-φ x / x` tends to `0` at `+∞`. -/
lemma tendsto_neg_gaussianPDFReal_div_atTop :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x / x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x ↦ (√(2 * π))⁻¹ / x) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hx,
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  gcongr
  exact gaussianPDFReal_zero_one_le x

/-- `φ x (1 + 1 / x²)` is integrable on `Ioi t` for `t > 0`. -/
lemma integrableOn_gaussianPDFReal_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)) (Ioi t) := by
  refine ((integrable_gaussianPDFReal 0 1).restrict.const_mul (1 + 1 / t ^ 2)).mono' ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 1).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (by positivity)),
      mul_comm]
    gcongr
    exact gaussianPDFReal_nonneg 0 1 x

/-- The integral identity `∫ x in Ioi t, φ x (1 + 1 / x²) = φ t / t` for `t > 0`. -/
lemma integral_gaussianPDFReal_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi t, gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2) = gaussianPDFReal 0 1 t / t := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_neg_gaussianPDFReal_div ht).continuousAt.continuousWithinAt
    (fun x hx ↦ hasDerivAt_neg_gaussianPDFReal_div (ht.trans hx))
    (integrableOn_gaussianPDFReal_mul_Ioi ht) tendsto_neg_gaussianPDFReal_div_atTop]
  ring

/-- Mills-ratio lower bound: `t / (1 + t²) φ(t) ≤ P(ξ ≥ t)` for a standard Gaussian `ξ` and
`t > 0`. -/
lemma mul_gaussianPDFReal_le_measureReal_Ici {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * gaussianPDFReal 0 1 t ≤ (gaussianReal 0 1).real (Ici t) := by
  rw [measureReal_Ici_gaussianReal_zero_one]
  have h : gaussianPDFReal 0 1 t / t ≤ (1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x := by
    rw [← integral_gaussianPDFReal_mul_Ioi ht, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_gaussianPDFReal_mul_Ioi ht)
      ((integrable_gaussianPDFReal 0 1).restrict.const_mul _) measurableSet_Ioi fun x hx ↦ ?_
    have hx' : t < x := hx
    rw [mul_comm]
    gcongr
    exact gaussianPDFReal_nonneg 0 1 x
  calc t / (1 + t ^ 2) * gaussianPDFReal 0 1 t
      = t ^ 2 / (1 + t ^ 2) * (gaussianPDFReal 0 1 t / t) := by field_simp
    _ ≤ t ^ 2 / (1 + t ^ 2) * ((1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x) := by
        gcongr
    _ = ∫ x in Ioi t, gaussianPDFReal 0 1 x := by field_simp; ring

/-! ### Positive and negative parts of a standard Gaussian -/

/-- `∫ x in Ioi 0, x φ x = φ 0 = 1 / √(2π)`. -/
lemma integral_Ioi_mul_gaussianPDFReal_zero_one :
    ∫ x in Ioi 0, x * gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ := by
  have hderiv : ∀ x, HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x) (x * gaussianPDFReal 0 1 x) x :=
    fun x ↦ (hasDerivAt_gaussianPDFReal_zero_one x).neg.congr_deriv (by ring)
  have hint : IntegrableOn (fun x ↦ x * gaussianPDFReal 0 1 x) (Ioi 0) := by
    have : (fun x ↦ x * gaussianPDFReal 0 1 x) =
        fun x ↦ (√(2 * π))⁻¹ * (x * exp (-(1 / 2) * x ^ 2)) := by
      funext x
      rw [gaussianPDFReal_zero_one, show -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by ring]
      ring
    rw [this]
    exact ((integrable_mul_exp_neg_mul_sq (by norm_num)).const_mul _).integrableOn
  have htend : Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
    simpa using tendsto_gaussianPDFReal_zero_one_atTop.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun x _ ↦ hderiv x) hint htend]
  simp [gaussianPDFReal_zero_one]

/-- The expectation of the positive part of a standard Gaussian is `1 / √(2π)`. -/
lemma integral_posPart_gaussianReal_zero_one :
    ∫ x, max x 0 ∂gaussianReal 0 1 = (√(2 * π))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← integral_Ioi_mul_gaussianPDFReal_zero_one, ← integral_indicator measurableSet_Ioi]
  congr with x
  rw [indicator_apply, smul_eq_mul]
  split_ifs with hx
  · rw [max_eq_left (le_of_lt hx), mul_comm]
  · rw [max_eq_right (not_lt.1 hx), mul_zero]

/-- The expectation of the negative part of a standard Gaussian is `1 / √(2π)`. -/
lemma integral_negPart_gaussianReal_zero_one :
    ∫ x, max (-x) 0 ∂gaussianReal 0 1 = (√(2 * π))⁻¹ := by
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun x ↦ -x) (f := fun x ↦ max x 0)
    (by fun_prop) (by fun_prop)
  rw [gaussianReal_map_neg, neg_zero, integral_posPart_gaussianReal_zero_one] at h
  exact h.symm

/-- The expectation of the positive part of a `N(0, 2)` Gaussian is `1 / √π`. -/
lemma integral_posPart_gaussianReal_zero_two :
    ∫ x, max x 0 ∂gaussianReal 0 2 = (√π)⁻¹ := by
  have hmap : (gaussianReal 0 1).map (√2 * ·) = gaussianReal 0 2 := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [show ∀ x : ℝ, max (√2 * x) 0 = √2 * max x 0 from fun x ↦ by
    rw [mul_max_of_nonneg _ _ (sqrt_nonneg 2), mul_zero]]
  rw [integral_const_mul, integral_posPart_gaussianReal_zero_one,
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

/-! ### Expected maximum of two coordinates -/

variable {ι : Type*} [Fintype ι]

/-- The law of `x ↦ x i - x j` (`i ≠ j`) under a product of standard Gaussians is `N(0, 2)`. -/
lemma map_sub_eval_pi_gaussianReal {i j : ι} (hij : i ≠ j) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun x ↦ x i - x j) = gaussianReal 0 2 := by
  classical
  set a : EuclideanSpace ℝ ι := EuclideanSpace.single i 1 - EuclideanSpace.single j 1 with ha
  have h1 : (fun x : ι → ℝ ↦ x i - x j) =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) a) ∘ (WithLp.toLp 2) := by
    ext x
    simp [a, EuclideanSpace.inner_single_left]
  have h2 : ‖a‖₊ ^ 2 = 2 := by
    rw [← NNReal.coe_inj]
    push_cast
    rw [ha, norm_sub_sq_real, PiLp.norm_single, PiLp.norm_single,
      EuclideanSpace.inner_single_left, PiLp.single_apply]
    norm_num [hij]
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
    stdGaussian_map_toDual, h2]

/-- The expectation of the maximum of two distinct coordinates of a product of standard
Gaussians is `1 / √π`. -/
lemma integral_max_pi_gaussianReal {i j : ι} (hij : i ≠ j) :
    ∫ x, max (x i) (x j) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) = (√π)⁻¹ := by
  have hmax : ∀ a b : ℝ, max a b = b + max (a - b) 0 := fun a b ↦ by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (sub_nonpos.2 h), add_zero]
    · rw [max_eq_left h, max_eq_left (sub_nonneg.2 h), add_sub_cancel]
  have hfun : (fun x : ι → ℝ ↦ max (x i) (x j)) = fun x ↦ x j + max (x i - x j) 0 :=
    funext fun x ↦ hmax _ _
  rw [hfun]
  have hint : Integrable (fun x : ι → ℝ ↦ max (x i - x j) 0)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
    have h := (IsGaussian.integrable_id (μ := gaussianReal 0 2)).pos_part
    rw [← map_sub_eval_pi_gaussianReal hij, integrable_map_measure (by fun_prop) (by fun_prop)] at h
    exact h
  rw [integral_add (integrable_eval IsGaussian.integrable_id) hint, integral_eval,
    integral_id_gaussianReal, zero_add,
    ← integral_map (f := fun y ↦ max y 0) (by fun_prop) (by fun_prop),
    map_sub_eval_pi_gaussianReal hij, integral_posPart_gaussianReal_zero_two]

/-! ### Numerical facts -/

/-- `log 128 = 7 log 2 < 4.86`. -/
lemma log_128_lt : log 128 < 4.86 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
  push_cast
  linarith [log_two_lt_d9]

/-- `4.85 < 7 log 2 = log 128`. -/
lemma lt_log_128 : 4.85 < log 128 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, log_pow]
  push_cast
  linarith [log_two_gt_d9]

/-- Linearization of the logarithm: `log m ≤ 3.86 + m / 128` for `m ≥ 128`. -/
lemma log_le_add_div_of_le {m : ℝ} (hm : 128 ≤ m) : log m ≤ 3.86 + m / 128 := by
  have h : log m = log 128 + log (m / 128) := by
    rw [← log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  rw [h]
  have := log_le_sub_one_of_pos (x := m / 128) (by positivity)
  linarith [log_128_lt]

/-- For `m ≥ 128`, `2π (log m + 2.25) ≤ m`. -/
lemma two_pi_mul_log_add_le {m : ℝ} (hm : 128 ≤ m) : 2 * π * (log m + 2.25) ≤ m := by
  have h1 := log_le_add_div_of_le hm
  have h2 : 0 ≤ log m + 2.25 := by linarith [log_nonneg (by linarith : (1 : ℝ) ≤ m)]
  have h3 : π * (log m + 2.25) ≤ 3.15 * (3.86 + m / 128 + 2.25) :=
    mul_le_mul pi_lt_d2.le (by linarith) h2 (by norm_num)
  linarith

/-- If `L ≥ 4` and `2π (L + 2.25) ≤ m` then `2π (1 + L)² ≤ m L`. -/
lemma two_pi_mul_sq_le {m L : ℝ} (hL : 4 ≤ L) (h : 2 * π * (L + 2.25) ≤ m) :
    2 * π * (1 + L) ^ 2 ≤ m * L := by
  have h1 : 2 * π * (L + 2.25) * L ≤ m * L := mul_le_mul_of_nonneg_right h (by linarith)
  have h2 : (1 + L) ^ 2 ≤ (L + 2.25) * L := by nlinarith
  have h3 : 2 * π * (1 + L) ^ 2 ≤ 2 * π * ((L + 2.25) * L) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- For `m ≥ 128` and `t = √(log m)`, the Mills-ratio lower bound `t / (1 + t²) φ(t)` on the
Gaussian tail at `t` is at least `1 / m`. -/
lemma one_le_mul_gaussianPDFReal_sqrt_log {m : ℝ} (hm : 128 ≤ m) :
    1 ≤ m * (√(log m) / (1 + √(log m) ^ 2) * gaussianPDFReal 0 1 (√(log m))) := by
  have hL : 4.85 < log m := lt_log_128.trans_le (log_le_log (by norm_num) hm)
  have key : 2 * π * (1 + log m) ^ 2 ≤ m * log m :=
    two_pi_mul_sq_le (by linarith) (two_pi_mul_log_add_le hm)
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ m = s ^ 2 :=
    ⟨√m, sqrt_pos.2 (by linarith), (sq_sqrt (by linarith)).symm⟩
  have ht2 : √(log (s ^ 2)) ^ 2 = log (s ^ 2) := sq_sqrt (by linarith)
  set t := √(log (s ^ 2))
  have ht : 0 < t := sqrt_pos.2 (by linarith)
  have hexp : exp (-t ^ 2 / 2) = s⁻¹ := by
    rw [← exp_log hs, ← exp_neg]
    congr 1
    rw [ht2, log_pow]
    push_cast
    ring
  rw [gaussianPDFReal_zero_one, hexp]
  have hsq : (1 + t ^ 2) * √(2 * π) ≤ s * t := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow,
      sq_sqrt (x := 2 * π) (by positivity), ht2]
    linarith
  have h : s ^ 2 * (t / (1 + t ^ 2) * ((√(2 * π))⁻¹ * s⁻¹)) = s * t / ((1 + t ^ 2) * √(2 * π)) := by
    field_simp
  rw [h, le_div_iff₀ (by positivity), one_mul]
  exact hsq

/-- `√(log m) / 4 ≤ 1 / √π` for `1 ≤ m ≤ 128`. -/
lemma sqrt_log_div_four_le_inv_sqrt_pi {m : ℝ} (hm0 : 1 ≤ m) (hm : m ≤ 128) :
    √(log m) / 4 ≤ (√π)⁻¹ := by
  have h0 : 0 ≤ log m := log_nonneg hm0
  have h1 : log m ≤ 4.86 := (log_le_log (by linarith) hm).trans log_128_lt.le
  have h2 : log m * π ≤ 4.86 * 3.15 := mul_le_mul h1 pi_lt_d2.le pi_pos.le (by norm_num)
  have h3 : √(log m) * √π ≤ 4 := by
    rw [← sqrt_mul h0, sqrt_le_left (by norm_num)]
    linarith
  calc √(log m) / 4 = √(log m) * √π / (4 * √π) := by field_simp
    _ ≤ 4 / (4 * √π) := by gcongr
    _ = (√π)⁻¹ := by field_simp

/-- `1 / √(2π) ≤ 1 / 2`. -/
lemma inv_sqrt_two_pi_le_half : (√(2 * π))⁻¹ ≤ 1 / 2 := by
  rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
  exact (le_sqrt (by norm_num) (by positivity)).2 (by linarith [pi_gt_three])

/-- If `0 ≤ p ≤ 1` and `1 ≤ m p`, then `(1 - p) ^ m ≤ exp (-1)`. -/
lemma pow_one_sub_le_exp_neg_one {p : ℝ} {m : ℕ} (hp1 : p ≤ 1) (h : 1 ≤ m * p) :
    (1 - p) ^ m ≤ exp (-1) := by
  calc (1 - p) ^ m ≤ exp (-p) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) m
    _ = exp (-(m * p)) := by rw [← exp_nat_mul, mul_neg]
    _ ≤ exp (-1) := exp_le_exp.2 (by linarith)

/-! ### The main lower bound -/

/-- `P(ξ < t) = 1 - P(ξ ≥ t)` for a standard Gaussian `ξ`. -/
lemma measureReal_Iio_gaussianReal_zero_one (t : ℝ) :
    (gaussianReal 0 1).real (Iio t) = 1 - (gaussianReal 0 1).real (Ici t) := by
  rw [← compl_Ici, measureReal_compl measurableSet_Ici, probReal_univ]

omit [Fintype ι] in
/-- Pointwise lower bound on the maximum: `t 1_{t ≤ max_i x_i} - max (-x_{i₀}) 0 ≤ max_i x_i`. -/
lemma indicator_sub_negPart_le_iSup [Finite ι] (i₀ : ι) (t : ℝ) (x : ι → ℝ) :
    {x : ι → ℝ | t ≤ ⨆ i, x i}.indicator (fun _ ↦ t) x - max (-(x i₀)) 0 ≤ ⨆ i, x i := by
  rw [indicator_apply]
  split_ifs with h
  · have : t ≤ ⨆ i, x i := h
    linarith [le_max_right (-(x i₀)) 0]
  · have : x i₀ ≤ ⨆ i, x i := le_ciSup (Finite.bddAbove_range _) i₀
    linarith [le_max_left (-(x i₀)) 0]

section Nonempty

variable [Nonempty ι]

/-- The maximum of the coordinates is integrable under a product of standard Gaussians. -/
lemma integrable_iSup_pi_gaussianReal :
    Integrable (fun x : ι → ℝ ↦ ⨆ i, x i) (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  refine (integrable_finsetSum Finset.univ fun i _ ↦
    (integrable_eval (i := i) IsGaussian.integrable_id).abs).mono' ?_ ?_
  · exact (Measurable.iSup fun i ↦ measurable_pi_apply i).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using abs_le_sum_abs_iSup x

/-- The probability that all coordinates are below `t` is `P(ξ < t) ^ m`. -/
lemma measureReal_iSup_lt_pi_gaussianReal (t : ℝ) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real {x | ⨆ i, x i < t}
      = (gaussianReal 0 1).real (Iio t) ^ Fintype.card ι := by
  have : {x : ι → ℝ | ⨆ i, x i < t} = Set.pi univ fun _ ↦ Iio t := by
    ext x
    simp [Finite.ciSup_lt_iff]
  rw [this, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const,
    Finset.card_univ, measureReal_def]

/-- For `m ≥ 128` coordinates and `t = √(log m)`, `P(max_i ξ_i ≥ t) ≥ 1 / 2`. -/
lemma one_half_le_measureReal_le_iSup_pi_gaussianReal (hι : 128 ≤ Fintype.card ι) :
    1 / 2 ≤ (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real
      {x | √(log (Fintype.card ι)) ≤ ⨆ i, x i} := by
  set m := Fintype.card ι
  set t := √(log m)
  have hm : (128 : ℝ) ≤ m := by exact_mod_cast hι
  have ht : 0 < t := sqrt_pos.2 (by linarith [lt_log_128.trans_le (log_le_log (by norm_num) hm)])
  have hp1 : 1 ≤ m * (gaussianReal 0 1).real (Ici t) :=
    calc 1 ≤ m * (t / (1 + t ^ 2) * gaussianPDFReal 0 1 t) :=
          one_le_mul_gaussianPDFReal_sqrt_log hm
      _ ≤ m * (gaussianReal 0 1).real (Ici t) := by
          gcongr
          exact mul_gaussianPDFReal_le_measureReal_Ici ht
  have hcompl : {x : ι → ℝ | t ≤ ⨆ i, x i} = {x | ⨆ i, x i < t}ᶜ := by
    ext x
    simp
  have hmeas : MeasurableSet {x : ι → ℝ | ⨆ i, x i < t} :=
    measurableSet_lt (Measurable.iSup fun i ↦ measurable_pi_apply i) measurable_const
  rw [hcompl, measureReal_compl hmeas, probReal_univ, measureReal_iSup_lt_pi_gaussianReal,
    measureReal_Iio_gaussianReal_zero_one]
  have := pow_one_sub_le_exp_neg_one (m := m) measureReal_le_one hp1
  linarith [exp_neg_one_lt_d9]

/-- The main lower bound in the case of at least `128` coordinates. -/
lemma sqrt_log_div_four_le_integral_iSup_pi_gaussianReal_of_le (hι : 128 ≤ Fintype.card ι) :
    √(log (Fintype.card ι)) / 4 ≤ ∫ x, ⨆ i, x i ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set m := Fintype.card ι
  set t := √(log m)
  set S := {x : ι → ℝ | t ≤ ⨆ i, x i}
  have hm : (128 : ℝ) ≤ m := by exact_mod_cast hι
  have ht : 2 ≤ t := (le_sqrt (by norm_num) (log_nonneg (by linarith))).2
    (by linarith [lt_log_128.trans_le (log_le_log (by norm_num) hm)])
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (Measurable.iSup fun i ↦ measurable_pi_apply i)
  have hneg : Integrable (fun x : ι → ℝ ↦ max (-(x i₀)) 0)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    integrable_comp_eval (f := fun y ↦ max (-y) 0) IsGaussian.integrable_id.neg.pos_part
  have hint : Integrable (fun x ↦ S.indicator (fun _ ↦ t) x - max (-(x i₀)) 0)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    ((integrable_const t).indicator hS).sub hneg
  have h1 : ∫ x, (S.indicator (fun _ ↦ t) x - max (-(x i₀)) 0)
        ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1)
      = t * (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real S - (√(2 * π))⁻¹ := by
    rw [integral_sub ((integrable_const t).indicator hS) hneg, integral_indicator_const t hS,
      integral_comp_eval (μ := fun _ : ι ↦ gaussianReal 0 1) (i := i₀) (f := fun y ↦ max (-y) 0)
        (measurable_neg.max measurable_const).aestronglyMeasurable,
      integral_negPart_gaussianReal_zero_one, smul_eq_mul, mul_comm]
  have h2 := one_half_le_measureReal_le_iSup_pi_gaussianReal hι
  have h3 : t * (1 / 2) ≤ t * (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real S :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  calc t / 4 ≤ t * (Measure.pi fun _ : ι ↦ gaussianReal 0 1).real S - (√(2 * π))⁻¹ := by
        linarith [inv_sqrt_two_pi_le_half]
    _ = ∫ x, (S.indicator (fun _ ↦ t) x - max (-(x i₀)) 0)
          ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) := h1.symm
    _ ≤ ∫ x, ⨆ i, x i ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
        integral_mono hint integrable_iSup_pi_gaussianReal (indicator_sub_negPart_le_iSup i₀ t)

/-- The main lower bound in the case of `2 ≤ m ≤ 128` coordinates. -/
lemma sqrt_log_div_four_le_integral_iSup_pi_gaussianReal_of_le' (hι : 2 ≤ Fintype.card ι)
    (hι' : Fintype.card ι ≤ 128) :
    √(log (Fintype.card ι)) / 4 ≤ ∫ x, ⨆ i, x i ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hι
  have hint : Integrable (fun x : ι → ℝ ↦ max (x i) (x j))
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    (integrable_eval IsGaussian.integrable_id).sup (integrable_eval IsGaussian.integrable_id)
  calc √(log (Fintype.card ι)) / 4 ≤ (√π)⁻¹ :=
        sqrt_log_div_four_le_inv_sqrt_pi (by exact_mod_cast hι.trans' one_le_two)
          (by exact_mod_cast hι')
    _ = ∫ x, max (x i) (x j) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
        (integral_max_pi_gaussianReal hij).symm
    _ ≤ ∫ x, ⨆ i, x i ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
        integral_mono hint integrable_iSup_pi_gaussianReal fun x ↦
          max_le (le_ciSup (Finite.bddAbove_range _) i) (le_ciSup (Finite.bddAbove_range _) j)

end Nonempty

/-- For `m ≥ 2` i.i.d. standard Gaussians, `E[max_i ξ_i] ≥ √(log m) / 4`. -/
lemma sqrt_log_div_four_le_integral_iSup_pi_gaussianReal (hι : 2 ≤ Fintype.card ι) :
    √(log (Fintype.card ι)) / 4 ≤ ∫ x, ⨆ i, x i ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  rcases le_or_gt 128 (Fintype.card ι) with h | h
  · exact sqrt_log_div_four_le_integral_iSup_pi_gaussianReal_of_le h
  · exact sqrt_log_div_four_le_integral_iSup_pi_gaussianReal_of_le' hι h.le

end ProbabilityTheory
