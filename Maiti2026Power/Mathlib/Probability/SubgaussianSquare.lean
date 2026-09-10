/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.GaussianSquareMGF

/-!
# The square of a sub-Gaussian variable

The Gaussian trick `exp (a z²) = E[exp (√(2a) z G)]` for `G ~ N(0, 1)` and Fubini give, for a
sub-Gaussian variable `Z` with constant `c`, `E[exp (a Z²)] ≤ E[exp (c a G²)] = (1 - 2ca)^(-1/2)`
whenever `0 ≤ a` and `2 c a < 1`.

* `HasSubgaussianMGF.integral_exp_mul_sq_le`: the bound above.
* `HasSubgaussianMGF.integral_pow_four_le`: `E[Z⁴] ≤ 14 c²`.
* `HasSubgaussianMGF.integral_pow_four_le_of_integral_sq_eq`: if moreover `E[Z²] = c`, then
  `E[Z⁴] ≤ 4 c²`.
* `HasSubgaussianMGF.hasSubexponentialMGF_sq_sub`: under the same hypothesis, `Z² - c` is
  sub-exponential with parameters `(4 c², 4 c)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {Z : Ω → ℝ} {c : ℝ≥0}

namespace HasSubgaussianMGF

/-- The Gaussian trick: `∫⁻ exp (a Z²) ≤ (1 - 2 c a)^(-1/2)`. -/
lemma lintegral_exp_mul_sq_le [SFinite μ] (h : HasSubgaussianMGF Z c μ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * c * a < 1) :
    ∫⁻ ω, ENNReal.ofReal (exp (a * Z ω ^ 2)) ∂μ ≤ ENNReal.ofReal ((√(1 - 2 * c * a))⁻¹) := by
  set s := √(2 * a) with hs
  have hs2 : s ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hpt : ∀ z : ℝ, exp (a * z ^ 2) = ∫ v, exp ((s * z) * v) ∂gaussianReal 0 1 := by
    intro z
    have := mgf_gaussianReal (X := id) (p := gaussianReal 0 1) (μ := 0) (v := 1) HasLaw.id
      (s * z)
    simp only [mgf, id] at this
    rw [this]
    congr 1
    rw [NNReal.coe_one, zero_mul, zero_add, one_mul, mul_pow, hs2]
    ring
  have hZ : AEMeasurable Z μ := h.aemeasurable
  have hZ' : AEMeasurable (Function.uncurry fun ω v ↦ ENNReal.ofReal (exp ((s * Z ω) * v)))
      (μ.prod (gaussianReal 0 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable
      ((hZ.comp_fst.const_mul s).mul measurable_snd.aemeasurable))
  calc ∫⁻ ω, ENNReal.ofReal (exp (a * Z ω ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ v, ENNReal.ofReal (exp ((s * Z ω) * v)) ∂gaussianReal 0 1 ∂μ := by
        refine lintegral_congr fun ω ↦ ?_
        rw [hpt, ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
          (ae_of_all _ fun _ ↦ (exp_pos _).le)]
    _ = ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (exp ((s * v) * Z ω)) ∂μ ∂gaussianReal 0 1 := by
        rw [lintegral_lintegral_swap hZ']
        refine lintegral_congr fun v ↦ lintegral_congr fun ω ↦ ?_
        ring_nf
    _ ≤ ∫⁻ v, ENNReal.ofReal (exp (c * (s * v) ^ 2 / 2)) ∂gaussianReal 0 1 := by
        refine lintegral_mono fun v ↦ ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_mul _)
          (ae_of_all _ fun _ ↦ (exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (h.mgf_le _)
    _ = ENNReal.ofReal (∫ v, exp ((c * a) * v ^ 2) ∂gaussianReal 0 1) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_sq_gaussianReal 0 1
          (by rw [NNReal.coe_one, mul_one]; linarith)) (ae_of_all _ fun _ ↦ (exp_pos _).le)]
        refine lintegral_congr fun v ↦ ?_
        congr 2
        rw [mul_pow, hs2]
        ring
    _ = ENNReal.ofReal ((√(1 - 2 * c * a))⁻¹) := by
        rw [integral_exp_mul_sq_gaussianReal 0 1 (by rw [NNReal.coe_one, mul_one]; linarith)]
        simp only [NNReal.coe_one, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, zero_mul, zero_div, exp_zero]
        ring_nf

lemma integrable_exp_mul_sq [SFinite μ] (h : HasSubgaussianMGF Z c μ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * c * a < 1) :
    Integrable (fun ω ↦ exp (a * Z ω ^ 2)) μ := by
  refine ⟨(Real.measurable_exp.comp_aemeasurable
    ((h.aemeasurable.pow_const 2).const_mul a)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  exact (h.lintegral_exp_mul_sq_le ha0 ha).trans_lt ENNReal.ofReal_lt_top

/-- **MGF of the square of a sub-Gaussian variable**: `E[exp (a Z²)] ≤ (1 - 2 c a)^(-1/2)` for
`0 ≤ a` and `2 c a < 1`. -/
lemma integral_exp_mul_sq_le [SFinite μ] (h : HasSubgaussianMGF Z c μ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : 2 * c * a < 1) :
    ∫ ω, exp (a * Z ω ^ 2) ∂μ ≤ (√(1 - 2 * c * a))⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (exp_pos _).le)
    (h.integrable_exp_mul_sq ha0 ha).aestronglyMeasurable,
    ← ENNReal.toReal_ofReal (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.lintegral_exp_mul_sq_le ha0 ha)

/-- Fourth moment of a sub-Gaussian variable: `E[Z⁴] ≤ 14 c²`. -/
lemma integral_pow_four_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF Z c μ) :
    ∫ ω, Z ω ^ 4 ∂μ ≤ 14 * c ^ 2 := by
  by_cases hc : c = 0
  · subst hc
    have hZ0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (by filter_upwards [hZ0] with ω hω; simp [hω])]
    simp
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  set a : ℝ := 1 / (4 * c) with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : 2 * c * a = 1 / 2 := by
    rw [ha_def]
    field_simp
    ring
  have ha : 2 * c * a < 1 := by linarith
  have h1 := h.integral_exp_mul_sq_le ha0 ha
  have hint4 : Integrable (fun ω ↦ Z ω ^ 4) μ :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp [h.integrableExpSet_eq_univ]) 4
  have hexp := h.integrable_exp_mul_sq ha0 ha
  have h3 : ∫ ω, a ^ 2 / 2 * Z ω ^ 4 ∂μ ≤ ∫ ω, (exp (a * Z ω ^ 2) - 1) ∂μ := by
    refine integral_mono (hint4.const_mul _) (hexp.sub (integrable_const 1)) fun ω ↦ ?_
    have h5 := Real.quadratic_le_exp_of_nonneg (x := a * Z ω ^ 2) (by positivity)
    have h6 : 0 ≤ a * Z ω ^ 2 := by positivity
    simp only
    nlinarith [h5, h6]
  rw [integral_const_mul, integral_sub hexp (integrable_const 1), integral_const, probReal_univ,
    smul_eq_mul, one_mul] at h3
  have h4 : (√(1 - 2 * c * a))⁻¹ = √2 := by
    rw [ha1, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.sqrt_inv, inv_inv]
  have hsqrt2 : √2 ≤ 23 / 16 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have ha2 : a ^ 2 = 1 / (16 * c ^ 2) := by
    rw [ha_def]
    field_simp
    ring
  have h7 : a ^ 2 / 2 * ∫ ω, Z ω ^ 4 ∂μ ≤ √2 - 1 := by
    rw [← h4]
    linarith
  rw [ha2] at h7
  have h8 : ∫ ω, Z ω ^ 4 ∂μ ≤ 32 * c ^ 2 * (√2 - 1) := by
    have : 1 / (16 * c ^ 2) / 2 * ∫ ω, Z ω ^ 4 ∂μ = (∫ ω, Z ω ^ 4 ∂μ) / (32 * c ^ 2) := by
      field_simp
      ring
    rw [this, div_le_iff₀ (by positivity)] at h7
    linarith
  nlinarith [mul_nonneg (sq_nonneg (c : ℝ)) (by linarith : (0 : ℝ) ≤ 23 / 16 - √2)]

/-- If `Z` is sub-Gaussian with constant `c` and `E[Z²] = c`, then `E[Z⁴] ≤ 4 c²`.

Keeping the linear term of `1 + x + x²/2 ≤ exp x` (which `integral_pow_four_le` throws away) pays
for a factor of more than three. The sharp constant is `3 c²`, the Gaussian value: letting `a → 0`
in the proof below gives `E[Z⁴] ≤ 3 c²`, which is also what matching the `t⁴` coefficients of
`E[exp (t Z)] ≤ exp (c t²/2)` at `t = 0` gives, so `E[Z²] = c` forces a kurtosis of at most 3. -/
lemma integral_pow_four_le_of_integral_sq_eq [IsProbabilityMeasure μ] (h : HasSubgaussianMGF Z c μ)
    (hZ2 : ∫ ω, Z ω ^ 2 ∂μ = c) :
    ∫ ω, Z ω ^ 4 ∂μ ≤ 4 * c ^ 2 := by
  have hint4 : Integrable (fun ω ↦ Z ω ^ 4) μ :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp [h.integrableExpSet_eq_univ]) 4
  have hint2 : Integrable (fun ω ↦ Z ω ^ 2) μ :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp [h.integrableExpSet_eq_univ]) 2
  by_cases hc : c = 0
  · -- `E[Z²] = 0` forces `Z = 0` almost everywhere
    have hZ0 : ∀ᵐ ω ∂μ, Z ω ^ 2 = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg (Z ω)) hint2).1 (by simp [hZ2, hc])
      filter_upwards [this] with ω hω using hω
    rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ)) ?_]
    · simp [hc]
    · filter_upwards [hZ0] with ω hω
      nlinarith [hω]
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  set a : ℝ := 1 / (8 * c) with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : 2 * c * a = 1 / 4 := by
    rw [ha_def]
    field_simp
    ring
  have ha : 2 * c * a < 1 := by linarith
  have hexp := h.integrable_exp_mul_sq ha0 ha
  have h1 := h.integral_exp_mul_sq_le ha0 ha
  -- `1 + a E[Z²] + a²/2 E[Z⁴] ≤ E[exp (a Z²)]`
  have hi1 : Integrable (fun ω ↦ 1 + a * Z ω ^ 2) μ :=
    (integrable_const 1).add (hint2.const_mul a)
  have hi2 : Integrable (fun ω ↦ a ^ 2 / 2 * Z ω ^ 4) μ := hint4.const_mul _
  have h3 : 1 + a * c + a ^ 2 / 2 * ∫ ω, Z ω ^ 4 ∂μ ≤ ∫ ω, exp (a * Z ω ^ 2) ∂μ := by
    have hle : ∫ ω, (1 + a * Z ω ^ 2 + a ^ 2 / 2 * Z ω ^ 4) ∂μ ≤ ∫ ω, exp (a * Z ω ^ 2) ∂μ := by
      refine integral_mono (hi1.add hi2) hexp fun ω ↦ ?_
      have h5 := Real.quadratic_le_exp_of_nonneg (x := a * Z ω ^ 2) (by positivity)
      simp only
      nlinarith [h5]
    rw [integral_add hi1 hi2, integral_add (integrable_const 1) (hint2.const_mul a),
      integral_const, integral_const_mul, integral_const_mul, hZ2, probReal_univ, smul_eq_mul,
      one_mul] at hle
    exact hle
  -- `(1 - 1/4)^(-1/2) = 2/√3 ≤ 500/433`
  have hsqrt : (433 / 500 : ℝ) ≤ √(1 - 2 * c * a) := by
    rw [ha1, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show (433 / 500 : ℝ) = √((433 / 500) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv : (√(1 - 2 * c * a))⁻¹ ≤ 500 / 433 := by
    rw [inv_le_comm₀ (Real.sqrt_pos.2 (by linarith)) (by norm_num),
      show ((500 : ℝ) / 433)⁻¹ = 433 / 500 by norm_num]
    exact hsqrt
  have ha2 : a ^ 2 = 1 / (64 * c ^ 2) := by
    rw [ha_def]
    field_simp
    ring
  have hac : a * c = 1 / 8 := by
    rw [ha_def]
    field_simp
  have h4 : a ^ 2 / 2 * ∫ ω, Z ω ^ 4 ∂μ ≤ 500 / 433 - 9 / 8 := by
    have h6 := h3.trans (h1.trans hinv)
    rw [hac] at h6
    linarith
  rw [ha2, div_div, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h4
  nlinarith [h4, sq_nonneg (c : ℝ)]

/-- **The centered square of a sub-Gaussian variable is sub-exponential**: if `Z` is sub-Gaussian
with constant `c` and `E[Z²] = c`, then `Z² - c` has sub-exponential parameters `(4 c², 4 c)`.

The parameters are close to optimal: `Z ~ N(0, c)` saturates the moment generating function bound,
and for it the smallest `V` that works on `|t| ≤ 1/(4c)` is `(16 log 2 - 8) c² ≈ 3.09 c²`; no `V`
works for `b ≤ 2 c`, and `V ≥ 2 c² = Var(Z²)` for every `b`. -/
lemma hasSubexponentialMGF_sq_sub [IsProbabilityMeasure μ] (h : HasSubgaussianMGF Z c μ)
    (hZ2 : ∫ ω, Z ω ^ 2 ∂μ = c) :
    HasSubexponentialMGF (fun ω ↦ Z ω ^ 2 - c) (4 * c ^ 2) (4 * c) μ := by
  have hc := c.coe_nonneg
  have hZ := h.aemeasurable
  have hint2 : Integrable (fun ω ↦ Z ω ^ 2) μ :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp [h.integrableExpSet_eq_univ]) 2
  have hint4 : Integrable (fun ω ↦ Z ω ^ 4) μ :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp [h.integrableExpSet_eq_univ]) 4
  have hmeas : ∀ a : ℝ, AEStronglyMeasurable (fun ω ↦ exp (a * (Z ω ^ 2 - c))) μ := fun a ↦
    (Real.measurable_exp.comp_aemeasurable
      (((hZ.pow_const 2).sub_const _).const_mul a)).aestronglyMeasurable
  have hmgf : ∀ a : ℝ, mgf (fun ω ↦ Z ω ^ 2 - c) μ a
      = exp (-(a * c)) * ∫ ω, exp (a * Z ω ^ 2) ∂μ := by
    intro a
    rw [mgf, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only
    rw [← exp_add]
    congr 1
    ring
  have key : ∀ a : ℝ, 4 * c * |a| ≤ 1 → 0 ≤ a → 2 * c * a < 1 := by
    intro a ha ha0
    rw [abs_of_nonneg ha0] at ha
    linarith
  constructor
  · intro a ha
    rcases le_or_gt 0 a with ha0 | ha0
    · have := (h.integrable_exp_mul_sq ha0 (key a ha ha0)).const_mul (exp (-(a * c)))
      refine this.congr (ae_of_all _ fun ω ↦ ?_)
      simp only
      rw [← exp_add]
      congr 1
      ring
    · refine Integrable.mono' (integrable_const (exp (-(a * c)))) (hmeas a)
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
      nlinarith [sq_nonneg (Z ω)]
  · intro a ha
    have hν : |2 * c * a| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      linarith
    rw [hmgf]
    rcases le_or_gt 0 a with ha0 | ha0
    · have h2ca := key a ha ha0
      have h1 : 0 < 1 - 2 * c * a := by linarith
      have hsqrt : (√(1 - 2 * c * a))⁻¹ = exp (-(log (1 - 2 * c * a) / 2)) := by
        rw [exp_neg, ← Real.log_sqrt h1.le, exp_log (Real.sqrt_pos.2 h1)]
      calc exp (-(a * c)) * ∫ ω, exp (a * Z ω ^ 2) ∂μ
          ≤ exp (-(a * c)) * (√(1 - 2 * c * a))⁻¹ := by
            gcongr
            exact h.integral_exp_mul_sq_le ha0 h2ca
        _ = exp (-(a * c) + -(log (1 - 2 * c * a) / 2)) := by rw [hsqrt, exp_add]
        _ ≤ exp (4 * c ^ 2 * a ^ 2 / 2) := by
            rw [exp_le_exp]
            have hi := neg_log_one_sub_le_add_sq hν
            nlinarith [hi, sq_nonneg (c * a)]
    · have hpt : ∀ ω, exp (a * Z ω ^ 2) ≤ 1 + a * Z ω ^ 2 + a ^ 2 / 2 * Z ω ^ 4 := by
        intro ω
        have := Real.exp_le_one_add_add_sq_div_two_of_nonpos (x := a * Z ω ^ 2)
          (by nlinarith [sq_nonneg (Z ω)])
        have e : (a * Z ω ^ 2) ^ 2 / 2 = a ^ 2 / 2 * Z ω ^ 4 := by ring
        linarith
      have hexp : Integrable (fun ω ↦ exp (a * Z ω ^ 2)) μ := by
        refine Integrable.mono' (integrable_const 1) (Real.measurable_exp.comp_aemeasurable
          ((hZ.pow_const 2).const_mul a)).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
        rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
        nlinarith [sq_nonneg (Z ω)]
      have hi1 : Integrable (fun ω ↦ 1 + a * Z ω ^ 2) μ :=
        (integrable_const 1).add (hint2.const_mul a)
      have hi2 : Integrable (fun ω ↦ a ^ 2 / 2 * Z ω ^ 4) μ := hint4.const_mul _
      have hI : ∫ ω, exp (a * Z ω ^ 2) ∂μ ≤ 1 + a * c + 2 * c ^ 2 * a ^ 2 := by
        calc ∫ ω, exp (a * Z ω ^ 2) ∂μ
            ≤ ∫ ω, (1 + a * Z ω ^ 2 + a ^ 2 / 2 * Z ω ^ 4) ∂μ :=
              integral_mono hexp (hi1.add hi2) hpt
          _ = 1 + a * c + a ^ 2 / 2 * ∫ ω, Z ω ^ 4 ∂μ := by
              rw [integral_add hi1 hi2, integral_add (integrable_const 1) (hint2.const_mul a),
                integral_const, integral_const_mul, integral_const_mul, hZ2, probReal_univ,
                smul_eq_mul, one_mul]
          _ ≤ 1 + a * c + a ^ 2 / 2 * (4 * c ^ 2) := by
              gcongr
              exact h.integral_pow_four_le_of_integral_sq_eq hZ2
          _ = 1 + a * c + 2 * c ^ 2 * a ^ 2 := by ring
      calc exp (-(a * c)) * ∫ ω, exp (a * Z ω ^ 2) ∂μ
          ≤ exp (-(a * c)) * exp (a * c + 2 * c ^ 2 * a ^ 2) := by
            gcongr
            refine hI.trans ?_
            linarith [Real.add_one_le_exp (a * c + 2 * c ^ 2 * a ^ 2)]
        _ = exp (2 * c ^ 2 * a ^ 2) := by
            rw [← exp_add]
            congr 1
            ring
        _ = exp (4 * c ^ 2 * a ^ 2 / 2) := by
            congr 1
            ring

end HasSubgaussianMGF

end ProbabilityTheory
