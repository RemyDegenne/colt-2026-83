/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gamma
public import Maiti2026Power.Mathlib.Probability.GaussianSquareMGF
public import Maiti2026Power.Mathlib.Probability.Moments.ExtOfMGF

/-!
# Chi-squared distributions over ℝ

The chi-squared distribution with `d` degrees of freedom is the gamma distribution with shape
`d / 2` and rate `1 / 2`, and this is how it is defined here on top of Mathlib's
`ProbabilityTheory.gammaMeasure` (the way `expMeasure` is defined as `gammaMeasure 1 r`).

## Main definitions

* `chiSqPDFReal d`: the function
  `x ↦ x ^ (d / 2 - 1) * exp (-x / 2) / (2 ^ (d / 2) * Gamma (d / 2))` for `0 ≤ x` and `0` else,
  the probability density function of the chi-squared distribution with `d` degrees of freedom;
* `chiSqPDF d`: its `ℝ≥0∞`-valued version;
* `chiSqMeasure d`: the chi-squared measure on `ℝ` with `d` degrees of freedom.

## Main results

* `isProbabilityMeasure_chiSqMeasure`: `chiSqMeasure d` is a probability measure for `0 < d`;
* `mgf_gammaMeasure`: `∫ exp (t x) dγ(a, r) = (r / (r - t)) ^ a` for `t < r`, the moment generating
  function of the gamma distribution (absent from Mathlib);
* `mgf_chiSqMeasure`: `(1 - 2t) ^ (-d/2)` for `t < 1/2`;
* `mgf_norm_sq_stdGaussian`: the squared norm of a standard Gaussian vector of a `d`-dimensional
  real inner product space has the moment generating function of `chiSqMeasure d`;
* `map_norm_sq_stdGaussian_eq_chiSqMeasure`: **the law of `‖g‖ ^ 2` for a standard Gaussian vector
  `g` of a `d`-dimensional real inner product space is `chiSqMeasure d`** (`d = finrank ℝ E`).
  This is what justifies calling `‖g‖² - d` a centered chi-square variable in
  `GaussianSquareMGF.lean`. It is deduced from the equality of the moment
  generating functions through `Measure.ext_of_mgf_eq` (see
  `Maiti2026Power/Mathlib/Probability/Moments/ExtOfMGF.lean`), which needs the integrability of
  `exp (t X)` near `0` and its failure for `t ≥ 1/2`, both proved here
  (`integrable_exp_mul_gammaMeasure`, `not_integrable_exp_mul_gammaMeasure`,
  `integrable_exp_mul_norm_sq_stdGaussian`, `not_integrable_exp_mul_norm_sq_stdGaussian`).
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

section ChiSqPDF

variable {d : ℕ} {x : ℝ}

/-- The pdf of the chi-squared distribution with `d` degrees of freedom. -/
noncomputable def chiSqPDFReal (d : ℕ) (x : ℝ) : ℝ := gammaPDFReal (d / 2) (1 / 2) x

/-- The pdf of the chi-squared distribution with `d` degrees of freedom, as a function valued in
`ℝ≥0∞`. -/
noncomputable def chiSqPDF (d : ℕ) (x : ℝ) : ℝ≥0∞ := gammaPDF (d / 2) (1 / 2) x

lemma chiSqPDF_eq (d : ℕ) (x : ℝ) : chiSqPDF d x = ENNReal.ofReal (chiSqPDFReal d x) := rfl

lemma chiSqPDFReal_of_neg (hx : x < 0) : chiSqPDFReal d x = 0 := by
  simp [chiSqPDFReal, gammaPDFReal, not_le.2 hx]

lemma chiSqPDF_of_neg (hx : x < 0) : chiSqPDF d x = 0 := gammaPDF_of_neg hx

/-- The usual formula for the chi-squared pdf on `[0, ∞)`. -/
lemma chiSqPDFReal_of_nonneg (hx : 0 ≤ x) :
    chiSqPDFReal d x
      = x ^ ((d : ℝ) / 2 - 1) * exp (-x / 2) / (2 ^ ((d : ℝ) / 2) * Gamma (d / 2)) := by
  rw [chiSqPDFReal, gammaPDFReal, ite_eq_left hx, Real.div_rpow zero_le_one (by norm_num),
    Real.one_rpow, show -((1 : ℝ) / 2 * x) = -x / 2 by ring]
  ring

@[fun_prop]
lemma measurable_chiSqPDFReal (d : ℕ) : Measurable (chiSqPDFReal d) :=
  measurable_gammaPDFReal _ _

lemma chiSqPDFReal_nonneg (hd : 0 < d) (x : ℝ) : 0 ≤ chiSqPDFReal d x :=
  gammaPDFReal_nonneg (by positivity) (by norm_num) x

@[simp]
lemma lintegral_chiSqPDF_eq_one (hd : 0 < d) : ∫⁻ x, chiSqPDF d x = 1 :=
  lintegral_gammaPDF_eq_one (by positivity) (by norm_num)

end ChiSqPDF

/-- The chi-squared measure with `d` degrees of freedom: the gamma measure with shape `d / 2` and
rate `1 / 2`. -/
noncomputable def chiSqMeasure (d : ℕ) : Measure ℝ := gammaMeasure (d / 2) (1 / 2)

lemma chiSqMeasure_eq_withDensity (d : ℕ) :
    chiSqMeasure d = volume.withDensity (chiSqPDF d) := rfl

lemma isProbabilityMeasure_chiSqMeasure {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (chiSqMeasure d) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)

instance (d : ℕ) [NeZero d] : IsProbabilityMeasure (chiSqMeasure d) :=
  isProbabilityMeasure_chiSqMeasure (Nat.pos_of_ne_zero (NeZero.ne d))

section CDF

lemma cdf_chiSqMeasure_eq_integral {d : ℕ} (hd : 0 < d) (x : ℝ) :
    cdf (chiSqMeasure d) x = ∫ y in Iic x, chiSqPDFReal d y :=
  cdf_gammaMeasure_eq_integral (by positivity) (by norm_num) x

lemma cdf_chiSqMeasure_eq_lintegral {d : ℕ} (hd : 0 < d) (x : ℝ) :
    cdf (chiSqMeasure d) x = (∫⁻ y in Iic x, chiSqPDF d y).toReal :=
  cdf_gammaMeasure_eq_lintegral (by positivity) (by norm_num) x

end CDF

section MGF

/-- The moment generating function of the gamma distribution: `∫ exp (t x) dγ(a, r)`
is `(r / (r - t)) ^ a` for `t < r`. Mathlib has the gamma distribution but not its mgf. -/
lemma integral_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂gammaMeasure a r = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := by linarith
  have hGa : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have hzero : ∀ x, x ∉ Ici (0 : ℝ) → gammaPDFReal a r x * exp (t * x) = 0 := by
    intro x hx
    rw [gammaPDFReal, ite_eq_right (by simpa using hx), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun (g := fun x ↦ r ^ a / Gamma a * (x ^ (a - 1) * exp (-((r - t) * x))))
      measurableSet_Ioi (fun x hx ↦ ?_), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrt, Real.div_rpow hr.le hrt.le,
    show (1 : ℝ) / (r - t) = (r - t)⁻¹ by ring, Real.inv_rpow hrt.le]
  · field_simp
  · rw [gammaPDFReal, ite_eq_left (le_of_lt hx), mul_assoc, mul_assoc, ← exp_add]
    ring_nf

/-- The moment generating function of the chi-squared distribution with `d` degrees of freedom:
`(1 - 2t) ^ (-d/2)` for `t < 1/2`. -/
lemma mgf_chiSqMeasure {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : t < 1 / 2) :
    mgf id (chiSqMeasure d) t = (1 - 2 * t) ^ (-(d : ℝ) / 2) := by
  have h1 : (0 : ℝ) < 1 - 2 * t := by linarith
  rw [mgf, chiSqMeasure]
  simp_rw [id]
  rw [integral_exp_mul_gammaMeasure (by positivity) (by norm_num) (by linarith)]
  rw [show (1 : ℝ) / 2 / (1 / 2 - t) = (1 - 2 * t)⁻¹ by field_simp,
    Real.inv_rpow h1.le, ← Real.rpow_neg h1.le]
  congr 1
  ring

end MGF

section Integrability

/-- For `t < r`, `exp (t x)` is integrable for the gamma distribution: the integrand is a multiple
of the gamma density with rate `r - t`. -/
lemma integrable_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  have hrt : 0 < r - t := by linarith
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hpdf : Integrable (gammaPDFReal a (r - t)) := by
    refine ⟨(stronglyMeasurable_gammaPDFReal a (r - t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg ha hrt))]
    rw [show (fun x ↦ ENNReal.ofReal (gammaPDFReal a (r - t) x)) = gammaPDF a (r - t) from rfl,
      lintegral_gammaPDF_eq_one ha hrt]
    exact ENNReal.one_lt_top
  rw [gammaMeasure, integrable_withDensity_iff hmeas (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  refine ((hpdf.const_mul ((r / (r - t)) ^ a)).congr (ae_of_all _ fun x ↦ ?_)).congr
    (ae_of_all _ fun x ↦ rfl)
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rcases le_or_gt 0 x with hx | hx
  · have hG : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
    have hrta : (r - t) ^ a ≠ 0 := (Real.rpow_pos_of_pos hrt a).ne'
    have hcomb : exp (t * x) * exp (-(r * x)) = exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [gammaPDFReal, gammaPDFReal, ite_eq_left hx, ite_eq_left hx, Real.div_rpow hr.le hrt.le,
      show exp (t * x) * (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)))
        = r ^ a / Gamma a * x ^ (a - 1) * (exp (t * x) * exp (-(r * x))) by ring, hcomb]
    field_simp
  · rw [gammaPDFReal, gammaPDFReal, ite_eq_right (by linarith), ite_eq_right (by linarith)]
    ring

/-- For `r ≤ t`, `exp (t x)` is *not* integrable for the gamma distribution: on `(1, ∞)` the
integrand dominates `x ↦ c x ^ (a - 1)`, which is not integrable there since `a - 1 ≥ -1`. -/
lemma not_integrable_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : r ≤ t) :
    ¬ Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  have hc : 0 < r ^ a / Gamma a := by positivity
  intro hint
  rw [gammaMeasure, integrable_withDensity_iff hmeas (ae_of_all _ fun x ↦ by simp [gammaPDF])]
    at hint
  have hint' : IntegrableOn (fun x ↦ exp (t * x) * (gammaPDF a r x).toReal) (Ioi 1) :=
    hint.integrableOn
  have hsmall : IntegrableOn (fun x ↦ r ^ a / Gamma a * x ^ (a - 1)) (Ioi 1) := by
    refine Integrable.mono' hint' (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
    intro x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hcomb : exp (t * x) * (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)))
        = r ^ a / Gamma a * x ^ (a - 1) * exp ((t - r) * x) := by
      rw [show r ^ a / Gamma a * x ^ (a - 1) * exp ((t - r) * x)
          = r ^ a / Gamma a * x ^ (a - 1) * (exp (t * x) * exp (-(r * x))) by
        rw [← Real.exp_add]; congr 1; ring_nf]
      ring
    rw [Real.norm_of_nonneg (by positivity), gammaPDF,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), gammaPDFReal, ite_eq_left hx0.le, hcomb]
    have h1 : (1 : ℝ) ≤ exp ((t - r) * x) := Real.one_le_exp (by nlinarith)
    have h2 : (0 : ℝ) < x ^ (a - 1) := Real.rpow_pos_of_pos hx0 _
    nlinarith [mul_pos hc h2]
  have : IntegrableOn (fun x : ℝ ↦ x ^ (a - 1)) (Ioi 1) := by
    have := hsmall.const_mul (Gamma a / r ^ a)
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    field_simp
  rw [integrableOn_Ioi_rpow_iff one_pos] at this
  linarith

end Integrability

section StdGaussian

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `exp (t ‖∑ i, x i • b i‖²) = ∏ i, exp (t xᵢ²)` in an orthonormal basis `b`. -/
lemma exp_mul_norm_sum_smul_sq_eq_prod (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : ι → ℝ) :
    exp (t * ‖∑ i, x i • b i‖ ^ 2) = ∏ i, exp (t * x i ^ 2) := by
  rw [b.norm_sum_smul_sq, Finset.mul_sum, Real.exp_sum]

/-- The moment generating function of `‖g‖ ^ 2` for a standard Gaussian vector `g` of a
`d`-dimensional inner product space: `(1 - 2t) ^ (-d/2)` for `t < 1/2`. -/
lemma integral_exp_mul_norm_sq_stdGaussian {t : ℝ} (ht : t < 1 / 2) :
    ∫ g, exp (t * ‖g‖ ^ 2) ∂(stdGaussian E)
      = (1 - 2 * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  have h1 : (0 : ℝ) < 1 - 2 * t := by linarith
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integral_map (measurable_sum_smul_orthonormalBasis _).aemeasurable (by fun_prop)]
  simp_rw [exp_mul_norm_sum_smul_sq_eq_prod]
  rw [integral_fintype_prod_eq_prod (f := fun _ (x : ℝ) ↦ exp (t * x ^ 2))]
  have hfac : ∀ _i : Fin (Module.finrank ℝ E), ∫ x : ℝ, exp (t * x ^ 2) ∂gaussianReal 0 1
      = (1 - 2 * t) ^ (-(1 : ℝ) / 2) := by
    intro _i
    rw [integral_exp_mul_sq_gaussianReal 0 1 (by push_cast; linarith)]
    have h2 : (1 : ℝ) - 2 * ((1 : ℝ≥0) : ℝ) * t = 1 - 2 * t := by push_cast; ring
    rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_neg h1.le]
    norm_num
  rw [Finset.prod_congr rfl (fun i _ ↦ hfac i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.rpow_natCast ((1 - 2 * t) ^ (-(1 : ℝ) / 2)) (Module.finrank ℝ E),
    ← Real.rpow_mul h1.le]
  congr 1
  ring

/-- **The squared norm of a standard Gaussian vector of a `d`-dimensional inner product space has
the moment generating function of the chi-squared distribution with `d` degrees of freedom.** -/
lemma mgf_norm_sq_stdGaussian [Nontrivial E] {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun g ↦ ‖g‖ ^ 2) (stdGaussian E) t = mgf id (chiSqMeasure (Module.finrank ℝ E)) t := by
  rw [mgf, integral_exp_mul_norm_sq_stdGaussian ht, mgf_chiSqMeasure Module.finrank_pos ht]

/-- For `t < 1/2`, `exp (t ‖g‖²)` is integrable for a standard Gaussian vector. -/
lemma integrable_exp_mul_norm_sq_stdGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun g ↦ exp (t * ‖g‖ ^ 2)) (stdGaussian E) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integrable_map_measure (by fun_prop) (measurable_sum_smul_orthonormalBasis _).aemeasurable]
  simp_rw [Function.comp_def, exp_mul_norm_sum_smul_sq_eq_prod]
  exact Integrable.fintype_prod fun _ ↦
    integrable_exp_mul_sq_gaussianReal 0 1 (by push_cast; linarith)

/-- For `1/2 ≤ t`, `exp (t x²)` is not integrable for `N(0,1)`: the integrand against the density
is bounded below by the constant `(√(2π))⁻¹`. -/
lemma not_integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : 1 / 2 ≤ t) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x ^ 2)) (gaussianReal 0 1) := by
  intro hint
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hint
  have hconst : Integrable (fun _ : ℝ ↦ (√(2 * π))⁻¹) volume := by
    refine Integrable.mono' hint (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), gaussianPDF,
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), gaussianPDFReal]
    have hle : (1 : ℝ) ≤ exp (t * x ^ 2) * exp (-(x - 0) ^ 2 / (2 * 1)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [sq_nonneg x])
    push_cast
    calc (√(2 * π))⁻¹ = (√(2 * π * 1))⁻¹ * 1 := by norm_num
      _ ≤ (√(2 * π * 1))⁻¹ * (exp (t * x ^ 2) * exp (-(x - 0) ^ 2 / (2 * 1))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = exp (t * x ^ 2) * ((√(2 * π * 1))⁻¹ * exp (-(x - 0) ^ 2 / (2 * 1))) := by ring
  rw [integrable_const_iff] at hconst
  rcases hconst with h | h
  · have : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
    simp only [inv_eq_zero] at h
    linarith
  · exact (isFiniteMeasure_iff _).not.2 (by simp) h

/-- For `1/2 ≤ t`, `exp (t ‖g‖²)` is not integrable for a standard Gaussian vector: bounding the
product over an orthonormal basis below by a single factor reduces to the one-dimensional case. -/
lemma not_integrable_exp_mul_norm_sq_stdGaussian [Nontrivial E] {t : ℝ} (ht : 1 / 2 ≤ t) :
    ¬ Integrable (fun g ↦ exp (t * ‖g‖ ^ 2)) (stdGaussian E) := by
  intro hint
  rw [stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    integrable_map_measure (by fun_prop)
      (measurable_sum_smul_orthonormalBasis _).aemeasurable] at hint
  simp_rw [Function.comp_def, exp_mul_norm_sum_smul_sq_eq_prod] at hint
  have hne : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.1 Module.finrank_pos
  obtain ⟨j⟩ := hne
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hmeas1 : Measurable fun y : ℝ ↦ exp (t * y ^ 2) :=
    Real.measurable_exp.comp ((measurable_id.pow_const 2).const_mul t)
  have hdom : Integrable (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ exp (t * x j ^ 2))
      (Measure.pi fun _ ↦ gaussianReal 0 1) := by
    refine Integrable.mono' hint
      (hmeas1.comp (measurable_pi_apply j)).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, ← Real.exp_sum]
    refine Real.exp_le_exp.2 (Finset.single_le_sum (f := fun i ↦ t * x i ^ 2) ?_
      (Finset.mem_univ j))
    exact fun i _ ↦ mul_nonneg ht0 (sq_nonneg _)
  have h1d : Integrable (fun y : ℝ ↦ exp (t * y ^ 2))
      ((Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1).map fun x ↦ x j) := by
    rw [integrable_map_measure hmeas1.aestronglyMeasurable (measurable_pi_apply j).aemeasurable]
    simpa [Function.comp_def] using hdom
  rw [(measurePreserving_eval (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1) j).map_eq]
    at h1d
  exact not_integrable_exp_mul_sq_gaussianReal ht h1d

/-- **The squared norm of a standard Gaussian vector of a `d`-dimensional inner product space has
the chi-squared distribution with `d` degrees of freedom.** -/
theorem map_norm_sq_stdGaussian_eq_chiSqMeasure [Nontrivial E] :
    (stdGaussian E).map (fun g ↦ ‖g‖ ^ 2) = chiSqMeasure (Module.finrank ℝ E) := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have : IsProbabilityMeasure (chiSqMeasure (Module.finrank ℝ E)) :=
    isProbabilityMeasure_chiSqMeasure hd
  have hmgf : mgf (fun g ↦ ‖g‖ ^ 2) (stdGaussian E)
      = mgf id (chiSqMeasure (Module.finrank ℝ E)) := by
    funext t
    rcases lt_or_ge t (1 / 2) with h | h
    · exact mgf_norm_sq_stdGaussian h
    · rw [mgf, mgf, integral_undef (not_integrable_exp_mul_norm_sq_stdGaussian h), integral_undef]
      simpa [chiSqMeasure] using
        not_integrable_exp_mul_gammaMeasure (a := (Module.finrank ℝ E : ℝ) / 2) (r := 1 / 2)
          (t := t) (by positivity) (by norm_num) (by linarith)
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun g ↦ ‖g‖ ^ 2) (stdGaussian E)) := by
    refine mem_interior.2 ⟨Iio (1 / 2), fun x hx ↦ ?_, isOpen_Iio, by norm_num⟩
    exact integrable_exp_mul_norm_sq_stdGaussian hx
  have := Measure.ext_of_mgf_eq (μ := stdGaussian E)
    (μ' := chiSqMeasure (Module.finrank ℝ E)) (by fun_prop) aemeasurable_id h0 hmgf
  rwa [Measure.map_id] at this

end StdGaussian

end ProbabilityTheory
