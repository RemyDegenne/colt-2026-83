/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Probability.GaussianMGF
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian concentration for smooth Lipschitz functions (Maurey–Pisier)

Let `f : E → ℝ` be `C¹` with `‖∇f‖ ≤ L` everywhere, on a finite-dimensional real inner product
space `E`, and let `μ` be the standard Gaussian measure on `E`. Then `f - μ[f]` has a
sub-Gaussian moment generating function with constant `c_G L²`, where
`c_G = π²/4` (`hasSubgaussianMGF_sub_integral_stdGaussian`):
`∫ exp (λ (f x - μ[f])) ∂μ ≤ exp (c_G L² λ² / 2)`.

The proof is the Maurey–Pisier argument: symmetrization by Jensen's inequality with an
independent copy `g'` of `g`, interpolation `f(g) - f(g') = ∫₀^{π/2} ⟪∇f(g_θ), g'_θ⟫ dθ` along
the quarter circle `g_θ = sin θ • g + cos θ • g'`, `g'_θ = cos θ • g - sin θ • g'`, Jensen's
inequality for the uniform measure on `[0, π/2]`, Fubini, the rotation invariance of `μ ⊗ μ`
(Mathlib `IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero`) and the Gaussian
moment generating function of the linear form `⟪∇f(u), ·⟫`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real InnerProductSpace Set
open scoped RealInnerProductSpace NNReal

namespace ProbabilityTheory

/-- The Gaussian concentration constant `c_G = π²/4` of the Maurey–Pisier argument. -/
noncomputable def gaussianConcentrationConst : ℝ≥0 := ⟨π ^ 2 / 4, by positivity⟩

lemma coe_gaussianConcentrationConst : (gaussianConcentrationConst : ℝ) = π ^ 2 / 4 := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section gradient

variable {f : E → ℝ} {L : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
/-- A differentiable function with `‖∇f‖ ≤ L` is `L`-Lipschitz. -/
lemma lipschitzWith_of_norm_gradient_le (hf : Differentiable ℝ f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) : LipschitzWith L f := by
  refine lipschitzWith_of_nnnorm_fderiv_le hf fun x ↦ ?_
  rw [← toDual_gradient, LinearIsometryEquiv.nnnorm_map]
  exact_mod_cast hL x

omit [MeasurableSpace E] [BorelSpace E] in
/-- A differentiable function with `‖∇f‖ ≤ L` has linear growth. -/
lemma abs_le_of_norm_gradient_le (hf : Differentiable ℝ f) (hL : ∀ x, ‖gradient f x‖ ≤ L)
    (x : E) : |f x| ≤ |f 0| + L * ‖x‖ := by
  have h := (lipschitzWith_of_norm_gradient_le hf hL).dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  calc |f x| = |f x - f 0 + f 0| := by ring_nf
    _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
    _ ≤ L * ‖x‖ + |f 0| := by linarith
    _ = |f 0| + L * ‖x‖ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma abs_inner_gradient_le (hL : ∀ x, ‖gradient f x‖ ≤ L) (x v : E) :
    |⟪gradient f x, v⟫| ≤ L * ‖v‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of a `C¹` function is continuous. -/
lemma ContDiff.continuous_gradient (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have h : gradient f = (toDual ℝ E).symm ∘ fderiv ℝ f := by
    funext x
    rw [Function.comp_apply, ← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  rw [h]
  exact (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

/-- A `C¹` function with bounded gradient is integrable under a Gaussian measure, with all its
exponential moments. -/
lemma IsGaussian.integrable_exp_of_norm_gradient_le {μ : Measure E} [IsGaussian μ]
    (hf : ContDiff ℝ 1 f) (hL : ∀ x, ‖gradient f x‖ ≤ L) (t : ℝ) :
    Integrable (fun x ↦ exp (t * f x)) μ :=
  IsGaussian.integrable_exp_of_abs_le_add_mul_norm hf.continuous.aestronglyMeasurable
    (abs_le_of_norm_gradient_le (hf.differentiable one_ne_zero) hL) t

lemma IsGaussian.integrable_of_norm_gradient_le {μ : Measure E} [IsGaussian μ]
    (hf : ContDiff ℝ 1 f) (hL : ∀ x, ‖gradient f x‖ ≤ L) : Integrable f μ :=
  IsGaussian.integrable_of_abs_le_add_mul_norm hf.continuous.aestronglyMeasurable
    (abs_le_of_norm_gradient_le (hf.differentiable one_ne_zero) hL)

end gradient

section interpolation

variable {f : E → ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `θ ↦ f (sin θ • u + cos θ • v)`. -/
lemma hasDerivAt_comp_quarterCircle (hf : Differentiable ℝ f) (u v : E) (θ : ℝ) :
    HasDerivAt (fun θ ↦ f (sin θ • u + cos θ • v))
      ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ θ := by
  have hγ : HasDerivAt (fun θ ↦ sin θ • u + cos θ • v) (cos θ • u + (-sin θ) • v) θ :=
    ((hasDerivAt_sin θ).smul_const u).add ((hasDerivAt_cos θ).smul_const v)
  have h := (hasGradientAt_iff_hasFDerivAt.1 (hf _).hasGradientAt).comp_hasDerivAt θ hγ
  exact h.congr_deriv (by rw [toDual_apply_apply, sub_eq_add_neg, neg_smul])

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Interpolation along a quarter circle**:
`f u - f v = ∫₀^{π/2} ⟪∇f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ dθ`. -/
lemma sub_eq_integral_quarterCircle (hf : ContDiff ℝ 1 f) (u v : E) :
    f u - f v =
      ∫ θ in (0 : ℝ)..(π / 2), ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ := by
  have hcont : Continuous fun θ : ℝ ↦
      ⟪gradient f (sin θ • u + cos θ • v), cos θ • u - sin θ • v⟫ :=
    (hf.continuous_gradient.comp (by fun_prop)).inner (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ ↦ hasDerivAt_comp_quarterCircle (hf.differentiable one_ne_zero) u v θ)
    (hcont.intervalIntegrable _ _)]
  simp

/-- **Jensen's inequality for the uniform measure on `[0, π/2]`**: for a continuous `h`,
`exp (s ∫₀^{π/2} h) ≤ (2/π) ∫₀^{π/2} exp (π s / 2 · h θ) dθ`. -/
lemma exp_mul_integral_le_integral_exp {h : ℝ → ℝ} (hc : Continuous h) (s : ℝ) :
    exp (s * ∫ θ in (0 : ℝ)..(π / 2), h θ) ≤
      2 / π * ∫ θ in (0 : ℝ)..(π / 2), exp (π * s / 2 * h θ) := by
  have hπ : 0 < π / 2 := by positivity
  set ν : Measure ℝ := volume.restrict (Ioc 0 (π / 2)) with hν
  have hν_univ : ν.real univ = π / 2 := by
    rw [hν, measureReal_restrict_apply_univ, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hπ.le]
  have : NeZero ν := ⟨fun h0 ↦ by simp [h0] at hν_univ; linarith⟩
  have hint : ∀ g : ℝ → ℝ, Continuous g → Integrable g ν := fun g hg ↦
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hJ := ConvexOn.map_average_le (μ := ν) (f := fun θ ↦ π * s / 2 * h θ) convexOn_exp
    continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    (hint _ (by fun_prop)) (hint _ (by fun_prop))
  rw [average_eq, average_eq, hν_univ, smul_eq_mul, smul_eq_mul, integral_const_mul] at hJ
  rw [intervalIntegral.integral_of_le hπ.le, intervalIntegral.integral_of_le hπ.le]
  have h1 : (π / 2)⁻¹ * (π * s / 2 * ∫ θ, h θ ∂ν) = s * ∫ θ, h θ ∂ν := by
    field_simp
  rw [h1, inv_div] at hJ
  exact hJ

end interpolation

section rotation

variable {μ : Measure E} [IsGaussian μ]

/-- For a centered Gaussian measure `μ`, the law of
`(sin θ • g + cos θ • g', cos θ • g - sin θ • g')` under `μ ⊗ μ` is `μ ⊗ μ`: the integrals of
`Φ ∘ rotation θ ∘ swap` and of `Φ` coincide. -/
lemma integral_comp_rotation_swap_prod (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0) {Φ : E × E → ℝ}
    (hΦ : Continuous Φ) (θ : ℝ) :
    ∫ p, Φ (ContinuousLinearMap.rotation θ p.swap) ∂(μ.prod μ) = ∫ p, Φ p ∂(μ.prod μ) := by
  have h1 : (μ.prod μ).map Prod.swap = μ.prod μ := Measure.prod_swap
  have h2 := IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero (μ := μ) hμ θ
  calc ∫ p, Φ (ContinuousLinearMap.rotation θ p.swap) ∂(μ.prod μ)
      = ∫ q, Φ (ContinuousLinearMap.rotation θ q) ∂((μ.prod μ).map Prod.swap) :=
        (integral_map measurable_swap.aemeasurable
          (hΦ.comp (ContinuousLinearMap.rotation θ).continuous).aestronglyMeasurable).symm
    _ = ∫ q, Φ (ContinuousLinearMap.rotation θ q) ∂(μ.prod μ) := by rw [h1]
    _ = ∫ r, Φ r ∂((μ.prod μ).map (ContinuousLinearMap.rotation θ)) :=
        (integral_map (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable
          hΦ.aestronglyMeasurable).symm
    _ = ∫ r, Φ r ∂(μ.prod μ) := by rw [h2]

end rotation

section maureyPisier

variable {f : E → ℝ} {L : ℝ≥0}

/-- **MGF of the rotated gradient term**: for `(g, g') ~ μ ⊗ μ` with `μ` the standard Gaussian
measure, `∫ exp (s ⟪∇f(g), g'⟫) = ∫ exp (s² ‖∇f(g)‖² / 2) ≤ exp (s² L² / 2)`. -/
lemma integral_exp_inner_gradient_prod_stdGaussian_le (hf : ContDiff ℝ 1 f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) (s : ℝ) :
    ∫ p, exp (s * ⟪gradient f p.1, p.2⟫) ∂((stdGaussian E).prod (stdGaussian E)) ≤
      exp (s ^ 2 * L ^ 2 / 2) := by
  have hint : Integrable (fun p : E × E ↦ exp (s * ⟪gradient f p.1, p.2⟫))
      ((stdGaussian E).prod (stdGaussian E)) := by
    refine ((integrable_const (1 : ℝ)).mul_prod
      (IsGaussian.integrable_exp_mul_norm (μ := stdGaussian E) (|s| * L))).mono'
      (continuous_const.mul ((hf.continuous_gradient.comp continuous_fst).inner
        continuous_snd)).rexp.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, one_mul]
    refine Real.exp_le_exp.2 ?_
    calc s * ⟪gradient f p.1, p.2⟫ ≤ |s * ⟪gradient f p.1, p.2⟫| := le_abs_self _
      _ = |s| * |⟪gradient f p.1, p.2⟫| := abs_mul _ _
      _ ≤ |s| * (L * ‖p.2‖) :=
          mul_le_mul_of_nonneg_left (abs_inner_gradient_le hL _ _) (abs_nonneg _)
      _ = |s| * L * ‖p.2‖ := by ring
  rw [integral_prod _ hint]
  simp_rw [integral_exp_mul_inner_stdGaussian]
  calc ∫ u, exp (s ^ 2 * ‖gradient f u‖ ^ 2 / 2) ∂stdGaussian E
      ≤ ∫ _, exp (s ^ 2 * L ^ 2 / 2) ∂stdGaussian E :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ (exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun u ↦ exp_le_exp.2 (by
            gcongr
            exact hL u))
    _ = exp (s ^ 2 * L ^ 2 / 2) := by simp

/-- **Maurey–Pisier Gaussian concentration**: a `C¹` function `f` with `‖∇f‖ ≤ L` everywhere
satisfies, under the standard Gaussian measure `μ`,
`∫ exp (λ (f x - μ[f])) ∂μ ≤ exp (c_G L² λ² / 2)` with `c_G = π²/4`, i.e. `f - μ[f]` has a
sub-Gaussian moment generating function with constant `c_G L²`. -/
theorem hasSubgaussianMGF_sub_integral_stdGaussian (hf : ContDiff ℝ 1 f)
    (hL : ∀ x, ‖gradient f x‖ ≤ L) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian E)
      (gaussianConcentrationConst * L ^ 2) (stdGaussian E) := by
  set μ := stdGaussian E with hμ
  set m := ∫ y, f y ∂μ with hm
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hfi : Integrable f μ := IsGaussian.integrable_of_norm_gradient_le hf hL
  have hexp : ∀ t, Integrable (fun x ↦ exp (t * f x)) μ :=
    IsGaussian.integrable_exp_of_norm_gradient_le hf hL
  have hint_sub : ∀ t, Integrable (fun x ↦ exp (t * (f x - m))) μ := fun t ↦ by
    refine ((hexp t).const_mul (exp (-(t * m)))).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  refine ⟨hint_sub, fun t ↦ ?_⟩
  change ∫ x, exp (t * (f x - m)) ∂μ ≤ exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2)
  -- Step 1: symmetrization by Jensen's inequality in the independent copy
  have hprod_int : Integrable (fun p : E × E ↦ exp (t * (f p.1 - f p.2))) (μ.prod μ) := by
    refine ((hexp t).mul_prod (hexp (-t))).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    ring_nf
  have step1 : ∫ x, exp (t * (f x - m)) ∂μ ≤ ∫ p, exp (t * (f p.1 - f p.2)) ∂(μ.prod μ) := by
    rw [integral_prod _ hprod_int]
    refine integral_mono (hint_sub t) hprod_int.integral_prod_left fun u ↦ ?_
    have hJ := ConvexOn.map_integral_le (μ := μ) (f := fun v ↦ t * (f u - f v)) convexOn_exp
      continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
      (((integrable_const (f u)).sub hfi).const_mul t)
      (((hexp (-t)).const_mul (exp (t * f u))).congr (Filter.Eventually.of_forall fun v ↦ by
        dsimp only [Function.comp_apply]
        rw [← Real.exp_add]
        ring_nf))
    rw [integral_const_mul, integral_sub (integrable_const _) hfi, integral_const, probReal_univ,
      one_smul] at hJ
    exact hJ
  -- Steps 2 and 3: interpolation and Jensen's inequality on the quarter circle
  set K : E × E → ℝ → ℝ := fun p θ ↦
    exp (π * t / 2 * ⟪gradient f (sin θ • p.1 + cos θ • p.2), cos θ • p.1 - sin θ • p.2⟫) with hK
  have step23 : ∀ p : E × E, exp (t * (f p.1 - f p.2)) ≤ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ :=
    fun p ↦ by
      rw [sub_eq_integral_quarterCircle hf p.1 p.2]
      exact exp_mul_integral_le_integral_exp
        ((hf.continuous_gradient.comp (by fun_prop)).inner (by fun_prop)) t
  -- Step 4: Fubini and rotation invariance
  set ν : Measure ℝ := volume.restrict (Ioc 0 (π / 2)) with hν
  have hK_cont : Continuous (Function.uncurry K) :=
    (continuous_const.mul ((hf.continuous_gradient.comp (by fun_prop)).inner (by fun_prop))).rexp
  have hK_int : Integrable (Function.uncurry K) ((μ.prod μ).prod ν) := by
    have hD : Integrable (fun p : E × E ↦
        exp (π * |t| / 2 * L * ‖p.1‖) * exp (π * |t| / 2 * L * ‖p.2‖)) (μ.prod μ) :=
      (IsGaussian.integrable_exp_mul_norm _).mul_prod (IsGaussian.integrable_exp_mul_norm _)
    refine (hD.mul_prod (integrable_const (1 : ℝ))).mono' hK_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q ↦ ?_)
    change ‖exp (π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
      cos q.2 • q.1.1 - sin q.2 • q.1.2⟫)‖ ≤ _
    rw [Real.norm_of_nonneg (exp_pos _).le, mul_one, ← Real.exp_add]
    refine exp_le_exp.2 ?_
    have h1 := abs_inner_gradient_le hL (sin q.2 • q.1.1 + cos q.2 • q.1.2)
      (cos q.2 • q.1.1 - sin q.2 • q.1.2)
    have h2 : ‖cos q.2 • q.1.1 - sin q.2 • q.1.2‖ ≤ ‖q.1.1‖ + ‖q.1.2‖ := by
      calc ‖cos q.2 • q.1.1 - sin q.2 • q.1.2‖
          ≤ ‖cos q.2 • q.1.1‖ + ‖sin q.2 • q.1.2‖ := norm_sub_le _ _
        _ = |cos q.2| * ‖q.1.1‖ + |sin q.2| * ‖q.1.2‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖q.1.1‖ + 1 * ‖q.1.2‖ := by
            gcongr
            exacts [abs_cos_le_one _, abs_sin_le_one _]
        _ = ‖q.1.1‖ + ‖q.1.2‖ := by ring
    have h3 : |π * t / 2| = π * |t| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_two]
    calc π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫
        ≤ |π * t / 2 * ⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫| := le_abs_self _
      _ = π * |t| / 2 * |⟪gradient f (sin q.2 • q.1.1 + cos q.2 • q.1.2),
          cos q.2 • q.1.1 - sin q.2 • q.1.2⟫| := by rw [abs_mul, h3]
      _ ≤ π * |t| / 2 * (L * (‖q.1.1‖ + ‖q.1.2‖)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 L.2)
      _ = π * |t| / 2 * L * ‖q.1.1‖ + π * |t| / 2 * L * ‖q.1.2‖ := by ring
  have hint2 : Integrable (fun p ↦ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) (μ.prod μ) := by
    simp_rw [intervalIntegral.integral_of_le hπ.le]
    exact hK_int.integral_prod_left.const_mul _
  have step4 : ∫ p, (2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) ∂(μ.prod μ) =
      2 / π * ∫ θ in (0 : ℝ)..(π / 2), ∫ p, K p θ ∂(μ.prod μ) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [intervalIntegral.integral_of_le hπ.le]
    exact integral_integral_swap hK_int
  have step_rot : ∀ θ, ∫ p, K p θ ∂(μ.prod μ) ≤ exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := fun θ ↦ by
    have h := integral_exp_inner_gradient_prod_stdGaussian_le hf hL (π * t / 2)
    rw [← integral_comp_rotation_swap_prod (μ := μ) integral_strongDual_stdGaussian
      (Φ := fun p ↦ exp (π * t / 2 * ⟪gradient f p.1, p.2⟫))
      ((continuous_const.mul ((hf.continuous_gradient.comp continuous_fst).inner
        continuous_snd)).rexp) θ] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    funext p
    have e1 : sin θ • p.1 + cos θ • p.2 = cos θ • p.2 + sin θ • p.1 := add_comm _ _
    have e2 : cos θ • p.1 - sin θ • p.2 = -sin θ • p.2 + cos θ • p.1 := by
      rw [neg_smul, sub_eq_add_neg, add_comm]
    simp only [hK]
    rw [e1, e2]
    rfl
  have hint_θ : IntervalIntegrable (fun θ ↦ ∫ p, K p θ ∂(μ.prod μ)) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le]
    exact hK_int.integral_prod_right
  -- Step 5: conclusion
  calc ∫ x, exp (t * (f x - m)) ∂μ
      ≤ ∫ p, exp (t * (f p.1 - f p.2)) ∂(μ.prod μ) := step1
    _ ≤ ∫ p, (2 / π * ∫ θ in (0 : ℝ)..(π / 2), K p θ) ∂(μ.prod μ) :=
        integral_mono hprod_int hint2 step23
    _ = 2 / π * ∫ θ in (0 : ℝ)..(π / 2), ∫ p, K p θ ∂(μ.prod μ) := step4
    _ ≤ 2 / π * ∫ θ in (0 : ℝ)..(π / 2), exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := by
        gcongr
        exact intervalIntegral.integral_mono_on hπ.le hint_θ intervalIntegrable_const
          fun θ _ ↦ step_rot θ
    _ = exp ((π * t / 2) ^ 2 * L ^ 2 / 2) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
          div_mul_div_comm, mul_comm (2 : ℝ) π, div_self (by positivity), one_mul]
    _ = exp (↑(gaussianConcentrationConst * L ^ 2) * t ^ 2 / 2) := by
        congr 1
        rw [NNReal.coe_mul, NNReal.coe_pow, coe_gaussianConcentrationConst]
        ring

end maureyPisier

end ProbabilityTheory
