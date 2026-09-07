/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.SteinIdentity

/-!
# Stein's identity for functions of exponential growth

The Stein identities of `Maiti2026Power.Mathlib.Probability.SteinIdentity` assume a bounded
derivative. Here we relax this hypothesis to `C¹` functions `F` such that `|F x|` and `‖DF(x)‖`
are bounded by `A * exp (B * ‖x‖)`: such functions, and their products with linear forms, are
integrable under every Gaussian measure (Fernique's theorem, `IsGaussian.integrable_exp_mul_norm`),
and the one-dimensional identity only needs integrability
(`integral_sub_mul_gaussianReal_of_integrable`).

## Main results

* `integral_sub_mul_gaussianReal_of_integrable`: one-dimensional **Stein's identity**
  `E[(ξ - μ) f(ξ)] = v E[f'(ξ)]` for `ξ ~ N(μ, v)`, from integrability hypotheses only.
* `IsGaussian.integrable_of_abs_le_mul_exp`, `IsGaussian.integrable_inner_mul_of_abs_le_mul_exp`,
  `IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le_mul_exp`: integrability under a Gaussian
  measure of functions of exponential growth.
* `integral_inner_mul_stdGaussian_of_le_exp`: **Stein's identity** `E[⟪a, g⟫ F(g)] = E[DF(g) a]`
  for `g ~ N(0, I)` on a finite-dimensional inner product space and `F` of exponential growth.
* `integral_inner_mul_multivariateGaussian_of_le_exp`: `E[⟪a, X⟫ F(X)] = E[DF(X) (S a)]` for
  `X ~ N(0, S)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped RealInnerProductSpace NNReal MatrixOrder

/-- `x ≤ exp x` for every real `x`. -/
lemma Real.le_exp_self (x : ℝ) : x ≤ rexp x :=
  (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)

namespace ProbabilityTheory

section real

variable {f : ℝ → ℝ} {μ : ℝ} {v : ℝ≥0}

/-- **Stein's identity** for `N(μ, v)` from integrability hypotheses only:
`E[(ξ - μ) f(ξ)] = v E[f'(ξ)]` when `f`, `x ↦ (x - μ) * f x` and `f'` are integrable.
Also true for `v = 0`. -/
lemma integral_sub_mul_gaussianReal_of_integrable (hf : Differentiable ℝ f)
    (h1 : Integrable f (gaussianReal μ v))
    (h2 : Integrable (fun x ↦ (x - μ) * f x) (gaussianReal μ v))
    (h3 : Integrable (deriv f) (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂gaussianReal μ v = v * ∫ x, deriv f x ∂gaussianReal μ v := by
  by_cases hv : v = 0
  · simp [hv]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  -- integration by parts on `ℝ` with `u = gaussianPDFReal μ v` and `v = f`
  have h_ibp : ∫ x, gaussianPDFReal μ v x * deriv f x
      = - ∫ x, (-((x - μ) / v) * gaussianPDFReal μ v x) * f x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ ↦ hasDerivAt_gaussianPDFReal μ v x) (fun x _ ↦ (hf x).hasDerivAt) ?_ ?_ ?_
    · exact (integrable_gaussianReal_iff hv).mp h3
    · have h := ((integrable_gaussianReal_iff hv).mp h2).const_mul (-(v : ℝ)⁻¹)
      refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply]
      ring
    · exact (integrable_gaussianReal_iff hv).mp h1
  calc ∫ x, (x - μ) * f x ∂gaussianReal μ v
      = ∫ x, gaussianPDFReal μ v x * ((x - μ) * f x) := by
        simp only [integral_gaussianReal_eq_integral_smul hv, smul_eq_mul]
    _ = ∫ x, -v * ((-((x - μ) / v) * gaussianPDFReal μ v x) * f x) := by
        congr 1 with x
        field_simp
    _ = -v * ∫ x, (-((x - μ) / v) * gaussianPDFReal μ v x) * f x := integral_const_mul _ _
    _ = v * ∫ x, gaussianPDFReal μ v x * deriv f x := by rw [h_ibp]; ring
    _ = v * ∫ x, deriv f x ∂gaussianReal μ v := by
        simp only [integral_gaussianReal_eq_integral_smul hv, smul_eq_mul]

/-- **Stein's identity** for the standard Gaussian from integrability hypotheses only:
`E[ξ f(ξ)] = E[f'(ξ)]` when `f`, `x ↦ x * f x` and `f'` are integrable. -/
lemma integral_mul_gaussianReal_zero_one_of_integrable (hf : Differentiable ℝ f)
    (h1 : Integrable f (gaussianReal 0 1)) (h2 : Integrable (fun x ↦ x * f x) (gaussianReal 0 1))
    (h3 : Integrable (deriv f) (gaussianReal 0 1)) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, deriv f x ∂gaussianReal 0 1 := by
  simpa using integral_sub_mul_gaussianReal_of_integrable hf h1 (by simpa using h2) h3

/-- `exp (B * |x|)` is integrable under a real Gaussian measure. -/
lemma integrable_exp_mul_abs_gaussianReal (B : ℝ) (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x ↦ rexp (B * |x|)) (gaussianReal μ v) :=
  integrable_exp_mul_abs (X := id) (integrable_exp_mul_gaussianReal B)
    (integrable_exp_mul_gaussianReal (-B))

/-- A measurable real function bounded by `C * exp (D * |x|)` is integrable under a real Gaussian
measure. -/
lemma integrable_gaussianReal_of_abs_le_mul_exp {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal μ v)) {C D : ℝ}
    (hb : ∀ x, |g x| ≤ C * rexp (D * |x|)) : Integrable g (gaussianReal μ v) :=
  ((integrable_exp_mul_abs_gaussianReal D μ v).const_mul C).mono' hg
    (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hb x))

/-- For a measurable real function `g` bounded by `C * exp (D * |x|)`, `x ↦ x * g x` is integrable
under a real Gaussian measure. -/
lemma integrable_mul_gaussianReal_of_abs_le_mul_exp {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal μ v)) {C D : ℝ}
    (hb : ∀ x, |g x| ≤ C * rexp (D * |x|)) :
    Integrable (fun x ↦ x * g x) (gaussianReal μ v) := by
  refine integrable_gaussianReal_of_abs_le_mul_exp (C := C) (D := D + 1) (by fun_prop) fun x ↦ ?_
  calc |x * g x| = |x| * |g x| := abs_mul _ _
    _ ≤ rexp |x| * (C * rexp (D * |x|)) :=
        mul_le_mul (Real.le_exp_self _) (hb x) (abs_nonneg _) (exp_pos _).le
    _ = C * rexp ((D + 1) * |x|) := by rw [add_mul, one_mul, Real.exp_add]; ring

end real

section normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
  {F : E → ℝ} {A B : ℝ}

/-- A measurable function bounded by `A * exp (B * ‖x‖)` is integrable under a Gaussian
measure. -/
lemma IsGaussian.integrable_of_abs_le_mul_exp (hF : AEStronglyMeasurable F μ)
    (hb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) : Integrable F μ :=
  ((IsGaussian.integrable_exp_mul_norm B).const_mul A).mono' hF
    (Filter.Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hb x))

/-- For a measurable function `F` bounded by `A * exp (B * ‖x‖)`, `x ↦ ‖x‖ * F x` is integrable
under a Gaussian measure. -/
lemma IsGaussian.integrable_norm_mul_of_abs_le_mul_exp (hF : AEStronglyMeasurable F μ)
    (hb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) : Integrable (fun x ↦ ‖x‖ * F x) μ := by
  refine IsGaussian.integrable_of_abs_le_mul_exp (A := A) (B := B + 1) (by fun_prop) fun x ↦ ?_
  calc |‖x‖ * F x| = ‖x‖ * |F x| := by rw [abs_mul, abs_norm]
    _ ≤ rexp ‖x‖ * (A * rexp (B * ‖x‖)) :=
        mul_le_mul (Real.le_exp_self _) (hb x) (abs_nonneg _) (exp_pos _).le
    _ = A * rexp ((B + 1) * ‖x‖) := by rw [add_mul, one_mul, Real.exp_add]; ring

/-- `DF(x) a` is integrable under a Gaussian measure when `F` is `C¹` with `‖DF(x)‖` bounded by
`A * exp (B * ‖x‖)`. -/
lemma IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le_mul_exp (hF : ContDiff ℝ 1 F)
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ A * rexp (B * ‖x‖)) (a : E) :
    Integrable (fun x ↦ fderiv ℝ F x a) μ :=
  IsGaussian.integrable_of_abs_le_mul_exp (A := A * ‖a‖) (B := B)
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable fun x ↦ by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ F x a‖ ≤ ‖fderiv ℝ F x‖ * ‖a‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ A * rexp (B * ‖x‖) * ‖a‖ := mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _)
        _ = A * ‖a‖ * rexp (B * ‖x‖) := by ring

end normed

section innerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
  {F : E → ℝ} {A B : ℝ}

/-- For a measurable function `F` bounded by `A * exp (B * ‖x‖)`, `x ↦ ⟪a, x⟫ * F x` is
integrable under a Gaussian measure. -/
lemma IsGaussian.integrable_inner_mul_of_abs_le_mul_exp (hF : AEStronglyMeasurable F μ)
    (hb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) (a : E) :
    Integrable (fun x ↦ ⟪a, x⟫ * F x) μ := by
  refine ((IsGaussian.integrable_norm_mul_of_abs_le_mul_exp hF hb).norm.const_mul ‖a‖).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, norm_mul, norm_norm, ← mul_assoc]
  gcongr
  exact norm_inner_le_norm _ _

end innerProduct

section euclidean

variable {n : ℕ} {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {A B : ℝ}

/-- The norm of `y` with `t` inserted at position `i` is at most `|t| + ‖y‖`. -/
lemma norm_toLp_insertNth_le (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    ‖(WithLp.toLp 2 (Fin.insertNth i t y) : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤
      |t| + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Real.norm_eq_abs, sq_abs]
  have hs : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  calc √(t ^ 2 + ∑ j, y j ^ 2) ≤ √((|t| + √(∑ j, y j ^ 2)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ j, y j ^ 2), abs_nonneg t, sq_abs t]
    _ = |t| + √(∑ j, y j ^ 2) := Real.sqrt_sq (by positivity)

/-- Growth transfer to the section `t ↦ G (y with t inserted at i)`: if
`|G x| ≤ A * exp (B * ‖x‖)`, then the section is bounded by a constant times `exp (|B| * |t|)`. -/
lemma abs_apply_toLp_insertNth_le {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hA : 0 ≤ A)
    (hG : ∀ x, |G x| ≤ A * rexp (B * ‖x‖)) (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    |G (WithLp.toLp 2 (Fin.insertNth i t y))| ≤
      A * rexp (|B| * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖) * rexp (|B| * |t|) := by
  rw [mul_assoc, ← Real.exp_add]
  refine (hG _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA)
  calc B * ‖(WithLp.toLp 2 (Fin.insertNth i t y) : EuclideanSpace ℝ (Fin (n + 1)))‖
      ≤ |B| * ‖(WithLp.toLp 2 (Fin.insertNth i t y) : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _)
    _ ≤ |B| * (|t| + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖) :=
        mul_le_mul_of_nonneg_left (norm_toLp_insertNth_le i t y) (abs_nonneg B)
    _ = |B| * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ + |B| * |t| := by ring

/-- **Stein's identity** for the `i`-th coordinate of a standard Gaussian vector:
`E[g_i F(g)] = E[∂_i F(g)]` for `C¹` functions of exponential growth. -/
lemma integral_apply_mul_stdGaussian_of_le_exp (hF : ContDiff ℝ 1 F)
    (hFb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ A * rexp (B * ‖x‖))
    (i : Fin (n + 1)) :
    ∫ x, x i * F x ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) =
      ∫ x, fderiv ℝ F x (EuclideanSpace.single i 1)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  have hA : 0 ≤ A := by simpa using (abs_nonneg _).trans (hFb 0)
  have hL' : ∀ x, |fderiv ℝ F x (EuclideanSpace.single i 1)| ≤ A * rexp (B * ‖x‖) := fun x ↦ by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖
        ≤ ‖fderiv ℝ F x‖ * ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ A * rexp (B * ‖x‖) := by rw [PiLp.norm_single, norm_one, mul_one]; exact hL _
  have hint1 : Integrable (fun x ↦ x i * F x) (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) := by
    have := IsGaussian.integrable_inner_mul_of_abs_le_mul_exp
      (μ := stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) hF.continuous.aestronglyMeasurable hFb
      (EuclideanSpace.single i 1)
    simpa [EuclideanSpace.inner_single_left] using this
  have hint2 : Integrable (fun x ↦ fderiv ℝ F x (EuclideanSpace.single i 1))
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) :=
    IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le_mul_exp hF hL _
  rw [integral_stdGaussian_eq_integral_insertNth hint1 i,
    integral_stdGaussian_eq_integral_insertNth hint2 i]
  congr 1
  ext y
  simp only [Fin.insertNth_apply_same]
  have hd : ∀ t, HasDerivAt (fun t ↦ F (WithLp.toLp 2 (Fin.insertNth i t y)))
      (fderiv ℝ F (WithLp.toLp 2 (Fin.insertNth i t y)) (EuclideanSpace.single i 1)) t := fun t ↦
    ((hF.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_toLp_insertNth i y t)
  have hd' : deriv (fun t ↦ F (WithLp.toLp 2 (Fin.insertNth i t y))) =
      fun t ↦ fderiv ℝ F (WithLp.toLp 2 (Fin.insertNth i t y)) (EuclideanSpace.single i 1) :=
    funext fun t ↦ (hd t).deriv
  have hc : Continuous fun t ↦
      (WithLp.toLp 2 (Fin.insertNth i t y) : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_toLp_insertNth i y t).continuousAt
  have h := integral_mul_gaussianReal_zero_one_of_integrable (fun t ↦ (hd t).differentiableAt)
    (integrable_gaussianReal_of_abs_le_mul_exp (hF.continuous.comp hc).aestronglyMeasurable
      (abs_apply_toLp_insertNth_le hA hFb i y))
    (integrable_mul_gaussianReal_of_abs_le_mul_exp (hF.continuous.comp hc).aestronglyMeasurable
      (abs_apply_toLp_insertNth_le hA hFb i y)) (by
      rw [hd']
      exact integrable_gaussianReal_of_abs_le_mul_exp
        (((hF.continuous_fderiv one_ne_zero).comp hc).clm_apply
          continuous_const).aestronglyMeasurable (abs_apply_toLp_insertNth_le hA hL' i y))
  rw [hd'] at h
  exact h

/-- **Stein's identity** on `ℝ^{n+1}` for `C¹` functions of exponential growth:
`E[⟪a, g⟫ F(g)] = E[DF(g) a]`. -/
lemma integral_inner_mul_stdGaussian_euclidean_of_le_exp (hF : ContDiff ℝ 1 F)
    (hFb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ A * rexp (B * ‖x‖))
    (a : EuclideanSpace ℝ (Fin (n + 1))) :
    ∫ x, ⟪a, x⟫ * F x ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) =
      ∫ x, fderiv ℝ F x a ∂stdGaussian (EuclideanSpace ℝ (Fin (n + 1))) := by
  have ha : a = ∑ j, a j • (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin (n + 1))) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr a]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  have h1 : ∀ x : EuclideanSpace ℝ (Fin (n + 1)), ⟪a, x⟫ * F x = ∑ j, a j * (x j * F x) := by
    intro x
    conv_lhs => rw [ha]
    simp [sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left, Finset.sum_mul,
      mul_assoc]
  have h2 : ∀ x : EuclideanSpace ℝ (Fin (n + 1)),
      fderiv ℝ F x a = ∑ j, a j * fderiv ℝ F x (EuclideanSpace.single j 1) := by
    intro x
    conv_lhs => rw [ha]
    simp [map_sum, map_smul]
  simp_rw [h1, h2]
  rw [integral_finsetSum _ fun j _ ↦ ?_, integral_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, integral_const_mul,
      integral_apply_mul_stdGaussian_of_le_exp hF hFb hL j]
  · exact (IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le_mul_exp hF hL _).const_mul _
  · have := IsGaussian.integrable_inner_mul_of_abs_le_mul_exp
      (μ := stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) hF.continuous.aestronglyMeasurable hFb
      (EuclideanSpace.single j 1)
    simpa [EuclideanSpace.inner_single_left] using this.const_mul (a j)

end euclidean

section general

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : E → ℝ} {A B : ℝ}

/-- **Stein's identity** (Gaussian integration by parts) for `C¹` functions of exponential
growth: if `|F x| ≤ A * exp (B * ‖x‖)` and `‖DF(x)‖ ≤ A * exp (B * ‖x‖)`, then for the standard
Gaussian measure on a finite-dimensional inner product space `E`, `E[⟪a, g⟫ F(g)] = E[DF(g) a]`. -/
lemma integral_inner_mul_stdGaussian_of_le_exp (hF : ContDiff ℝ 1 F)
    (hFb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖)) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ A * rexp (B * ‖x‖))
    (a : E) :
    ∫ x, ⟪a, x⟫ * F x ∂stdGaussian E = ∫ x, fderiv ℝ F x a ∂stdGaussian E := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ E = n := ⟨_, rfl⟩
  rcases n with _ | n
  · have ha : a = 0 := finrank_zero_iff_forall_zero.1 hn a
    simp [ha]
  have hA : 0 ≤ A := by simpa using (abs_nonneg _).trans (hFb 0)
  let b : OrthonormalBasis (Fin (n + 1)) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hn)
  let e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] E := b.repr.symm
  have h1 : ∀ y, ⟪a, e y⟫ = ⟪b.repr a, y⟫ := fun y ↦ by
    rw [← b.repr.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have h2 : ∀ y, fderiv ℝ F (e y) a = fderiv ℝ (F ∘ e) y (b.repr a) := fun y ↦ by
    rw [show (F ∘ e) = F ∘ e.toContinuousLinearEquiv from rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    simp [e]
  have hFe : ContDiff ℝ 1 (F ∘ e) := hF.comp e.contDiff
  have hFeb : ∀ y, |(F ∘ e) y| ≤ A * rexp (B * ‖y‖) := fun y ↦ by
    rw [Function.comp_apply, ← e.norm_map y]
    exact hFb _
  have hLe : ∀ y, ‖fderiv ℝ (F ∘ e) y‖ ≤ A * rexp (B * ‖y‖) := fun y ↦ by
    rw [show (F ∘ e) = F ∘ e.toContinuousLinearEquiv from rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA (exp_pos _).le) fun w ↦ ?_
    rw [ContinuousLinearMap.comp_apply]
    calc ‖fderiv ℝ F (e.toContinuousLinearEquiv y) (e.toContinuousLinearEquiv w)‖
        ≤ ‖fderiv ℝ F (e.toContinuousLinearEquiv y)‖ * ‖e.toContinuousLinearEquiv w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ A * rexp (B * ‖y‖) * ‖w‖ := by
          rw [show e.toContinuousLinearEquiv w = e w from rfl, e.norm_map]
          gcongr
          exact (hL _).trans_eq
            (by rw [show e.toContinuousLinearEquiv y = e y from rfl, e.norm_map])
  rw [← stdGaussian_map e, integral_map (by fun_prop) ?_, integral_map (by fun_prop) ?_]
  · simp_rw [h1, h2]
    exact integral_inner_mul_stdGaussian_euclidean_of_le_exp hFe hFeb hLe (b.repr a)
  · exact ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).mul hF.continuous).aestronglyMeasurable

end general

section multivariate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : EuclideanSpace ℝ ι → ℝ} {A B : ℝ}

/-- **Stein's identity** for a centered Gaussian vector `X ~ N(0, S)` of `ℝ^ι` and `C¹`
functions of exponential growth: `E[⟪a, X⟫ F(X)] = E[DF(X) (S a)]`, i.e.
`E[X_i F(X)] = ∑ j, S i j E[∂_j F(X)]`. -/
lemma integral_inner_mul_multivariateGaussian_of_le_exp {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hF : ContDiff ℝ 1 F) (hFb : ∀ x, |F x| ≤ A * rexp (B * ‖x‖))
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ A * rexp (B * ‖x‖)) (a : EuclideanSpace ℝ ι) :
    ∫ x, ⟪a, x⟫ * F x ∂multivariateGaussian 0 S =
      ∫ x, fderiv ℝ F x (Matrix.toEuclideanCLM (𝕜 := ℝ) S a) ∂multivariateGaussian 0 S := by
  have hA : 0 ≤ A := by simpa using (abs_nonneg _).trans (hFb 0)
  set M := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hM
  have hmap : multivariateGaussian 0 S = (stdGaussian (EuclideanSpace ℝ ι)).map M := by
    rw [← multivariateGaussian_zero_one,
      multivariateGaussian_zero_map_toEuclideanCLM Matrix.PosSemidef.one, Matrix.mul_one,
      Matrix.transpose_sqrt, hS.sqrt_mul_sqrt]
  have hsymm : ∀ x y, ⟪x, M y⟫ = ⟪M x, y⟫ := fun x y ↦ by
    rw [← ContinuousLinearMap.adjoint_inner_left, hM, Matrix.adjoint_toEuclideanCLM,
      Matrix.transpose_sqrt]
  have hMM : ∀ x, M (M x) = Matrix.toEuclideanCLM (𝕜 := ℝ) S x := fun x ↦ by
    change (M * M) x = _
    rw [hM, ← map_mul, hS.sqrt_mul_sqrt]
  have hFM : ContDiff ℝ 1 (F ∘ M) := hF.comp M.contDiff
  have hdM : ∀ g, fderiv ℝ (F ∘ M) g = (fderiv ℝ F (M g)).comp M := fun g ↦ by
    rw [fderiv_comp g (hF.differentiable one_ne_zero _) M.differentiableAt, M.fderiv]
  -- growth bounds for `F ∘ M`, with constants `A * max 1 ‖M‖` and `|B| * ‖M‖`
  have hexp : ∀ g, rexp (B * ‖M g‖) ≤ rexp (|B| * ‖M‖ * ‖g‖) := fun g ↦ by
    refine Real.exp_le_exp.2 ?_
    calc B * ‖M g‖ ≤ |B| * ‖M g‖ := mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg _)
      _ ≤ |B| * (‖M‖ * ‖g‖) := mul_le_mul_of_nonneg_left (M.le_opNorm g) (abs_nonneg B)
      _ = |B| * ‖M‖ * ‖g‖ := by ring
  have hA' : 0 ≤ A * max 1 ‖M‖ := mul_nonneg hA (zero_le_one.trans (le_max_left _ _))
  have hFMb : ∀ g, |(F ∘ M) g| ≤ A * max 1 ‖M‖ * rexp (|B| * ‖M‖ * ‖g‖) := fun g ↦
    calc |(F ∘ M) g| ≤ A * rexp (B * ‖M g‖) := hFb _
      _ ≤ A * max 1 ‖M‖ * rexp (|B| * ‖M‖ * ‖g‖) :=
        mul_le_mul (le_mul_of_one_le_right hA (le_max_left _ _)) (hexp g) (exp_pos _).le hA'
  have hLM : ∀ g, ‖fderiv ℝ (F ∘ M) g‖ ≤ A * max 1 ‖M‖ * rexp (|B| * ‖M‖ * ‖g‖) := fun g ↦ by
    rw [hdM]
    calc ‖(fderiv ℝ F (M g)).comp M‖ ≤ ‖fderiv ℝ F (M g)‖ * ‖M‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A * rexp (B * ‖M g‖) * ‖M‖ := mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)
      _ = A * ‖M‖ * rexp (B * ‖M g‖) := by ring
      _ ≤ A * max 1 ‖M‖ * rexp (|B| * ‖M‖ * ‖g‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right _ _) hA) (hexp g) (exp_pos _).le hA'
  rw [hmap, integral_map (by fun_prop) ?_, integral_map (by fun_prop) ?_]
  · simp_rw [hsymm a]
    have h := integral_inner_mul_stdGaussian_of_le_exp hFM hFMb hLM (M a)
    simp_rw [Function.comp_apply, hdM, ContinuousLinearMap.comp_apply, hMM] at h
    exact h
  · exact ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).mul hF.continuous).aestronglyMeasurable

end multivariate

end ProbabilityTheory
