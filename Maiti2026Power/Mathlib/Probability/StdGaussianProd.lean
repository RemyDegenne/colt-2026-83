/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Maiti2026Power.Mathlib.Probability.GaussianMGF

/-!
# Products of standard Gaussian measures and independence of uncorrelated linear images

* `map_toLp_prod_stdGaussian`: a pair of independent standard Gaussian vectors of `E` and `F` is a
  standard Gaussian vector of the product space `WithLp 2 (E × F)`.
* `isGaussian_prod_stdGaussian`: the product of two standard Gaussian measures is a Gaussian
  measure on the product space.
* `covariance_inner_add_prod_stdGaussian`: the covariance of the linear forms
  `⟪a, A₁ p.1 + A₂ p.2⟫` and `⟪b, B₁ p.1 + B₂ p.2⟫` under the product of two standard Gaussian
  measures is `⟪a, (A₁ ∘L B₁† + A₂ ∘L B₂†) b⟫`.
* `indepFun_add_prod_stdGaussian_of_comp_adjoint_eq_zero`: if `A₁ ∘L B₁† + A₂ ∘L B₂† = 0`, then
  the linear images `A₁ p.1 + A₂ p.2` and `B₁ p.1 + B₂ p.2` of a pair of independent standard
  Gaussian vectors are independent.

## TODO

`covariance_comp_fst_prod` and `covariance_comp_snd_prod` (the covariance of two functions of one
coordinate under a product measure) are general facts about `ProbabilityTheory.covariance` which
belong next to `covariance_fst_snd_prod` in Mathlib rather than in this Gaussian file.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace InnerProduct

namespace ProbabilityTheory

section Prod

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **A pair of independent standard Gaussian vectors is a standard Gaussian vector on the product
space**: the product of the standard Gaussian measures of `E` and `F` is the standard Gaussian
measure of `E × F` with the inner product `⟪(a, b), (x, y)⟫ = ⟪a, x⟫ + ⟪b, y⟫`, that is of
`WithLp 2 (E × F)`. -/
lemma map_toLp_prod_stdGaussian :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2)
      = stdGaussian (WithLp 2 (E × F)) := by
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  norm_cast
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd]
  linarith [WithLp.prod_norm_sq_eq_of_L2 t]

/-- The product of two standard Gaussian measures is a Gaussian measure on the product space. -/
instance isGaussian_prod_stdGaussian : IsGaussian ((stdGaussian E).prod (stdGaussian F)) := by
  have h : (stdGaussian E).prod (stdGaussian F)
      = (stdGaussian (WithLp 2 (E × F))).map (WithLp.prodContinuousLinearEquiv 2 ℝ E F) := by
    rw [← map_toLp_prod_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  rw [h]
  infer_instance

end Prod

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Linear forms are square integrable under the standard Gaussian measure. -/
lemma memLp_two_inner_stdGaussian (a : E) : MemLp (fun g ↦ ⟪a, g⟫) 2 (stdGaussian E) :=
  IsGaussian.memLp_two_id.const_inner a

/-- The covariance of two linear forms under the standard Gaussian measure. -/
lemma covariance_inner_stdGaussian (a b : E) :
    cov[fun g ↦ ⟪a, g⟫, fun g ↦ ⟪b, g⟫; stdGaussian E] = ⟪a, b⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'}

/-- The covariance of two functions of the first coordinate under a product measure is their
covariance under the first marginal. -/
lemma covariance_comp_fst_prod [IsProbabilityMeasure ν] {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    cov[fun p ↦ X p.1, fun p ↦ Y p.1; μ.prod ν] = cov[X, Y; μ] := by
  have h : (μ.prod ν).map Prod.fst = μ := by simp
  rw [← covariance_map_fun (Z := Prod.fst) (μ := μ.prod ν) (by rwa [h]) (by rwa [h])
    measurable_fst.aemeasurable, h]

/-- The covariance of two functions of the second coordinate under a product measure is their
covariance under the second marginal. -/
lemma covariance_comp_snd_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X Y : Ω' → ℝ}
    (hX : AEStronglyMeasurable X ν) (hY : AEStronglyMeasurable Y ν) :
    cov[fun p ↦ X p.2, fun p ↦ Y p.2; μ.prod ν] = cov[X, Y; ν] := by
  have h : (μ.prod ν).map Prod.snd = ν := by simp
  rw [← covariance_map_fun (Z := Prod.snd) (μ := μ.prod ν) (by rwa [h]) (by rwa [h])
    measurable_snd.aemeasurable, h]

end Covariance

section Prod

variable {E₁ E₂ F G : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {A₁ : E₁ →L[ℝ] F} {A₂ : E₂ →L[ℝ] F} {B₁ : E₁ →L[ℝ] G} {B₂ : E₂ →L[ℝ] G}

omit [BorelSpace E₂] in
/-- Linear forms of the first coordinate are square integrable under a product of standard
Gaussian measures. -/
lemma memLp_two_inner_fst_prod_stdGaussian (a : E₁) :
    MemLp (fun p : E₁ × E₂ ↦ ⟪a, p.1⟫) 2 ((stdGaussian E₁).prod (stdGaussian E₂)) :=
  (memLp_two_inner_stdGaussian a).comp_fst _

omit [BorelSpace E₁] in
/-- Linear forms of the second coordinate are square integrable under a product of standard
Gaussian measures. -/
lemma memLp_two_inner_snd_prod_stdGaussian (a : E₂) :
    MemLp (fun p : E₁ × E₂ ↦ ⟪a, p.2⟫) 2 ((stdGaussian E₁).prod (stdGaussian E₂)) :=
  (memLp_two_inner_stdGaussian a).comp_snd _

/-- The covariance of two linear forms of a pair of independent standard Gaussian vectors. -/
lemma covariance_inner_add_prod_stdGaussian (a : F) (b : G) :
    cov[fun p ↦ ⟪a, A₁ p.1 + A₂ p.2⟫, fun p ↦ ⟪b, B₁ p.1 + B₂ p.2⟫;
        (stdGaussian E₁).prod (stdGaussian E₂)] =
      ⟪a, (A₁ ∘L B₁†) b⟫ + ⟪a, (A₂ ∘L B₂†) b⟫ := by
  have h₁ : (fun p : E₁ × E₂ ↦ ⟪a, A₁ p.1 + A₂ p.2⟫) =
      (fun p ↦ ⟪(A₁†) a, p.1⟫) + fun p ↦ ⟪(A₂†) a, p.2⟫ := by
    ext p
    simp [inner_add_right, ContinuousLinearMap.adjoint_inner_left]
  have h₂ : (fun p : E₁ × E₂ ↦ ⟪b, B₁ p.1 + B₂ p.2⟫) =
      (fun p ↦ ⟪(B₁†) b, p.1⟫) + fun p ↦ ⟪(B₂†) b, p.2⟫ := by
    ext p
    simp [inner_add_right, ContinuousLinearMap.adjoint_inner_left]
  rw [h₁, h₂,
    covariance_add_left (memLp_two_inner_fst_prod_stdGaussian _)
      (memLp_two_inner_snd_prod_stdGaussian _)
      ((memLp_two_inner_fst_prod_stdGaussian _).add (memLp_two_inner_snd_prod_stdGaussian _)),
    covariance_add_right (memLp_two_inner_fst_prod_stdGaussian _)
      (memLp_two_inner_fst_prod_stdGaussian _) (memLp_two_inner_snd_prod_stdGaussian _),
    covariance_add_right (memLp_two_inner_snd_prod_stdGaussian _)
      (memLp_two_inner_fst_prod_stdGaussian _) (memLp_two_inner_snd_prod_stdGaussian _),
    covariance_fst_snd_prod (memLp_two_inner_stdGaussian _) (memLp_two_inner_stdGaussian _),
    covariance_comm (fun p : E₁ × E₂ ↦ ⟪(A₂†) a, p.2⟫),
    covariance_fst_snd_prod (memLp_two_inner_stdGaussian _) (memLp_two_inner_stdGaussian _),
    covariance_comp_fst_prod (by fun_prop) (by fun_prop),
    covariance_comp_snd_prod (by fun_prop) (by fun_prop),
    covariance_inner_stdGaussian, covariance_inner_stdGaussian]
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- The linear images `A₁ p.1 + A₂ p.2` and `B₁ p.1 + B₂ p.2` of a pair of independent standard
Gaussian vectors are independent as soon as they are uncorrelated, that is
`A₁ ∘L B₁† + A₂ ∘L B₂† = 0`. -/
lemma indepFun_add_prod_stdGaussian_of_comp_adjoint_eq_zero
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace G] [BorelSpace G]
    (h : A₁ ∘L B₁† + A₂ ∘L B₂† = 0) :
    IndepFun (fun p ↦ A₁ p.1 + A₂ p.2) (fun p ↦ B₁ p.1 + B₂ p.2)
      ((stdGaussian E₁).prod (stdGaussian E₂)) := by
  refine HasGaussianLaw.indepFun_of_covariance_inner ?_ fun a b ↦ ?_
  · exact HasGaussianLaw.map_fun (IsGaussian.hasGaussianLaw_id
      (μ := (stdGaussian E₁).prod (stdGaussian E₂)))
      ((A₁ ∘L ContinuousLinearMap.fst ℝ _ _ + A₂ ∘L ContinuousLinearMap.snd ℝ _ _).prod
        (B₁ ∘L ContinuousLinearMap.fst ℝ _ _ + B₂ ∘L ContinuousLinearMap.snd ℝ _ _))
  · rw [covariance_inner_add_prod_stdGaussian, ← inner_add_right, ← add_apply, h]
    simp

/-- The linear image `A₁ p.1 + A₂ p.2` of a pair of independent standard Gaussian vectors is
centered. -/
lemma integral_add_prod_stdGaussian :
    ∫ p, (A₁ p.1 + A₂ p.2) ∂((stdGaussian E₁).prod (stdGaussian E₂)) = 0 := by
  have h₁ : Integrable (fun p : E₁ × E₂ ↦ p.1) ((stdGaussian E₁).prod (stdGaussian E₂)) :=
    IsGaussian.integrable_id.comp_fst _
  have h₂ : Integrable (fun p : E₁ × E₂ ↦ p.2) ((stdGaussian E₁).prod (stdGaussian E₂)) :=
    IsGaussian.integrable_id.comp_snd _
  rw [integral_add (A₁.integrable_comp h₁) (A₂.integrable_comp h₂),
    A₁.integral_comp_comm h₁, A₂.integral_comp_comm h₂, integral_prod _ h₁, integral_prod _ h₂]
  simp [integral_id_stdGaussian]

end Prod

end ProbabilityTheory
