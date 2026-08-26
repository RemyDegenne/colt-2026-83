/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.CovarianceBilin
public import COLT83.Mathlib.Probability.GaussianMGF

/-!
# Products of standard Gaussian measures and independence of uncorrelated linear images

* `stdGaussian_map_blocks`: splitting the coordinates of a standard Gaussian vector on
  `EuclideanSpace ℝ (ι ⊕ κ)` into the `ι`-block and the `κ`-block gives a pair of independent
  standard Gaussian vectors, that is the product measure
  `(stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ))`.
* `isGaussian_prod_stdGaussian`: this product measure is a Gaussian measure on the product space.
* `covariance_inner_add_prod_stdGaussian`: the covariance of the linear forms
  `⟪a, A₁ p.1 + A₂ p.2⟫` and `⟪b, B₁ p.1 + B₂ p.2⟫` under the product of two standard Gaussian
  measures is `⟪a, (A₁ ∘L B₁† + A₂ ∘L B₂†) b⟫`.
* `indepFun_add_prod_stdGaussian_of_comp_adjoint_eq_zero`: if `A₁ ∘L B₁† + A₂ ∘L B₂† = 0`, then
  the linear images `A₁ p.1 + A₂ p.2` and `B₁ p.1 + B₂ p.2` of a pair of independent standard
  Gaussian vectors are independent.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace ProbabilityTheory

section Blocks

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Splitting a standard Gaussian vector on `EuclideanSpace ℝ (ι ⊕ κ)` into its `ι`-block and its
`κ`-block gives a pair of independent standard Gaussian vectors. -/
lemma stdGaussian_map_blocks :
    (stdGaussian (EuclideanSpace ℝ (ι ⊕ κ))).map
        (fun g ↦ (WithLp.toLp 2 fun i ↦ g (Sum.inl i), WithLp.toLp 2 fun j ↦ g (Sum.inr j))) =
      (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ)) := by
  rw [← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    ← (measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ ↦ gaussianReal 0 1)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The product of two standard Gaussian measures on Euclidean spaces is a Gaussian measure on
the product space. -/
instance isGaussian_prod_stdGaussian :
    IsGaussian ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ))) := by
  rw [← stdGaussian_map_blocks]
  -- the block map is a continuous linear map
  have : (fun g : EuclideanSpace ℝ (ι ⊕ κ) ↦
      ((WithLp.toLp 2 fun i ↦ g (Sum.inl i) : EuclideanSpace ℝ ι),
        (WithLp.toLp 2 fun j ↦ g (Sum.inr j) : EuclideanSpace ℝ κ))) =
      ((PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap ∘L
          ContinuousLinearMap.pi fun i ↦ PiLp.proj 2 _ (Sum.inl i)).prod
        ((PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap ∘L
          ContinuousLinearMap.pi fun j ↦ PiLp.proj 2 _ (Sum.inr j)) := by
    ext g <;> rfl
  rw [this]
  infer_instance

end Blocks

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

/-- Linear forms of the first coordinate are square integrable under a product of standard
Gaussian measures. -/
lemma memLp_two_inner_fst_prod_stdGaussian (a : E₁) :
    MemLp (fun p : E₁ × E₂ ↦ ⟪a, p.1⟫) 2 ((stdGaussian E₁).prod (stdGaussian E₂)) :=
  (memLp_two_inner_stdGaussian a).comp_fst _

/-- Linear forms of the second coordinate are square integrable under a product of standard
Gaussian measures. -/
lemma memLp_two_inner_snd_prod_stdGaussian (a : E₂) :
    MemLp (fun p : E₁ × E₂ ↦ ⟪a, p.2⟫) 2 ((stdGaussian E₁).prod (stdGaussian E₂)) :=
  (memLp_two_inner_stdGaussian a).comp_snd _

/-- The covariance of two linear forms of a pair of independent standard Gaussian vectors. -/
lemma covariance_inner_add_prod_stdGaussian (a : F) (b : G) :
    cov[fun p ↦ ⟪a, A₁ p.1 + A₂ p.2⟫, fun p ↦ ⟪b, B₁ p.1 + B₂ p.2⟫;
        (stdGaussian E₁).prod (stdGaussian E₂)] =
      ⟪a, (A₁ ∘L ContinuousLinearMap.adjoint B₁) b⟫
        + ⟪a, (A₂ ∘L ContinuousLinearMap.adjoint B₂) b⟫ := by
  have h₁ : (fun p : E₁ × E₂ ↦ ⟪a, A₁ p.1 + A₂ p.2⟫) =
      (fun p ↦ ⟪ContinuousLinearMap.adjoint A₁ a, p.1⟫)
        + fun p ↦ ⟪ContinuousLinearMap.adjoint A₂ a, p.2⟫ := by
    ext p
    simp [inner_add_right, ContinuousLinearMap.adjoint_inner_left]
  have h₂ : (fun p : E₁ × E₂ ↦ ⟪b, B₁ p.1 + B₂ p.2⟫) =
      (fun p ↦ ⟪ContinuousLinearMap.adjoint B₁ b, p.1⟫)
        + fun p ↦ ⟪ContinuousLinearMap.adjoint B₂ b, p.2⟫ := by
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
    covariance_comm (fun p : E₁ × E₂ ↦ ⟪ContinuousLinearMap.adjoint A₂ a, p.2⟫),
    covariance_fst_snd_prod (memLp_two_inner_stdGaussian _) (memLp_two_inner_stdGaussian _),
    covariance_comp_fst_prod (by fun_prop) (by fun_prop),
    covariance_comp_snd_prod (by fun_prop) (by fun_prop),
    covariance_inner_stdGaussian, covariance_inner_stdGaussian]
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- The linear images `A₁ p.1 + A₂ p.2` and `B₁ p.1 + B₂ p.2` of a pair of independent standard
Gaussian vectors are independent as soon as they are uncorrelated, that is
`A₁ ∘L B₁† + A₂ ∘L B₂† = 0`. -/
lemma indepFun_add_prod_stdGaussian_of_comp_adjoint_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A₁ : EuclideanSpace ℝ ι →L[ℝ] F} {A₂ : EuclideanSpace ℝ κ →L[ℝ] F}
    {B₁ : EuclideanSpace ℝ ι →L[ℝ] G} {B₂ : EuclideanSpace ℝ κ →L[ℝ] G}
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace G] [BorelSpace G]
    (h : A₁ ∘L ContinuousLinearMap.adjoint B₁ + A₂ ∘L ContinuousLinearMap.adjoint B₂ = 0) :
    IndepFun (fun p ↦ A₁ p.1 + A₂ p.2) (fun p ↦ B₁ p.1 + B₂ p.2)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ))) := by
  refine HasGaussianLaw.indepFun_of_covariance_inner ?_ fun a b ↦ ?_
  · exact HasGaussianLaw.map_fun (IsGaussian.hasGaussianLaw_id
      (μ := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ κ))))
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
