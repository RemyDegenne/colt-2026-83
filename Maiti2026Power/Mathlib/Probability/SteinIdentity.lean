/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.GaussianMGF
public import Maiti2026Power.Mathlib.Probability.SteinReal
public import Maiti2026Power.Mathlib.Probability.MultivariateGaussian
public import Maiti2026Power.Mathlib.Matrix.Loewner

/-!
# Stein's identity for the standard Gaussian measure

For the standard Gaussian measure on a finite-dimensional inner product space `E` and a `C¹`
function `F : E → ℝ` with bounded derivative,
`∫ ⟪a, x⟫ F x ∂(stdGaussian E) = ∫ DF(x) a ∂(stdGaussian E)`
(`integral_inner_mul_stdGaussian`, Gaussian integration by parts). It is deduced from the
one-dimensional identity (`integral_mul_gaussianReal_zero_one_of_hasDerivAt`) by Fubini on the
coordinates (`integral_apply_mul_stdGaussian`).

`integral_fderiv_apply_stdGaussian` is the form used by the Gaussian interpolation method: for
`C²` functions with bounded second derivative and linear maps `L L' : E' → E`,
`∫ DF(L g) (L' g) = ∫ ∑ k, D²F(L g) (L (b k)) (L' (b k))` for an orthonormal basis `b` of `E'`.
For a centered Gaussian vector with covariance `S`, `integral_inner_mul_multivariateGaussian`
gives `E[⟪a, X⟫ F(X)] = E[DF(X) (S a)]`.
-/

@[expose] public section

open MeasureTheory Real InnerProductSpace
open scoped RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

section integrability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
  {F : E → ℝ} {L : ℝ}

/-- `⟪a, x⟫ F x` is integrable under a Gaussian measure when `F` is `C¹` with bounded
derivative. -/
lemma IsGaussian.integrable_inner_mul_of_norm_fderiv_le (hF : ContDiff ℝ 1 F)
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (a : E) :
    Integrable (fun x ↦ ⟪a, x⟫ * F x) μ := by
  refine IsGaussian.integrable_of_abs_le_add_mul_norm_sq (A := 0) (B := ‖a‖ * |F 0|)
    (C := ‖a‖ * L) ((continuous_const.inner continuous_id).mul hF.continuous).aestronglyMeasurable
    fun x ↦ ?_
  rw [abs_mul]
  calc |⟪a, x⟫| * |F x| ≤ (‖a‖ * ‖x‖) * (|F 0| + L * ‖x‖) :=
        mul_le_mul (abs_real_inner_le_norm _ _)
          (abs_le_of_norm_fderiv_le (hF.differentiable one_ne_zero) hL x) (abs_nonneg _)
          (by positivity)
    _ = 0 + ‖a‖ * |F 0| * ‖x‖ + ‖a‖ * L * ‖x‖ ^ 2 := by ring

end integrability

section integrabilityNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
  {F : E → ℝ} {L : ℝ}

/-- `DF(x) a` is integrable under a Gaussian measure when `F` is `C¹` with bounded
derivative. -/
lemma IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le (hF : ContDiff ℝ 1 F)
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (a : E) :
    Integrable (fun x ↦ fderiv ℝ F x a) μ :=
  IsGaussian.integrable_of_abs_le_add_mul_norm (A := L * ‖a‖) (B := 0)
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable fun x ↦ by
      rw [← Real.norm_eq_abs, zero_mul, add_zero]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _))

end integrabilityNormed

section basis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {F : E → ℝ} {L : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The curve `t ↦ ∑ j, (insertNth i t y) j • b j` obtained by moving along the `i`-th vector of an
orthonormal basis has derivative `b i`. -/
lemma hasDerivAt_sum_smul_insertNth (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (i : Fin (n + 1))
    (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∑ j, (Fin.insertNth i s y : Fin (n + 1) → ℝ) j • b j) (b i) t := by
  have hsplit : ∀ s : ℝ, ∑ j, (Fin.insertNth i s y : Fin (n + 1) → ℝ) j • b j
      = s • b i + ∑ j : Fin n, y j • b (i.succAbove j) := by
    intro s
    rw [Fin.sum_univ_succAbove (fun j ↦ (Fin.insertNth i s y : Fin (n + 1) → ℝ) j • b j) i]
    simp
  simp_rw [hsplit]
  simpa using ((hasDerivAt_id t).smul_const (b i)).add_const
    (∑ j : Fin n, y j • b (i.succAbove j))

/-- Fubini for the standard Gaussian measure along an orthonormal basis: integrate first along the
`i`-th basis vector. -/
lemma integral_stdGaussian_eq_integral_insertNth (b : OrthonormalBasis (Fin (n + 1)) ℝ E)
    {G : E → ℝ} (hG : Integrable G (stdGaussian E)) (i : Fin (n + 1)) :
    ∫ x, G x ∂stdGaussian E =
      ∫ y, ∫ t, G (∑ j, (Fin.insertNth i t y : Fin (n + 1) → ℝ) j • b j) ∂gaussianReal 0 1
        ∂(Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  have hmeasb : Measurable fun x : Fin (n + 1) → ℝ ↦ ∑ j, x j • b j :=
    (continuous_finsetSum _ fun j _ ↦ (continuous_apply j).smul continuous_const).measurable
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) i).symm
  rw [stdGaussian_eq_map_pi_orthonormalBasis b] at hG ⊢
  rw [integral_map hmeasb.aemeasurable hG.1, ← hmp.integral_comp']
  have hint : Integrable
      (fun z ↦ G (∑ j, ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm z) j
        • b j))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1)) := by
    rw [show (fun z ↦ G (∑ j,
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm z) j • b j))
        = (G ∘ fun x : Fin (n + 1) → ℝ ↦ ∑ j, x j • b j) ∘
          (MeasurableEquiv.piFinSuccAbove _ i).symm from rfl,
      hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    exact (integrable_map_measure hG.1 hmeasb.aemeasurable).1 hG
  rw [integral_prod_symm _ hint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]

/-- **Stein's identity** along a vector of an orthonormal basis:
`E[⟪b i, g⟫ F(g)] = E[DF(g) (b i)]` for `C¹` functions with bounded derivative. -/
lemma integral_inner_mul_stdGaussian_basis (b : OrthonormalBasis (Fin (n + 1)) ℝ E)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (i : Fin (n + 1)) :
    ∫ x, ⟪b i, x⟫ * F x ∂stdGaussian E = ∫ x, fderiv ℝ F x (b i) ∂stdGaussian E := by
  have hint1 : Integrable (fun x ↦ ⟪b i, x⟫ * F x) (stdGaussian E) :=
    IsGaussian.integrable_inner_mul_of_norm_fderiv_le hF hL (b i)
  have hint2 : Integrable (fun x ↦ fderiv ℝ F x (b i)) (stdGaussian E) :=
    IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le hF hL _
  rw [integral_stdGaussian_eq_integral_insertNth b hint1 i,
    integral_stdGaussian_eq_integral_insertNth b hint2 i]
  congr 1
  ext y
  simp only [b.inner_sum_smul, Fin.insertNth_apply_same]
  refine integral_mul_gaussianReal_zero_one_of_hasDerivAt (L := L)
    (f' := fun t ↦ fderiv ℝ F (∑ j, (Fin.insertNth i t y : Fin (n + 1) → ℝ) j • b j) (b i))
    (fun t ↦ ((hF.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_sum_smul_insertNth b i y t)) fun t ↦ ?_
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ F (∑ j, (Fin.insertNth i t y : Fin (n + 1) → ℝ) j • b j) (b i)‖
      ≤ ‖fderiv ℝ F (∑ j, (Fin.insertNth i t y : Fin (n + 1) → ℝ) j • b j)‖ * ‖b i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ L := by rw [b.norm_eq_one, mul_one]; exact hL _

end basis

section general

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : E → ℝ} {L : ℝ}

/-- **Stein's identity** (Gaussian integration by parts): for the standard Gaussian measure on a
finite-dimensional inner product space `E` and a `C¹` function `F` with bounded derivative,
`E[⟪a, g⟫ F(g)] = E[DF(g) a]`. -/
lemma integral_inner_mul_stdGaussian (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (a : E) :
    ∫ x, ⟪a, x⟫ * F x ∂stdGaussian E = ∫ x, fderiv ℝ F x a ∂stdGaussian E := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ E = n := ⟨_, rfl⟩
  rcases n with _ | n
  · have ha : a = 0 := finrank_zero_iff_forall_zero.1 hn a
    simp [ha]
  -- expand `a` in an orthonormal basis and apply Stein's identity along each basis vector
  let b : OrthonormalBasis (Fin (n + 1)) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hn)
  have ha : a = ∑ j, ⟪b j, a⟫ • b j := (b.sum_repr' a).symm
  have h1 : ∀ x : E, ⟪a, x⟫ * F x = ∑ j, ⟪b j, a⟫ * (⟪b j, x⟫ * F x) := by
    intro x
    conv_lhs => rw [ha]
    simp [sum_inner, real_inner_smul_left, Finset.sum_mul, mul_assoc]
  have h2 : ∀ x : E, fderiv ℝ F x a = ∑ j, ⟪b j, a⟫ * fderiv ℝ F x (b j) := by
    intro x
    conv_lhs => rw [ha]
    simp [map_sum, map_smul]
  simp_rw [h1, h2]
  rw [integral_finsetSum _ fun j _ ↦ ?_, integral_finsetSum _ fun j _ ↦ ?_]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, integral_const_mul, integral_inner_mul_stdGaussian_basis b hF hL j]
  · exact (IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le hF hL _).const_mul _
  · exact (IsGaussian.integrable_inner_mul_of_norm_fderiv_le hF hL (b j)).const_mul _

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {κ : Type*} [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Stein's identity for linear images**: if `F : E → ℝ` is `C²` with bounded second
derivative and `L L' : E' → E` are linear, then for `g ~ N(0, I)` on `E'` and an orthonormal
basis `b` of `E'`, `E[DF(L g) (L' g)] = E[∑ k, D²F(L g) (L (b k)) (L' (b k))]`. -/
lemma integral_fderiv_apply_stdGaussian (hF : ContDiff ℝ 2 F) {K : ℝ}
    (hK : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ K) (L L' : E' →L[ℝ] E) (b : OrthonormalBasis κ ℝ E') :
    ∫ g, fderiv ℝ F (L g) (L' g) ∂stdGaussian E' =
      ∫ g, ∑ k, fderiv ℝ (fderiv ℝ F) (L g) (L (b k)) (L' (b k)) ∂stdGaussian E' := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)) (hK 0)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) le_rfl
  have hφd : ∀ (k : κ) (g : E'), HasFDerivAt (fun g ↦ fderiv ℝ F (L g) (L' (b k)))
      (((fderiv ℝ (fderiv ℝ F) (L g)).comp L).flip (L' (b k))) g := fun k g ↦ by
    have h1 : HasFDerivAt (fun g ↦ fderiv ℝ F (L g)) ((fderiv ℝ (fderiv ℝ F) (L g)).comp L) g :=
      ((hF1.differentiable one_ne_zero) (L g)).hasFDerivAt.comp g L.hasFDerivAt
    exact (h1.clm_apply (hasFDerivAt_const (L' (b k)) g)).congr_fderiv (by simp)
  have hφc : ∀ k : κ, ContDiff ℝ 1 (fun g ↦ fderiv ℝ F (L g) (L' (b k))) := fun k ↦
    (hF1.comp L.contDiff).clm_apply contDiff_const
  have hφL : ∀ (k : κ) (g : E'), ‖fderiv ℝ (fun g ↦ fderiv ℝ F (L g) (L' (b k))) g‖ ≤
      K * ‖L‖ * ‖L' (b k)‖ := fun k g ↦ by
    rw [(hφd k g).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
    calc ‖fderiv ℝ (fderiv ℝ F) (L g) (L w) (L' (b k))‖
        ≤ ‖fderiv ℝ (fderiv ℝ F) (L g) (L w)‖ * ‖L' (b k)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ F) (L g)‖ * ‖L w‖ * ‖L' (b k)‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * (‖L‖ * ‖w‖) * ‖L' (b k)‖ := by
          gcongr
          · exact hK _
          · exact L.le_opNorm w
      _ = K * ‖L‖ * ‖L' (b k)‖ * ‖w‖ := by ring
  have hexp : ∀ g, fderiv ℝ F (L g) (L' g) = ∑ k, ⟪b k, g⟫ * fderiv ℝ F (L g) (L' (b k)) := by
    intro g
    have hg : L' g = ∑ k, ⟪b k, g⟫ • L' (b k) := by
      conv_lhs => rw [← b.sum_repr' g]
      simp [map_sum, map_smul]
    rw [hg, map_sum]
    simp [map_smul]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ ↦
    IsGaussian.integrable_inner_mul_of_norm_fderiv_le (hφc k) (hφL k) (b k)]
  rw [integral_finsetSum _ fun k _ ↦ ?_]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_inner_mul_stdGaussian (hφc k) (hφL k) (b k)]
    congr 1
    ext g
    rw [(hφd k g).fderiv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  · have := IsGaussian.integrable_fderiv_apply_of_norm_fderiv_le (μ := stdGaussian E') (hφc k)
      (hφL k) (b k)
    refine this.congr (Filter.Eventually.of_forall fun g ↦ ?_)
    dsimp only
    rw [(hφd k g).fderiv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]

end general

section multivariate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : EuclideanSpace ℝ ι → ℝ} {L : ℝ}

/-- **Stein's identity** for a centered Gaussian vector `X ~ N(0, S)` of `ℝ^ι`:
`E[⟪a, X⟫ F(X)] = E[DF(X) (S a)]`, i.e. `E[X_i F(X)] = ∑ j, S i j E[∂_j F(X)]`. -/
lemma integral_inner_mul_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (a : EuclideanSpace ℝ ι) :
    ∫ x, ⟪a, x⟫ * F x ∂multivariateGaussian 0 S =
      ∫ x, fderiv ℝ F x (Matrix.toEuclideanCLM (𝕜 := ℝ) S a) ∂multivariateGaussian 0 S := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
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
  have hLM : ∀ g, ‖fderiv ℝ (F ∘ M) g‖ ≤ L * ‖M‖ := fun g ↦ by
    rw [hdM]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))
  rw [hmap, integral_map (by fun_prop) ?_, integral_map (by fun_prop) ?_]
  · simp_rw [hsymm a]
    have h := integral_inner_mul_stdGaussian hFM hLM (M a)
    simp_rw [Function.comp_apply, hdM, ContinuousLinearMap.comp_apply, hMM] at h
    exact h
  · exact ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).mul hF.continuous).aestronglyMeasurable

end multivariate

end ProbabilityTheory
