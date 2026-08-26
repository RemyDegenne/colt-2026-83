/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.DesignSet
public import Mathlib.Analysis.Matrix.Order
public import COLT83.Mathlib.Analysis.InnerProductSpace.OrthonormalBasisSubmodule

/-!
# The intrinsic width through a Gaussian vector supported on the span

Let `𝒳 ⊆ ℝ^ι` be an action set (nonempty, bounded) spanning the subspace `V = span ℝ 𝒳` of
dimension `r`, and let `B` be the standard orthonormal basis of `V`. The intrinsic width
`intrinsicGw 𝒳` is the Gaussian width term of the coordinate image `𝒳_r = B.repr '' 𝒳 ⊆ ℝ^r`.

* `spanBasisMatrix 𝒳`: the `ι × Fin r` matrix whose columns are the basis vectors `B k`;
  `𝒳_r` is the image of `𝒳` by the linear map with matrix `(spanBasisMatrix 𝒳)ᵀ`
  (`intrinsicGw_eq_gw_image`).
* `intrinsicGw_le_gaussianWidth`: if `Σ ∈ designSet 𝒳` and `S` is a positive semidefinite
  matrix with range in `V` such that `Σ S` is the identity on `V` (that is, `S` is the
  pseudo-inverse of `Σ`), then `intrinsicGw 𝒳 ≤ E[sup_{x ∈ 𝒳} ⟪x, G⟫]` for `G ~ N(0, S)`.
  This is the tool used to bound the intrinsic width of a set through an explicit design and
  an explicit Gaussian vector living on its span, without computing an orthonormal basis.

Blueprint: `def:width_subspace`, `lem:multitask_width_reduction` (general part).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {R : ℝ}

/-- The matrix whose columns are the vectors of the standard orthonormal basis of `span ℝ 𝒳`. -/
noncomputable def spanBasisMatrix (𝒳 : Set (EuclideanSpace ℝ ι)) :
    Matrix ι (Fin (Module.finrank ℝ (Submodule.span ℝ 𝒳))) ℝ :=
  fun i k ↦ ((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)) k : EuclideanSpace ℝ ι) i

omit [DecidableEq ι] in
lemma transpose_spanBasisMatrix_mulVec_apply (y : EuclideanSpace ℝ ι)
    (k : Fin (Module.finrank ℝ (Submodule.span ℝ 𝒳))) :
    ((spanBasisMatrix 𝒳)ᵀ *ᵥ WithLp.ofLp y) k =
      ⟪((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)) k : EuclideanSpace ℝ ι), y⟫ := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, spanBasisMatrix,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

lemma toEuclideanLin_transpose_spanBasisMatrix_apply (y : EuclideanSpace ℝ ι)
    (k : Fin (Module.finrank ℝ (Submodule.span ℝ 𝒳))) :
    Matrix.toEuclideanLin (spanBasisMatrix 𝒳)ᵀ y k =
      ⟪((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)) k : EuclideanSpace ℝ ι), y⟫ :=
  transpose_spanBasisMatrix_mulVec_apply y k

/-- The intrinsic width of `𝒳` is the Gaussian width term of the image of `𝒳` by the linear map
with matrix `(spanBasisMatrix 𝒳)ᵀ`, `x ↦ (⟪B k, x⟫)_k`. -/
lemma intrinsicGw_eq_gw_image (𝒳 : Set (EuclideanSpace ℝ ι)) :
    intrinsicGw 𝒳 = gw (Matrix.toEuclideanLin (spanBasisMatrix 𝒳)ᵀ '' 𝒳) := by
  unfold intrinsicGw
  refine congrArg gw ?_
  ext z
  constructor
  · rintro ⟨⟨x, hxV⟩, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    ext k
    rw [toEuclideanLin_transpose_spanBasisMatrix_apply, OrthonormalBasis.repr_apply_apply,
      Submodule.coe_inner]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, Submodule.subset_span hx⟩, hx, ?_⟩
    ext k
    rw [toEuclideanLin_transpose_spanBasisMatrix_apply, OrthonormalBasis.repr_apply_apply,
      Submodule.coe_inner]

omit [DecidableEq ι] in
lemma transpose_mul_spanBasisMatrix (𝒳 : Set (EuclideanSpace ℝ ι)) :
    (spanBasisMatrix 𝒳)ᵀ * spanBasisMatrix 𝒳 = 1 := by
  ext k l
  have h := orthonormal_iff_ite.1 (stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)).orthonormal k l
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  rw [Matrix.mul_apply, Matrix.one_apply, ← h]
  simp only [Matrix.transpose_apply, spanBasisMatrix, dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

omit [DecidableEq ι] in
/-- `M Mᵀ v = v` for `v ∈ span ℝ 𝒳`, where `M = spanBasisMatrix 𝒳`. -/
lemma spanBasisMatrix_mulVec_transpose_mulVec {v : EuclideanSpace ℝ ι}
    (hv : v ∈ Submodule.span ℝ 𝒳) :
    spanBasisMatrix 𝒳 *ᵥ ((spanBasisMatrix 𝒳)ᵀ *ᵥ WithLp.ofLp v) = WithLp.ofLp v := by
  ext i
  have h := congrArg (fun z : EuclideanSpace ℝ ι ↦ z.ofLp i)
    ((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)).sum_inner_coe_smul_coe hv)
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [← h]
  change ∑ k, spanBasisMatrix 𝒳 i k * ((spanBasisMatrix 𝒳)ᵀ *ᵥ WithLp.ofLp v) k = _
  simp_rw [transpose_spanBasisMatrix_mulVec_apply]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- **Intrinsic width through a Gaussian vector on the span.** Let `Σ ∈ designSet 𝒳` and let
`S` be a positive semidefinite matrix whose range is contained in `V = span ℝ 𝒳` and such that
`Σ S v = v` for every `v ∈ V` (`S` is the pseudo-inverse of `Σ`). Then
`intrinsicGw 𝒳 ≤ E[sup_{x ∈ 𝒳} ⟪x, G⟫]` where `G ~ N(0, S)`. -/
lemma intrinsicGw_le_gaussianWidth (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    {S D : Matrix ι ι ℝ} (hS : S.PosSemidef) (hD : D ∈ designSet 𝒳)
    (hSV : ∀ y, Matrix.toEuclideanLin S y ∈ Submodule.span ℝ 𝒳)
    (hDS : ∀ v ∈ Submodule.span ℝ 𝒳,
      Matrix.toEuclideanLin D (Matrix.toEuclideanLin S v) = v) :
    intrinsicGw 𝒳 ≤ gaussianWidth 𝒳 (multivariateGaussian 0 S) := by
  set M := spanBasisMatrix 𝒳 with hM
  set L := Matrix.toEuclideanLin Mᵀ with hL
  set Lc := LinearMap.toContinuousLinearMap L with hLc
  have hLc_apply : ∀ y, Lc y = L y := fun y ↦ rfl
  -- the matrix identities
  have h1 : Mᵀ * M = 1 := transpose_mul_spanBasisMatrix 𝒳
  have h3 : M * (Mᵀ * (S * M)) = S * M := by
    ext i k
    have hk := hSV ((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)) k)
    exact congrArg (fun z ↦ z i) (spanBasisMatrix_mulVec_transpose_mulVec hk)
  have h4 : D * (S * M) = M := by
    ext i k
    have hk := hDS _ ((stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)) k).2
    exact congrArg (fun z : EuclideanSpace ℝ ι ↦ z.ofLp i) hk
  have hinv : (Mᵀ * D * M) * (Mᵀ * S * M) = 1 := by
    calc (Mᵀ * D * M) * (Mᵀ * S * M) = Mᵀ * (D * (M * (Mᵀ * (S * M)))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h3, h4, h1]
  -- the design matrix `A = Mᵀ D M` of `𝒳_r`
  have hDpsd : D.PosSemidef := posSemidef_of_mem_designSet hD
  have hApsd : (Mᵀ * D * M).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hDpsd.mul_mul_conjTranspose_same Mᵀ
  have hApd : (Mᵀ * D * M).PosDef :=
    hApsd.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hinv))
  have hAmem : Mᵀ * D * M ∈ designSet (L '' 𝒳) := by
    let f : Matrix ι ι ℝ →ₗ[ℝ] Matrix (Fin (Module.finrank ℝ (Submodule.span ℝ 𝒳)))
        (Fin (Module.finrank ℝ (Submodule.span ℝ 𝒳))) ℝ :=
      { toFun := fun X ↦ Mᵀ * X * M
        map_add' := fun X Y ↦ by rw [Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c X ↦ by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
    have hf : Mᵀ * D * M = f D := rfl
    rw [hf, designSet]
    have himage : f '' (outerSelf '' 𝒳) = outerSelf '' (L '' 𝒳) := by
      rw [Set.image_image, Set.image_image]
      refine Set.image_congr fun x _ ↦ ?_
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, hL, outerSelf_toEuclideanLin,
        Matrix.transpose_transpose]
    rw [← himage, ← f.image_convexHull]
    exact Set.mem_image_of_mem f hD
  -- bounds on `𝒳_r`
  have hne' : (L '' 𝒳).Nonempty := hne.image _
  have hR0 : 0 ≤ R := nonneg_of_norm_le hne hR
  have hR' : ∀ z ∈ L '' 𝒳, ‖z‖ ≤ ‖Lc‖ * R := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hLc_apply]
    exact (Lc.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  -- the support function of `𝒳_r` at `L y` is the support function of `𝒳` at `y`
  have hsupp : ∀ y, supportFn (L '' 𝒳) (L y) = supportFn 𝒳 y := by
    intro y
    rw [supportFn_eq_sSup, supportFn_eq_sSup, Set.image_image]
    congr 1
    refine Set.image_congr fun x hx ↦ ?_
    rw [EuclideanSpace.inner_eq_star_dotProduct (L x) (L y), star_trivial]
    simp only [dotProduct, hL, hM, toEuclideanLin_transpose_spanBasisMatrix_apply]
    rw [← (stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)).sum_inner_coe_mul_inner_coe
      (Submodule.subset_span hx) y]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  -- conclusion
  rw [intrinsicGw_eq_gw_image]
  refine (gw_le_gwMat hne' hR' hAmem hApd).trans (le_of_eq ?_)
  have hmap := multivariateGaussian_zero_map_toEuclideanLin hS Mᵀ
  rw [Matrix.transpose_transpose] at hmap
  rw [gwMat, Matrix.inv_eq_right_inv hinv, ← hmap, gaussianWidth, gaussianWidth,
    integral_map Lc.continuous.aemeasurable (continuous_supportFn hne' hR').aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ hsupp y)

end COLT83
