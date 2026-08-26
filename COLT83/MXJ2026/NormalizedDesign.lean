/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.OptimalDesign

/-!
# The normalized `G`-optimal design and a well-separated pair of arms

For a `G`-optimal design `w` on `𝒳` with design matrix `A` (`IsGOptimalDesign`), the normalizing
matrix `M = normalizeMat A = d^{-1/2} √(A⁻¹)` is symmetric (`transpose_normalizeMat`), so that
`⟪x, M u⟫ = ⟪M x, u⟫` (`inner_toEuclideanCLM_normalizeMat`), it maps the support of `w` to unit
vectors `v_x = M x` with `∑ₓ w x • v_x v_xᵀ = I / d`, hence for every support point `x₁`
`∑ₓ w x ⟪v_{x₁}, v_x⟫ ^ 2 = 1 / d` (`IsGOptimalDesign.sum_mul_inner_normalizeMat_sq`). It follows
that some support point `k` has `⟪v_{x₁}, v_k⟫ ≤ 1 / √d ≤ 1 / √2` when `d ≥ 2`, and then
`‖v_{x₁} - v_k‖ ^ 2 = 2 - 2 ⟪v_{x₁}, v_k⟫ ≥ 2 - √2` (`IsGOptimalDesign.exists_separated_pair`).
This is the geometric input of the two-point lower bound of the adaptive lower bound chapter.
-/

@[expose] public section

open Real Finset
open scoped RealInnerProductSpace Matrix

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)}
  {w : EuclideanSpace ℝ ι →₀ ℝ}

/-- The normalizing matrix is symmetric. -/
lemma transpose_normalizeMat (A : Matrix ι ι ℝ) : (normalizeMat A)ᵀ = normalizeMat A := by
  rw [normalizeMat, Matrix.transpose_smul, Matrix.transpose_sqrt]

/-- `⟪x, M u⟫ = ⟪M x, u⟫` for the (symmetric) normalizing matrix `M`. -/
lemma inner_toEuclideanCLM_normalizeMat (A : Matrix ι ι ℝ) (x u : EuclideanSpace ℝ ι) :
    ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat A) u⟫ =
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat A) x, u⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, Matrix.adjoint_toEuclideanCLM,
    transpose_normalizeMat]

omit [Fintype ι] [DecidableEq ι] in
/-- The design matrix of the image of `w` by `f` is `∑ₓ w x • (f x) (f x)ᵀ`. -/
lemma designMatrix_mapDomain (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (w : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix (Finsupp.mapDomain f w) = ∑ x ∈ w.support, w x • outerSelf (f x) := by
  rw [designMatrix, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
  rfl

variable [Nonempty ι] (hw : IsGOptimalDesign 𝒳 w)
include hw

/-- For a `G`-optimal design `w` with normalized arms `v_x = M x`,
`∑ₓ w x ⟪v_{x₁}, v_x⟫ ^ 2 = ‖v_{x₁}‖ ^ 2 / d`. -/
lemma IsGOptimalDesign.sum_mul_inner_normalizeMat_sq (x₁ : EuclideanSpace ℝ ι) :
    ∑ x ∈ w.support, w x * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x⟫ ^ 2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁‖ ^ 2 /
        Fintype.card ι := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w))
  have h1 : ∑ x ∈ w.support, w x * ⟪L x₁, L x⟫ ^ 2 =
      WithLp.ofLp (L x₁) ⬝ᵥ designMatrix (Finsupp.mapDomain L w) *ᵥ WithLp.ofLp (L x₁) := by
    rw [designMatrix_mapDomain, Matrix.sum_mulVec, dotProduct_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_outerSelf_mulVec]
  rw [h1, hw.designMatrix_mapDomain_normalizeMat, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, div_eq_inv_mul]

/-- For a `G`-optimal design and a support point `x₁`, some support point `k` has
`⟪v_{x₁}, v_k⟫ ≤ 1 / √d`. -/
lemma IsGOptimalDesign.exists_inner_normalizeMat_le {x₁ : EuclideanSpace ℝ ι}
    (hx₁ : x₁ ∈ w.support) :
    ∃ k ∈ w.support, ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) k⟫ ≤
        1 / √(Fintype.card ι) := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w))
  have hsum := hw.sum_mul_inner_normalizeMat_sq x₁
  rw [hw.norm_normalizeMat_eq_one hx₁, one_pow] at hsum
  have hle : ∑ x ∈ w.support, w x * ⟪L x₁, L x⟫ ^ 2 ≤
      ∑ x ∈ w.support, w x * (1 / Fintype.card ι) := by
    rw [hsum, ← Finset.sum_mul, hw.isDesign.sum_eq_one, one_mul]
  obtain ⟨k, hk, hk'⟩ := Finset.exists_le_of_sum_le hw.isDesign.support_nonempty hle
  refine ⟨k, hk, ?_⟩
  have h1 : ⟪L x₁, L k⟫ ^ 2 ≤ 1 / Fintype.card ι :=
    le_of_mul_le_mul_left hk' (hw.isDesign.pos_of_mem_support hk)
  calc ⟪L x₁, L k⟫ ≤ |⟪L x₁, L k⟫| := le_abs_self _
    _ = √(⟪L x₁, L k⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(1 / Fintype.card ι) := Real.sqrt_le_sqrt h1
    _ = 1 / √(Fintype.card ι) := by rw [one_div, Real.sqrt_inv, one_div]

/-- `‖v_{x₁} - v_k‖ ^ 2 = 2 - 2 ⟪v_{x₁}, v_k⟫` for two support points of a `G`-optimal design. -/
lemma IsGOptimalDesign.norm_sub_sq_normalizeMat {x₁ k : EuclideanSpace ℝ ι}
    (hx₁ : x₁ ∈ w.support) (hk : k ∈ w.support) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁ -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) k‖ ^ 2 =
      2 - 2 * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) k⟫ := by
  rw [norm_sub_sq_real, hw.norm_normalizeMat_eq_one hx₁, hw.norm_normalizeMat_eq_one hk]
  ring

/-- **A well-separated pair of unit arms**: in dimension `d ≥ 2`, for every support point `x₁` of
a `G`-optimal design there is a support point `k` with `⟪v_{x₁}, v_k⟫ ≤ 1 / √2` and
`‖v_{x₁} - v_k‖ ^ 2 ≥ 2 - √2`. -/
lemma IsGOptimalDesign.exists_separated_pair (hd : 2 ≤ Fintype.card ι)
    {x₁ : EuclideanSpace ℝ ι} (hx₁ : x₁ ∈ w.support) :
    ∃ k ∈ w.support,
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) k⟫ ≤ 1 / √2 ∧
      2 - √2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x₁ -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) k‖ ^ 2 := by
  obtain ⟨k, hk, hle⟩ := hw.exists_inner_normalizeMat_le hx₁
  have h2 : (1 : ℝ) / √(Fintype.card ι) ≤ 1 / √2 := by
    gcongr
    exact_mod_cast hd
  have hle' := hle.trans h2
  refine ⟨k, hk, hle', ?_⟩
  rw [hw.norm_sub_sq_normalizeMat hx₁ hk]
  have h4 : (2 : ℝ) / √2 = √2 := by
    rw [div_eq_iff (by positivity), Real.mul_self_sqrt (by norm_num)]
  have h5 := mul_le_mul_of_nonneg_left hle' (by norm_num : (0 : ℝ) ≤ 2)
  rw [mul_one_div, h4] at h5
  linarith

end COLT83
