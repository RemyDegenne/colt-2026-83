/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.GaussianWidth
public import COLT83.Mathlib.Matrix.LoewnerInv
public import COLT83.Mathlib.Probability.MultivariateGaussian
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Design matrices and the Gaussian width term of an action set

For an action set `𝒳 ⊆ EuclideanSpace ℝ ι`:

* `designSet 𝒳 = conv {x xᵀ : x ∈ 𝒳}` is the set of *design matrices* `A(λ) = ∑ λ_x x xᵀ` of
  the finitely supported probability distributions `λ` on `𝒳`.
* `gwMat K A = E[sup_{x ∈ K} ⟪x, A^{-1/2} g⟫]`, `g ~ N(0, I)`, is the Gaussian width of the compact
  set `K` for the positive definite matrix `A`. Since `A^{-1/2} g ~ N(0, A⁻¹)`, it is defined as
  the Gaussian width of `K` for the Gaussian measure with covariance `A⁻¹`.
* `gw 𝒳 = inf {gwMat 𝒳 A : A ∈ designSet 𝒳, A ≻ 0}` is the *Gaussian width term* `w(𝒳)` of the
  action set (Maiti, Xu, Jamieson 2026); it is the relevant quantity when `𝒳` spans the space.
* `intrinsicGw 𝒳` is the Gaussian width term of `𝒳` seen as a subset of its own span `V`, in the
  coordinates of the standard orthonormal basis of `V`; it is the relevant quantity for action
  sets that do not span the space.

## Main results on `gwMat`

For a nonempty compact (or bounded) set `K` and positive definite matrices:
`gwMat_nonneg`, `gwMat_neg_set` and `gwMat_sub_set` (symmetry, `E[max_{x,y ∈ K} ⟪x - y, G⟫]
= 2 gwMat K A`), `gwMat_smul` (homogeneity `gwMat K (c • A) = c^{-1/2} gwMat K A`),
`gwMat_anti` (monotonicity in the Loewner order: `A ≤ B → gwMat K B ≤ gwMat K A`) and
`gwMat_image` (invariance under invertible linear maps `gwMat (M '' K) (M A Mᵀ) = gwMat K A`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped RealInnerProductSpace MatrixOrder Pointwise Matrix

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The design matrix `x xᵀ` of a point `x`. -/
def outerSelf (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x)

/-- The set of design matrices of `𝒳`: the convex hull of `{x xᵀ : x ∈ 𝒳}`, that is the set of
matrices `∑ λ_x x xᵀ` for `λ` a finitely supported probability distribution on `𝒳`. -/
def designSet (𝒳 : Set (EuclideanSpace ℝ ι)) : Set (Matrix ι ι ℝ) :=
  convexHull ℝ (outerSelf '' 𝒳)

/-- Gaussian width of the set `K` for the matrix `A`: `E[sup_{x ∈ K} ⟪x, A^{-1/2} g⟫]` for
`g ~ N(0, I)`, that is the Gaussian width of `K` for the centered Gaussian measure with covariance
`A⁻¹` (meaningful for `A` positive definite). -/
noncomputable def gwMat (K : Set (EuclideanSpace ℝ ι)) (A : Matrix ι ι ℝ) : ℝ :=
  gaussianWidth K (multivariateGaussian 0 A⁻¹)

/-- The Gaussian width term `w(𝒳)` of the action set `𝒳`: the infimum of `gwMat 𝒳 A` over the
positive definite design matrices `A` of `𝒳`. -/
noncomputable def gw (𝒳 : Set (EuclideanSpace ℝ ι)) : ℝ :=
  ⨅ A : {A : Matrix ι ι ℝ // A ∈ designSet 𝒳 ∧ A.PosDef}, gwMat 𝒳 A

/-- The intrinsic Gaussian width term of an action set `𝒳`: the Gaussian width term of `𝒳` seen
inside its span `V`, in the coordinates given by the standard orthonormal basis of `V`
(it does not depend on the choice of orthonormal basis). -/
noncomputable def intrinsicGw (𝒳 : Set (EuclideanSpace ℝ ι)) : ℝ :=
  gw ((fun x : Submodule.span ℝ 𝒳 ↦ (stdOrthonormalBasis ℝ (Submodule.span ℝ 𝒳)).repr x) ''
    (Subtype.val ⁻¹' 𝒳))

section gwMat

variable {K : Set (EuclideanSpace ℝ ι)} {R : ℝ} {A B : Matrix ι ι ℝ}

lemma integrable_supportFn_multivariateGaussian (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Integrable (supportFn K) (multivariateGaussian μ S) :=
  integrable_supportFn_of_isGaussian hne hK

lemma gwMat_nonneg (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (A : Matrix ι ι ℝ) :
    0 ≤ gwMat K A :=
  gaussianWidth_nonneg_of_integral_eq_zero hne hK IsGaussian.integrable_id (by simp)

/-- The width of `-K` is the width of `K` (the Gaussian vector `G ~ N(0, A⁻¹)` is symmetric). -/
lemma gwMat_neg_set (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hA : A.PosDef) :
    gwMat (-K) A = gwMat K A := by
  rw [gwMat, gwMat, gaussianWidth_neg_set hne hK,
    multivariateGaussian_zero_map_neg hA.inv.posSemidef]

/-- `E[max_{x, y ∈ K} ⟪x - y, G⟫] = 2 gwMat K A` for `G ~ N(0, A⁻¹)`. -/
lemma gwMat_sub_set (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hA : A.PosDef) :
    gwMat (K - K) A = 2 * gwMat K A := by
  have hnegK : ∀ x ∈ -K, ‖x‖ ≤ R := fun x hx ↦ by simpa using hK (-x) hx
  rw [sub_eq_add_neg, gwMat, gaussianWidth_add hne hK hne.neg hnegK IsGaussian.integrable_id.norm,
    ← gwMat, ← gwMat, gwMat_neg_set hne hK hA]
  ring

/-- Homogeneity: `gwMat K (c • A) = c^{-1/2} gwMat K A` for `c > 0`. -/
lemma gwMat_smul (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) :
    gwMat K (c • A) = (√c)⁻¹ * gwMat K A := by
  have hinv : (c • A)⁻¹ = ((√c)⁻¹) ^ 2 • A⁻¹ := by
    let _ := invertibleOfNonzero hc.ne'
    rw [Matrix.inv_smul (A := A) c hA.det_pos.ne'.isUnit, invOf_eq_inv, inv_pow,
      Real.sq_sqrt hc.le]
  rw [gwMat, gwMat, hinv, ← multivariateGaussian_zero_map_smul hA.inv.posSemidef,
    gaussianWidth_map_smul hne hK (by positivity)]

/-- Monotonicity in the Loewner order: `A ≤ B` implies `gwMat K B ≤ gwMat K A` (the Gaussian
vector `N(0, A⁻¹)` is `N(0, B⁻¹)` plus an independent centered Gaussian noise). -/
lemma gwMat_anti (hK : IsCompact K) (hne : K.Nonempty) (hA : A.PosDef) (hAB : A ≤ B) :
    gwMat K B ≤ gwMat K A := by
  have hB : B.PosDef := by simpa using hA.add_posSemidef (Matrix.le_iff.1 hAB)
  have hdiff : (A⁻¹ - B⁻¹).PosSemidef := Matrix.le_iff.1 (hA.inv_le_inv hAB)
  have h : multivariateGaussian 0 A⁻¹ =
      multivariateGaussian 0 B⁻¹ ∗ multivariateGaussian 0 (A⁻¹ - B⁻¹) := by
    rw [multivariateGaussian_conv hB.inv.posSemidef hdiff]
    simp
  rw [gwMat, gwMat, h]
  exact gaussianWidth_le_gaussianWidth_conv hK hne IsGaussian.integrable_id
    IsGaussian.integrable_id (by simp)

/-- Whitening: the width of `K` for `A` is the width of `A^{-1/2} K` for the standard Gaussian
measure, `gwMat K A = E[sup_{x ∈ K} ⟪A^{-1/2} x, g⟫]` with `g ~ N(0, I)`. -/
lemma gwMat_eq_gaussianWidth_stdGaussian (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (A : Matrix ι ι ℝ) :
    gwMat K A = gaussianWidth (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) '' K)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hsqrt : (CFC.sqrt A⁻¹)ᵀ = CFC.sqrt A⁻¹ := by
    have h : (CFC.sqrt A⁻¹).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, h.1.eq]
  rw [gwMat, multivariateGaussian]
  simp only [zero_add]
  rw [gaussianWidth_map hne hK, adjoint_toEuclideanCLM, hsqrt]

/-- The width of `K` for `A` is at most `sup_{x ∈ K} ‖A^{-1/2} x‖ · √d`. -/
lemma gwMat_le_mul_sqrt_card (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (A : Matrix ι ι ℝ)
    {R' : ℝ} (hR' : ∀ x ∈ K, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) x‖ ≤ R') :
    gwMat K A ≤ R' * √(Fintype.card ι) := by
  rw [gwMat_eq_gaussianWidth_stdGaussian hne hK A]
  have hR'' : ∀ y ∈ Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) '' K, ‖y‖ ≤ R' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hR' x hx
  refine (le_abs_self _).trans ((abs_gaussianWidth_le (hne.image _) hR''
    IsGaussian.integrable_id.norm).trans ?_)
  exact mul_le_mul_of_nonneg_left integral_norm_stdGaussian_le
    (nonneg_of_norm_le (hne.image _) hR'')

/-- Invariance under invertible linear maps: `gwMat (M '' K) (M A Mᵀ) = gwMat K A`. -/
lemma gwMat_image (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hA : A.PosDef)
    {M : Matrix ι ι ℝ} (hM : IsUnit M.det) :
    gwMat (Matrix.toEuclideanCLM (𝕜 := ℝ) M '' K) (M * A * Mᵀ) = gwMat K A := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hL
  have hne' : (L '' K).Nonempty := hne.image L
  have hK' : ∀ y ∈ L '' K, ‖y‖ ≤ ‖L‖ * R := by
    rintro _ ⟨x, hx, rfl⟩
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hK x hx) (norm_nonneg _))
  have h1 : (M * A * Mᵀ)⁻¹ = Mᵀ⁻¹ * A⁻¹ * (Mᵀ⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  have h2 : ∀ x, Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ (L x) = x := fun x ↦ by
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ * Matrix.toEuclideanCLM (𝕜 := ℝ) M) x = x
    rw [← map_mul, Matrix.nonsing_inv_mul _ hM, map_one]
    rfl
  rw [gwMat, gwMat, h1, ← multivariateGaussian_zero_map_toEuclideanCLM hA.inv.posSemidef,
    gaussianWidth_map hne' hK', adjoint_toEuclideanCLM, ← Matrix.transpose_nonsing_inv,
    Matrix.transpose_transpose, Set.image_image]
  simp only [h2, Set.image_id']

end gwMat

section gw

variable {𝒳 : Set (EuclideanSpace ℝ ι)} {R : ℝ} {A : Matrix ι ι ℝ}

/-- The set of positive definite design matrices of `𝒳`, over which `gw 𝒳` is an infimum. -/
abbrev posDefDesigns (𝒳 : Set (EuclideanSpace ℝ ι)) : Set (Matrix ι ι ℝ) :=
  {A | A ∈ designSet 𝒳 ∧ A.PosDef}

lemma gw_eq_iInf (𝒳 : Set (EuclideanSpace ℝ ι)) :
    gw 𝒳 = ⨅ A : posDefDesigns 𝒳, gwMat 𝒳 A := rfl

lemma bddBelow_range_gwMat (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) :
    BddBelow (Set.range fun A : posDefDesigns 𝒳 ↦ gwMat 𝒳 A) :=
  ⟨0, by rintro _ ⟨A, rfl⟩; exact gwMat_nonneg hne hR _⟩

lemma gw_nonneg (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) : 0 ≤ gw 𝒳 :=
  Real.iInf_nonneg fun A ↦ gwMat_nonneg hne hR A

/-- The Gaussian width term is at most the width for every positive definite design matrix. -/
lemma gw_le_gwMat (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hA : A ∈ designSet 𝒳)
    (hA' : A.PosDef) :
    gw 𝒳 ≤ gwMat 𝒳 A :=
  ciInf_le (bddBelow_range_gwMat hne hR) (⟨A, hA, hA'⟩ : posDefDesigns 𝒳)

/-- A lower bound on the width for every positive definite design matrix is a lower bound on the
Gaussian width term, provided a positive definite design matrix exists. -/
lemma le_gw (hex : ∃ A ∈ designSet 𝒳, A.PosDef) {c : ℝ}
    (h : ∀ A ∈ designSet 𝒳, A.PosDef → c ≤ gwMat 𝒳 A) :
    c ≤ gw 𝒳 := by
  obtain ⟨A₀, hA₀, hA₀'⟩ := hex
  have : Nonempty {A : Matrix ι ι ℝ // A ∈ designSet 𝒳 ∧ A.PosDef} := ⟨⟨A₀, hA₀, hA₀'⟩⟩
  exact le_ciInf fun A ↦ h A A.2.1 A.2.2

end gw

end COLT83
