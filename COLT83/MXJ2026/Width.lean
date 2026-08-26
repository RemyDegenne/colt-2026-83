/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.GaussianWidth
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
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped RealInnerProductSpace

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

end COLT83
