/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Matrix.Loewner
public import COLT83.Mathlib.Analysis.InnerProductSpace.EuclideanMatrix
public import Mathlib.Topology.Instances.Matrix

/-!
# The rank-one matrices `x xᵀ`

`outerSelf x = x xᵀ` for `x : EuclideanSpace ℝ ι`, and its basic properties: positive
semidefiniteness, trace, continuity, action as a linear map (`x xᵀ θ = ⟪x, θ⟫ x`), quadratic
form (`uᵀ (x xᵀ) u = ⟪u, x⟫²`), behaviour under linear maps (`(M x)(M x)ᵀ = M (x xᵀ) Mᵀ`) and
the matrix determinant lemma for `(1 - t) A + t x xᵀ`.
-/

@[expose] public section

open Matrix
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*}

/-- The design matrix `x xᵀ` of a point `x`. -/
def outerSelf (x : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x)

lemma outerSelf_eq_vecMulVec (x : EuclideanSpace ℝ ι) :
    outerSelf x = Matrix.vecMulVec (WithLp.ofLp x) (WithLp.ofLp x) := rfl

/-- `outerSelf` is continuous. -/
lemma continuous_outerSelf : Continuous (outerSelf (ι := ι)) :=
  Continuous.matrix_vecMulVec (PiLp.continuous_ofLp _ _) (PiLp.continuous_ofLp _ _)

/-- The design matrix `x xᵀ` is positive semidefinite. -/
lemma outerSelf_posSemidef [Finite ι] (x : EuclideanSpace ℝ ι) : (outerSelf x).PosSemidef := by
  have := Fintype.ofFinite ι
  simpa [outerSelf] using Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp x)

lemma posSemidef_sum_outerSelf [Finite ι] {κ : Type*} (s : Finset κ)
    (x : κ → EuclideanSpace ℝ ι) :
    (∑ t ∈ s, outerSelf (x t)).PosSemidef := by
  have := Fintype.ofFinite ι
  exact Finset.sum_induction _ _ (fun _ _ ha hb ↦ ha.add hb) Matrix.PosSemidef.zero
    fun t _ ↦ outerSelf_posSemidef (x t)

lemma transpose_sum_outerSelf {T : ℕ} (x : Fin T → EuclideanSpace ℝ ι) :
    (∑ t, outerSelf (x t))ᵀ = ∑ t, outerSelf (x t) := by
  simp [Matrix.transpose_sum, outerSelf_eq_vecMulVec, Matrix.transpose_vecMulVec]

variable [Fintype ι]

/-- The trace of `x xᵀ` is `‖x‖ ^ 2`. -/
lemma trace_outerSelf (x : EuclideanSpace ℝ ι) : (outerSelf x).trace = ‖x‖ ^ 2 := by
  rw [outerSelf, Matrix.trace_vecMulVec, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- `xᵀ M x = tr (M x xᵀ)`. -/
lemma dotProduct_mulVec_eq_trace_mul_outerSelf (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp x = (M * outerSelf x).trace := by
  rw [outerSelf, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- `uᵀ (y yᵀ) u = ⟪u, y⟫ ^ 2`. -/
lemma dotProduct_outerSelf_mulVec (u y : EuclideanSpace ℝ ι) :
    WithLp.ofLp u ⬝ᵥ outerSelf y *ᵥ WithLp.ofLp u = ⟪u, y⟫ ^ 2 := by
  rw [outerSelf, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul, sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm (WithLp.ofLp u)]

variable [DecidableEq ι]

/-- `(M x) (M x)ᵀ = M (x xᵀ) Mᵀ`. -/
lemma outerSelf_toEuclideanCLM (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    outerSelf (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) = M * outerSelf x * Mᵀ := by
  rw [outerSelf, outerSelf, Matrix.ofLp_toEuclideanCLM, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- `(N x)(N x)ᵀ = N (x xᵀ) Nᵀ` for a rectangular matrix `N`. -/
lemma outerSelf_toEuclideanLin {κ : Type*} (N : Matrix κ ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    outerSelf (Matrix.toEuclideanLin N x) = N * outerSelf x * Nᵀ := by
  rw [outerSelf, outerSelf, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

/-- The action of `x xᵀ` on `θ` is `⟪x, θ⟫ • x`. -/
lemma toEuclideanCLM_outerSelf_apply (x θ : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (outerSelf x) θ = ⟪x, θ⟫ • x := by
  apply WithLp.ofLp_injective
  ext i
  simp [Matrix.ofLp_toEuclideanCLM, outerSelf_eq_vecMulVec, Matrix.vecMulVec_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma toEuclideanCLM_sum_outerSelf_apply {T : ℕ} (x : Fin T → EuclideanSpace ℝ ι)
    (θ : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ t, outerSelf (x t)) θ = ∑ t, ⟪x t, θ⟫ • x t := by
  simp [map_sum, toEuclideanCLM_outerSelf_apply]

/-- The determinant of the mixture `(1 - t) A + t x xᵀ` of an invertible matrix `A` with a
rank-one matrix, by the matrix determinant lemma. -/
lemma det_smul_add_smul_outerSelf {A : Matrix ι ι ℝ} (hA : IsUnit A.det) {t : ℝ} (ht : t ≠ 1)
    (x : EuclideanSpace ℝ ι) :
    ((1 - t) • A + t • outerSelf x).det =
      (1 - t) ^ Fintype.card ι * A.det *
        (1 + t / (1 - t) * (WithLp.ofLp x ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp x)) := by
  have hs : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hsA : IsUnit ((1 - t) • A).det := by
    rw [Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ hs)).mul hA
  have h_inv : ((1 - t) • A)⁻¹ = (1 - t)⁻¹ • A⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.nonsing_inv_mul A hA, inv_mul_cancel₀ hs, one_smul]
  rw [outerSelf, ← Matrix.smul_vecMulVec, Matrix.det_add_vecMulVec hsA, Matrix.det_smul, h_inv,
    Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, div_eq_mul_inv]
  ring

end COLT83
