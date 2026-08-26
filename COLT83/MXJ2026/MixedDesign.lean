/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.OptimalDesign
public import COLT83.MXJ2026.Width

/-!
# The mixed design

The mixture `mixDesign w₁ w₂ = ½ w₁ + ½ w₂` of two design distributions is a design distribution
with design matrix `½ A(w₁) + ½ A(w₂)` (blueprint `def:mixed_design`). When `w₂` is `G`-optimal
and `A(w₁)` is positive definite, the mixed design matrix `A₀` satisfies `xᵀ A₀⁻¹ x ≤ 2 d` on
`𝒳` and `gwMat 𝒳 A₀ ≤ √2 gwMat 𝒳 A(w₁)` (blueprint `lem:mixed_design_bounds`): the mixed design
is simultaneously nearly `G`-optimal and nearly width-optimal.
-/

@[expose] public section

open Finset Matrix Real
open scoped Matrix MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {w₁ w₂ : EuclideanSpace ℝ ι →₀ ℝ}

/-- The mixture `½ w₁ + ½ w₂` of two design distributions. -/
noncomputable def mixDesign (w₁ w₂ : EuclideanSpace ℝ ι →₀ ℝ) : EuclideanSpace ℝ ι →₀ ℝ :=
  (1 / 2 : ℝ) • w₁ + (1 / 2 : ℝ) • w₂

omit [Fintype ι] in
lemma designMatrix_mixDesign (w₁ w₂ : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix (mixDesign w₁ w₂) =
      (1 / 2 : ℝ) • designMatrix w₁ + (1 / 2 : ℝ) • designMatrix w₂ := by
  simp [mixDesign, map_add, map_smul]

omit [Fintype ι] in
/-- The mixture of two design distributions on `𝒳` is a design distribution on `𝒳`. -/
lemma IsDesign.mixDesign (h₁ : IsDesign 𝒳 w₁) (h₂ : IsDesign 𝒳 w₂) :
    IsDesign 𝒳 (mixDesign w₁ w₂) where
  support_subset := by
    classical
    refine (Finset.coe_subset.2 Finsupp.support_add).trans ?_
    rw [Finset.coe_union]
    exact Set.union_subset
      ((Finset.coe_subset.2 Finsupp.support_smul).trans h₁.support_subset)
      ((Finset.coe_subset.2 Finsupp.support_smul).trans h₂.support_subset)
  nonneg x := by
    simp only [COLT83.mixDesign, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have := h₁.nonneg x
    have := h₂.nonneg x
    positivity
  sum_eq_one := by
    change (COLT83.mixDesign w₁ w₂).sum (fun _ v ↦ v) = 1
    rw [COLT83.mixDesign, Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finsupp.sum_smul_index' (fun _ ↦ rfl), Finsupp.sum_smul_index' (fun _ ↦ rfl)]
    simp only [smul_eq_mul, ← Finsupp.mul_sum]
    change 1 / 2 * ∑ x ∈ w₁.support, w₁ x + 1 / 2 * ∑ x ∈ w₂.support, w₂ x = 1
    rw [h₁.sum_eq_one, h₂.sum_eq_one]
    norm_num

omit [Fintype ι] in
/-- `½ A(w₁) ⪯ A(mixDesign w₁ w₂)` when `A(w₂)` is positive semidefinite. -/
lemma smul_designMatrix_le_designMatrix_mixDesign_left (h₂ : (designMatrix w₂).PosSemidef) :
    (1 / 2 : ℝ) • designMatrix w₁ ≤ designMatrix (mixDesign w₁ w₂) := by
  rw [Matrix.le_iff, designMatrix_mixDesign, add_sub_cancel_left]
  exact h₂.smul (by norm_num)

omit [Fintype ι] in
/-- `½ A(w₂) ⪯ A(mixDesign w₁ w₂)` when `A(w₁)` is positive semidefinite. -/
lemma smul_designMatrix_le_designMatrix_mixDesign_right (h₁ : (designMatrix w₁).PosSemidef) :
    (1 / 2 : ℝ) • designMatrix w₂ ≤ designMatrix (mixDesign w₁ w₂) := by
  rw [Matrix.le_iff, designMatrix_mixDesign, add_sub_cancel_right]
  exact h₁.smul (by norm_num)

omit [Fintype ι] in
/-- The mixed design matrix is positive definite as soon as one of the two design matrices is. -/
lemma posDef_designMatrix_mixDesign (h₁ : (designMatrix w₁).PosDef)
    (h₂ : (designMatrix w₂).PosSemidef) : (designMatrix (mixDesign w₁ w₂)).PosDef := by
  rw [designMatrix_mixDesign]
  exact (h₁.smul (by norm_num)).add_posSemidef (h₂.smul (by norm_num))

variable [DecidableEq ι]

/-- **Bounds for the mixed design, `G`-optimality part** (blueprint `lem:mixed_design_bounds`):
if `w₂` is `G`-optimal, `xᵀ A₀⁻¹ x ≤ 2 d` on `𝒳` for the mixed design matrix `A₀`. -/
theorem IsGOptimalDesign.dotProduct_inv_designMatrix_mixDesign_le (hw₂ : IsGOptimalDesign 𝒳 w₂)
    (h₁ : (designMatrix w₁).PosSemidef) {x : EuclideanSpace ℝ ι} (hx : x ∈ 𝒳) :
    WithLp.ofLp x ⬝ᵥ (designMatrix (mixDesign w₁ w₂))⁻¹ *ᵥ WithLp.ofLp x ≤ 2 * Fintype.card ι := by
  have h := hw₂.posDef.dotProduct_inv_mulVec_le_of_smul_le (by norm_num : (0 : ℝ) < 1 / 2)
    (smul_designMatrix_le_designMatrix_mixDesign_right h₁) (WithLp.ofLp x)
  rw [star_trivial] at h
  have := hw₂.dotProduct_inv_mulVec_le x hx
  linarith

/-- **Bounds for the mixed design, width part** (blueprint `lem:mixed_design_bounds`):
`gwMat 𝒳 A₀ ≤ √2 gwMat 𝒳 A(w₁)` for the mixed design matrix `A₀`. -/
theorem gwMat_designMatrix_mixDesign_le (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (h₁ : (designMatrix w₁).PosDef) (h₂ : (designMatrix w₂).PosSemidef) :
    gwMat 𝒳 (designMatrix (mixDesign w₁ w₂)) ≤ √2 * gwMat 𝒳 (designMatrix w₁) := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  calc gwMat 𝒳 (designMatrix (mixDesign w₁ w₂))
      ≤ gwMat 𝒳 ((1 / 2 : ℝ) • designMatrix w₁) :=
        gwMat_anti h𝒳 hne (h₁.smul (by norm_num))
          (smul_designMatrix_le_designMatrix_mixDesign_left h₂)
    _ = √2 * gwMat 𝒳 (designMatrix w₁) := by
        rw [gwMat_smul hne hR h₁ (by norm_num), one_div, Real.sqrt_inv, inv_inv]

end COLT83
