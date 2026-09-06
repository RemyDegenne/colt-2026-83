/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.DifferenceProcess

/-!
# The unit ball as an action set

Basic properties of the closed unit ball `unitBall ι` of `EuclideanSpace ℝ ι`: it is compact,
nonempty, spanning, its support function is the norm (`supportFn_unitBall`) and the simple regret
of `x` for the reward vector `θ` is `‖θ‖ - ⟪x, θ⟫` (`simpleRegret_unitBall`).
-/

@[expose] public section

open Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] {x : EuclideanSpace ℝ ι}

lemma mem_unitBall_iff : x ∈ unitBall ι ↔ ‖x‖ ≤ 1 := by simp [unitBall]

lemma norm_le_one_of_mem_unitBall (hx : x ∈ unitBall ι) : ‖x‖ ≤ 1 := mem_unitBall_iff.1 hx

lemma zero_mem_unitBall : (0 : EuclideanSpace ℝ ι) ∈ unitBall ι := by simp [mem_unitBall_iff]

lemma unitBall_nonempty : (unitBall ι).Nonempty := ⟨0, zero_mem_unitBall⟩

lemma isCompact_unitBall : IsCompact (unitBall ι) := isCompact_closedBall 0 1

/-- The unit ball is spanning: it contains the standard basis. -/
lemma span_unitBall : Submodule.span ℝ (unitBall ι) = ⊤ := by
  classical
  refine eq_top_iff.2 ?_
  rw [← (EuclideanSpace.basisFun ι ℝ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  simp [mem_unitBall_iff, EuclideanSpace.basisFun_apply]

/-- The support function of the unit ball is the norm. -/
lemma supportFn_unitBall (ξ : EuclideanSpace ℝ ι) : supportFn (unitBall ι) ξ = ‖ξ‖ := by
  have hR : ∀ y ∈ unitBall ι, ‖y‖ ≤ 1 := fun y hy ↦ norm_le_one_of_mem_unitBall hy
  refine le_antisymm (supportFn_le unitBall_nonempty fun y hy ↦ ?_) ?_
  · calc ⟪y, ξ⟫ ≤ ‖y‖ * ‖ξ‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖ξ‖ := by gcongr; exact norm_le_one_of_mem_unitBall hy
      _ = ‖ξ‖ := one_mul _
  · by_cases hξ : ξ = 0
    · subst hξ
      simpa using inner_le_supportFn hR zero_mem_unitBall (0 : EuclideanSpace ℝ ι)
    · have hξ' : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
      have hmem : ‖ξ‖⁻¹ • ξ ∈ unitBall ι := by
        rw [mem_unitBall_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ']
      have := inner_le_supportFn hR hmem ξ
      rwa [real_inner_smul_left, real_inner_self_eq_norm_sq, sq, inv_mul_cancel_left₀ hξ'] at this

/-- The simple regret on the unit ball: `r(x, θ) = ‖θ‖ - ⟪x, θ⟫`. -/
lemma simpleRegret_unitBall (θ x : EuclideanSpace ℝ ι) :
    simpleRegret (unitBall ι) θ x = ‖θ‖ - ⟪x, θ⟫ := by
  rw [simpleRegret_eq_supportFn_sub, supportFn_unitBall]

end COLT83
