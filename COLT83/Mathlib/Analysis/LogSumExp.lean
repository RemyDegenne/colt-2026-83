/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Log-sum-exp smoothing of a maximum of linear forms

For a finite family `x : ι → E` of vectors of a real inner product space and `β > 0`, the
log-sum-exp function `logSumExp β x v = (1/β) log ∑ i, exp (β ⟪x i, v⟫)` is a `C¹` smoothing of
the maximum `v ↦ ⨆ i, ⟪x i, v⟫`:
* it is sandwiched between the maximum and the maximum plus `log (card ι) / β`
  (`ciSup_inner_le_logSumExp`, `logSumExp_le_ciSup_inner_add`);
* its gradient is the convex combination `∑ i, softmax β x v i • x i` of the vectors `x i` with
  the softmax weights (`hasGradientAt_logSumExp`), hence has norm at most `sup_i ‖x i‖`
  (`norm_gradient_logSumExp_le`).
-/

@[expose] public section
set_option autoImplicit false

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℝ}

/-- The softmax weights `exp (β ⟪x i, v⟫) / ∑ j, exp (β ⟪x j, v⟫)`. -/
noncomputable def softmax (β : ℝ) (x : ι → E) (v : E) (i : ι) : ℝ :=
  Real.exp (β * ⟪x i, v⟫) / ∑ j, Real.exp (β * ⟪x j, v⟫)

/-- The log-sum-exp smoothing `(1/β) log ∑ i, exp (β ⟪x i, v⟫)` of `v ↦ max_i ⟪x i, v⟫`. -/
noncomputable def logSumExp (β : ℝ) (x : ι → E) (v : E) : ℝ :=
  (1 / β) * Real.log (∑ i, Real.exp (β * ⟪x i, v⟫))

/-- The denominator of the softmax weights is positive. -/
lemma sum_exp_inner_pos (β : ℝ) (x : ι → E) (v : E) : 0 < ∑ i, Real.exp (β * ⟪x i, v⟫) :=
  Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- The softmax weights are nonnegative. -/
lemma softmax_nonneg (β : ℝ) (x : ι → E) (v : E) (i : ι) : 0 ≤ softmax β x v i :=
  div_nonneg (Real.exp_pos _).le (sum_exp_inner_pos β x v).le

/-- The softmax weights sum to one. -/
lemma sum_softmax (β : ℝ) (x : ι → E) (v : E) : ∑ i, softmax β x v i = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (sum_exp_inner_pos β x v).ne'

omit [Nonempty ι] in
/-- The Fréchet derivative of `v ↦ ∑ i, exp (β ⟪x i, v⟫)`. -/
lemma hasFDerivAt_sum_exp_inner (β : ℝ) (x : ι → E) (v : E) :
    HasFDerivAt (fun v ↦ ∑ i, Real.exp (β * ⟪x i, v⟫))
      (∑ i, (Real.exp (β * ⟪x i, v⟫) * β) • innerSL ℝ (x i)) v := by
  refine HasFDerivAt.fun_sum fun i _ ↦ ?_
  have h : HasFDerivAt (fun v ↦ β * ⟪x i, v⟫) (β • innerSL ℝ (x i)) v :=
    (innerSL ℝ (x i)).hasFDerivAt.const_mul β
  simpa only [smul_smul] using h.exp

/-- The log-sum-exp function is `C¹`. -/
lemma contDiff_logSumExp (β : ℝ) (x : ι → E) : ContDiff ℝ 1 (logSumExp β x) := by
  have h : ContDiff ℝ 1 fun v ↦ ∑ i, Real.exp (β * ⟪x i, v⟫) :=
    ContDiff.sum fun i _ ↦ (contDiff_const.mul (innerSL ℝ (x i)).contDiff).exp
  exact contDiff_const.mul (h.log fun v ↦ (sum_exp_inner_pos β x v).ne')

section gradient

variable [CompleteSpace E]

/-- The gradient of the log-sum-exp function is the softmax-weighted average of the `x i`. -/
lemma hasGradientAt_logSumExp (hβ : 0 < β) (x : ι → E) (v : E) :
    HasGradientAt (logSumExp β x) (∑ i, softmax β x v i • x i) v := by
  have h := ((hasFDerivAt_sum_exp_inner β x v).log (sum_exp_inner_pos β x v).ne').const_mul
    (1 / β)
  refine hasGradientAt_iff_hasFDerivAt.2 (h.congr_fderiv ?_)
  ext w
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply,
    toDual_apply_apply, sum_inner, real_inner_smul_left, softmax, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp

/-- If `‖x i‖ ≤ R` for all `i`, the gradient of the log-sum-exp function has norm at most `R`. -/
lemma norm_gradient_logSumExp_le (hβ : 0 < β) {x : ι → E} {R : ℝ} (hR : ∀ i, ‖x i‖ ≤ R) (v : E) :
    ‖gradient (logSumExp β x) v‖ ≤ R := by
  rw [(hasGradientAt_logSumExp hβ x v).gradient]
  calc ‖∑ i, softmax β x v i • x i‖ ≤ ∑ i, ‖softmax β x v i • x i‖ := norm_sum_le _ _
    _ = ∑ i, softmax β x v i * ‖x i‖ := by
      simp_rw [norm_smul, Real.norm_of_nonneg (softmax_nonneg _ _ _ _)]
    _ ≤ ∑ i, softmax β x v i * R :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hR i) (softmax_nonneg _ _ _ _)
    _ = R := by rw [← Finset.sum_mul, sum_softmax, one_mul]

end gradient

/-- The log-sum-exp function dominates the maximum `⨆ i, ⟪x i, v⟫`. -/
lemma ciSup_inner_le_logSumExp (hβ : 0 < β) (x : ι → E) (v : E) :
    (⨆ i, ⟪x i, v⟫) ≤ logSumExp β x v := by
  refine ciSup_le fun i ↦ ?_
  rw [logSumExp, one_div, ← div_eq_inv_mul, le_div_iff₀ hβ, mul_comm ⟪x i, v⟫ β,
    Real.le_log_iff_exp_le (sum_exp_inner_pos β x v)]
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (β * ⟪x j, v⟫)).le) (Finset.mem_univ i)

/-- The log-sum-exp function exceeds the maximum `⨆ i, ⟪x i, v⟫` by at most
`log (card ι) / β`. -/
lemma logSumExp_le_ciSup_inner_add (hβ : 0 < β) (x : ι → E) (v : E) :
    logSumExp β x v ≤ (⨆ i, ⟪x i, v⟫) + Real.log (Fintype.card ι) / β := by
  have hbdd : BddAbove (Set.range fun i ↦ ⟪x i, v⟫) := Finite.bddAbove_range _
  have hS : ∑ i, Real.exp (β * ⟪x i, v⟫) ≤ Fintype.card ι * Real.exp (β * ⨆ i, ⟪x i, v⟫) := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun i ↦ Real.exp (β * ⟪x i, v⟫))
      (Real.exp (β * ⨆ i, ⟪x i, v⟫)) fun i _ ↦
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_ciSup hbdd i) hβ.le)
    simpa [nsmul_eq_mul] using h
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [logSumExp, one_div, ← div_eq_inv_mul, div_le_iff₀ hβ]
  calc Real.log (∑ i, Real.exp (β * ⟪x i, v⟫))
      ≤ Real.log (Fintype.card ι * Real.exp (β * ⨆ i, ⟪x i, v⟫)) :=
        Real.log_le_log (sum_exp_inner_pos β x v) hS
    _ = β * (⨆ i, ⟪x i, v⟫) + Real.log (Fintype.card ι) := by
        rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp, add_comm]
    _ = ((⨆ i, ⟪x i, v⟫) + Real.log (Fintype.card ι) / β) * β := by
        rw [add_mul, div_mul_cancel₀ _ hβ.ne', mul_comm]
