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
  (`norm_gradient_logSumExp_le`);
* it is smooth (`contDiff_logSumExp'`), with second derivative the softmax-weighted covariance of
  the linear forms `⟪x i, ·⟫` (`fderiv_fderiv_logSumExp_apply`), whose operator norm is at most
  `β * (sup_i ‖x i‖) ^ 2` (`norm_fderiv_fderiv_logSumExp_le`).
-/

@[expose] public section
set_option autoImplicit false

open InnerProductSpace
open scoped RealInnerProductSpace

/-- Bound on a weighted covariance: if `p` is a probability vector and `|a i| ≤ A`, `|b i| ≤ B`
for all `i`, then `|∑ i, p i * (a i * b i) - (∑ i, p i * a i) * (∑ i, p i * b i)| ≤ A * B`. -/
lemma abs_sum_mul_sub_mul_le {ι : Type*} [Fintype ι] {p a b : ι → ℝ} {A B : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ha : ∀ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ B) :
    |∑ i, p i * (a i * b i) - (∑ i, p i * a i) * (∑ i, p i * b i)| ≤ A * B := by
  obtain ⟨i₀, -⟩ := Finset.nonempty_of_sum_ne_zero (hp1.trans_ne one_ne_zero)
  have hA : 0 ≤ A := (abs_nonneg _).trans (ha i₀)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb i₀)
  -- centered second moments are bounded by the squared bounds
  have key : ∀ (c : ι → ℝ) (C : ℝ), (∀ i, |c i| ≤ C) →
      ∑ i, p i * (c i - ∑ j, p j * c j) ^ 2 ≤ C ^ 2 := by
    intro c C hc
    have h1 : ∑ i, p i * (c i - ∑ j, p j * c j) ^ 2
        = ∑ i, p i * c i ^ 2 - (∑ j, p j * c j) ^ 2 := by
      have : ∀ i, p i * (c i - ∑ j, p j * c j) ^ 2
          = p i * c i ^ 2 - (2 * ∑ j, p j * c j) * (p i * c i) + (∑ j, p j * c j) ^ 2 * p i :=
        fun i ↦ by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1]
      ring
    calc ∑ i, p i * (c i - ∑ j, p j * c j) ^ 2
        ≤ ∑ i, p i * c i ^ 2 := by rw [h1]; exact sub_le_self _ (sq_nonneg _)
      _ ≤ ∑ i, p i * C ^ 2 := Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hc i)).1 (abs_le.1 (hc i)).2) (hp i)
      _ = C ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]
  -- the covariance is the sum of the centered products
  have hcov : ∑ i, p i * (a i * b i) - (∑ i, p i * a i) * (∑ i, p i * b i)
      = ∑ i, p i * ((a i - ∑ j, p j * a j) * (b i - ∑ j, p j * b j)) := by
    have : ∀ i, p i * ((a i - ∑ j, p j * a j) * (b i - ∑ j, p j * b j))
        = p i * (a i * b i) - (∑ j, p j * b j) * (p i * a i) - (∑ j, p j * a j) * (p i * b i)
          + (∑ j, p j * a j) * (∑ j, p j * b j) * p i :=
      fun i ↦ by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, hp1]
    ring
  -- Cauchy–Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ √(p i) * (a i - ∑ j, p j * a j)) (fun i ↦ √(p i) * (b i - ∑ j, p j * b j))
  have hfg : ∀ i, √(p i) * (a i - ∑ j, p j * a j) * (√(p i) * (b i - ∑ j, p j * b j))
      = p i * ((a i - ∑ j, p j * a j) * (b i - ∑ j, p j * b j)) := fun i ↦ by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hp i)]
  have hf : ∀ i, (√(p i) * (a i - ∑ j, p j * a j)) ^ 2 = p i * (a i - ∑ j, p j * a j) ^ 2 :=
    fun i ↦ by rw [mul_pow, Real.sq_sqrt (hp i)]
  have hg : ∀ i, (√(p i) * (b i - ∑ j, p j * b j)) ^ 2 = p i * (b i - ∑ j, p j * b j) ^ 2 :=
    fun i ↦ by rw [mul_pow, Real.sq_sqrt (hp i)]
  simp_rw [hfg, hf, hg] at hcs
  rw [hcov]
  refine abs_le_of_sq_le_sq (hcs.trans ?_) (mul_nonneg hA hB)
  rw [mul_pow]
  exact mul_le_mul (key a A ha) (key b B hb) (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hp i) (sq_nonneg _)) (sq_nonneg _)

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

/-- The log-sum-exp function is smooth. -/
lemma contDiff_logSumExp' (n : WithTop ℕ∞) (β : ℝ) (x : ι → E) :
    ContDiff ℝ n (logSumExp β x) := by
  have h : ContDiff ℝ n fun v ↦ ∑ i, Real.exp (β * ⟪x i, v⟫) :=
    ContDiff.sum fun i _ ↦ (contDiff_const.mul (innerSL ℝ (x i)).contDiff).exp
  exact contDiff_const.mul (h.log fun v ↦ (sum_exp_inner_pos β x v).ne')

/-- The log-sum-exp function is `C¹`. -/
lemma contDiff_logSumExp (β : ℝ) (x : ι → E) : ContDiff ℝ 1 (logSumExp β x) :=
  contDiff_logSumExp' 1 β x

section fderiv

/-- The Fréchet derivative of the log-sum-exp function is the softmax-weighted average
`∑ i, softmax β x v i • ⟪x i, ·⟫` of the linear forms `⟪x i, ·⟫`. -/
lemma hasFDerivAt_logSumExp (hβ : β ≠ 0) (x : ι → E) (v : E) :
    HasFDerivAt (logSumExp β x) (∑ i, softmax β x v i • innerSL ℝ (x i)) v := by
  have h := ((hasFDerivAt_sum_exp_inner β x v).log (sum_exp_inner_pos β x v).ne').const_mul
    (1 / β)
  refine h.congr_fderiv ?_
  ext w
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply, softmax,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp

/-- The Fréchet derivative of the log-sum-exp function. -/
lemma fderiv_logSumExp (hβ : β ≠ 0) (x : ι → E) (v : E) :
    fderiv ℝ (logSumExp β x) v = ∑ i, softmax β x v i • innerSL ℝ (x i) :=
  (hasFDerivAt_logSumExp hβ x v).fderiv

/-- The Fréchet derivative of the softmax weights:
`∂ p_i = β p_i (⟪x i, ·⟫ - ∑ j, p_j ⟪x j, ·⟫)`. -/
lemma hasFDerivAt_softmax (β : ℝ) (x : ι → E) (v : E) (i : ι) :
    HasFDerivAt (fun v ↦ softmax β x v i)
      ((β * softmax β x v i) • (innerSL ℝ (x i) - ∑ j, softmax β x v j • innerSL ℝ (x j))) v := by
  have hS := sum_exp_inner_pos β x v
  have hnum : HasFDerivAt (fun v ↦ Real.exp (β * ⟪x i, v⟫))
      ((Real.exp (β * ⟪x i, v⟫) * β) • innerSL ℝ (x i)) v := by
    have h : HasFDerivAt (fun v ↦ β * ⟪x i, v⟫) (β • innerSL ℝ (x i)) v :=
      (innerSL ℝ (x i)).hasFDerivAt.const_mul β
    simpa only [smul_smul] using h.exp
  have hden : HasFDerivAt (fun v ↦ (∑ j, Real.exp (β * ⟪x j, v⟫))⁻¹)
      ((-((∑ j, Real.exp (β * ⟪x j, v⟫)) ^ 2)⁻¹) •
        ∑ j, (Real.exp (β * ⟪x j, v⟫) * β) • innerSL ℝ (x j)) v :=
    (hasDerivAt_inv hS.ne').comp_hasFDerivAt v (hasFDerivAt_sum_exp_inner β x v)
  simp_rw [softmax, div_eq_mul_inv]
  refine (hnum.fun_mul hden).congr_fderiv ?_
  ext w
  simp only [smul_apply, add_apply, sub_apply, FunLike.coe_sum, Finset.sum_apply,
    innerSL_apply_apply, smul_eq_mul]
  have h1 : ∑ j, Real.exp (β * ⟪x j, v⟫) * β * ⟪x j, w⟫
      = β * ∑ j, Real.exp (β * ⟪x j, v⟫) * ⟪x j, w⟫ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h2 : ∑ j, Real.exp (β * ⟪x j, v⟫) * (∑ j, Real.exp (β * ⟪x j, v⟫))⁻¹ * ⟪x j, w⟫
      = (∑ j, Real.exp (β * ⟪x j, v⟫))⁻¹ * ∑ j, Real.exp (β * ⟪x j, v⟫) * ⟪x j, w⟫ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h1, h2]
  field_simp
  ring

/-- The second derivative of the log-sum-exp function, as a bilinear form:
`D²F(v)(u, w) = β (∑ i, p_i ⟪x i, u⟫ ⟪x i, w⟫ - (∑ i, p_i ⟪x i, u⟫) (∑ i, p_i ⟪x i, w⟫))`. -/
lemma hasFDerivAt_fderiv_logSumExp (hβ : β ≠ 0) (x : ι → E) (v : E) :
    HasFDerivAt (fderiv ℝ (logSumExp β x))
      (β • (∑ i, softmax β x v i • (innerSL ℝ (x i)).smulRight (innerSL ℝ (x i)) -
        (∑ i, softmax β x v i • innerSL ℝ (x i)).smulRight
          (∑ i, softmax β x v i • innerSL ℝ (x i)))) v := by
  have h : fderiv ℝ (logSumExp β x) = fun v ↦ ∑ i, softmax β x v i • innerSL ℝ (x i) :=
    funext (fderiv_logSumExp hβ x)
  rw [h]
  refine (HasFDerivAt.fun_sum fun i _ ↦
    (hasFDerivAt_softmax β x v i).smul_const (innerSL ℝ (x i))).congr_fderiv ?_
  ext u w
  simp only [smul_apply, sub_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The second derivative of the log-sum-exp function, applied to two vectors. -/
lemma fderiv_fderiv_logSumExp_apply (hβ : β ≠ 0) (x : ι → E) (v u w : E) :
    fderiv ℝ (fderiv ℝ (logSumExp β x)) v u w =
      β * (∑ i, softmax β x v i * (⟪x i, u⟫ * ⟪x i, w⟫) -
        (∑ i, softmax β x v i * ⟪x i, u⟫) * (∑ i, softmax β x v i * ⟪x i, w⟫)) := by
  rw [(hasFDerivAt_fderiv_logSumExp hβ x v).fderiv]
  simp only [smul_apply, sub_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- If `‖x i‖ ≤ R` for all `i`, the second derivative of the log-sum-exp function has operator
norm at most `β * R ^ 2`. -/
lemma norm_fderiv_fderiv_logSumExp_le (hβ : 0 < β) {x : ι → E} {R : ℝ} (hR : ∀ i, ‖x i‖ ≤ R)
    (v : E) : ‖fderiv ℝ (fderiv ℝ (logSumExp β x)) v‖ ≤ β * R ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR (Classical.arbitrary ι))
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u w ↦ ?_
  rw [fderiv_fderiv_logSumExp_apply hβ.ne' x v u w, Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
  have hbound (y : E) (i : ι) : |⟪x i, y⟫| ≤ R * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _))
  have h := abs_sum_mul_sub_mul_le (softmax_nonneg β x v) (sum_softmax β x v) (hbound u)
    (hbound w)
  calc β * |∑ i, softmax β x v i * (⟪x i, u⟫ * ⟪x i, w⟫) -
        (∑ i, softmax β x v i * ⟪x i, u⟫) * (∑ i, softmax β x v i * ⟪x i, w⟫)|
      ≤ β * (R * ‖u‖ * (R * ‖w‖)) := mul_le_mul_of_nonneg_left h hβ.le
    _ = β * R ^ 2 * ‖u‖ * ‖w‖ := by ring

end fderiv

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
