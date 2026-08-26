/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.LeanMachineLearning.RepeatTestGaussian
public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.Width
public import COLT83.MXJ2026.LowerAdaptiveBaseline
public import COLT83.MXJ2026.MixtureKL
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# The lower bound for adaptive algorithms (Theorem 2)

Every `(ε, δ)`-PAC identification algorithm (adaptive or not) on a spanning action set
`𝒳 ⊆ ℝ^d`, `d ≥ 2`, with `δ < 1/16`, has budget `T ≥ d log(1/δ) / (20000 ε²)`.

Blueprint: `thm:lower_adaptive` (with the constant `c_ad = 1/(11556 + 5760√2) ≥ 1/20000`).

## Proof

The baseline bound (`baseline_le_budget_of_isPAC`) gives `(2 - √2) log(1/δ) ≤ 64 ε² T`, in
particular `T ≥ 1`, say `T = n + 1`. The test algorithm `A.testAlg n` plays `A` for `n + 1` rounds
and then repeats the recommendation `m := ⌈8 log(2/δ)/ε²⌉` times; its decision is
`phaseMean > ε` where `phaseMean` is the empirical mean of the last `m` observations. Under the
reward vector `0` the decision is `true` with probability at most `δ`
(`measureReal_lt_phaseMean_le_of_testAlg`), and under each alternative `mixtureParam w ε x`
(`x` in the support of a `G`-optimal design `w`) it is `false` with probability at most `2δ`
(`measureReal_phaseMean_le_le_of_testAlg`, using the PAC guarantee of `A` transferred to the
test). The Bretagnolle–Huber inequality for the mixture of the alternatives
(`IsGOptimalDesign.exp_neg_le_of_mixture`) then gives `(n + m + 1) · 9ε²/(2d) ≥ log(1/(8δ))`,
and the arithmetic of the constants concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- **Theorem 2** (Maiti, Xu, Jamieson 2026): an identification algorithm (adaptive or not) with
budget `T` which is `(ε, δ)`-PAC on a spanning compact action set `𝒳 ⊆ ℝ^d`, `d ≥ 2`, with
`δ < 1/16`, satisfies `T ≥ d log(1/δ) / (20000 ε²)`. -/
theorem le_budget_of_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) (hd : 2 ≤ Fintype.card ι)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 (1 / 16)) {T : ℕ}
    (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T) (hpac : IsPAC 𝒳 A ε δ) :
    Fintype.card ι * log (1 / δ) / (20000 * ε ^ 2) ≤ T := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  have hδ0 : 0 < δ := hδ.1
  -- Step 1: consequences of `δ < 1/16`
  set L := log (1 / δ) with hL
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hLδ : L = -log δ := by rw [hL, one_div, log_inv]
  have hL16 : 4 * log 2 < L := by
    have h1 : log δ < log (1 / 16) := log_lt_log hδ0 hδ.2
    rw [show (1 / 16 : ℝ) = 2 ^ (-4 : ℤ) by norm_num, log_zpow] at h1
    push_cast at h1
    linarith
  have hlog4 : log (1 / (4 * δ)) = L - 2 * log 2 := by
    rw [one_div, log_inv, log_mul (by norm_num) hδ0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    linarith
  have hlog8 : log (1 / (8 * δ)) = L - 3 * log 2 := by
    rw [one_div, log_inv, log_mul (by norm_num) hδ0.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    push_cast
    linarith
  have hlog2δ : log (2 / δ) = L + log 2 := by
    rw [log_div (by norm_num) hδ0.ne']
    linarith
  have hLpos : 0 < L := by linarith
  -- Step 2: the baseline bound, hence `T ≥ 1`
  have hbase := baseline_le_budget_of_isPAC 𝒳 h𝒳 hspan hd hε ⟨hδ0, by linarith [hδ.2]⟩ A hA hpac
  have hsqrt2 : √2 < 2 := by
    calc √2 < √4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hiii : (2 - √2) * L ≤ 64 * (ε ^ 2 * T) := by
    rw [hlog4, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hbase
    have h2 : (2 - √2) * (L / 2) ≤ (2 - √2) * (L - 2 * log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with hT | hT
    · exfalso
      rw [hT] at hiii
      simp only [Nat.cast_zero, mul_zero] at hiii
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 - √2) hLpos]
    · exact hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  -- Step 3: the length of the second phase
  set m := ⌈8 * log (2 / δ) / ε ^ 2⌉₊ with hm_def
  have hlog2δpos : 0 < log (2 / δ) := by rw [hlog2δ]; linarith
  have hm_pos : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hm_ge : 8 * log (2 / δ) / ε ^ 2 ≤ m := Nat.le_ceil _
  have hm_le : (m : ℝ) ≤ 8 * log (2 / δ) / ε ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hconc : 2 * exp (-(m * ε ^ 2 / 8)) ≤ δ := by
    have h1 : log (2 / δ) ≤ m * ε ^ 2 / 8 := by
      rw [div_le_iff₀ (by positivity)] at hm_ge
      linarith
    calc 2 * exp (-(m * ε ^ 2 / 8)) ≤ 2 * exp (-log (2 / δ)) := by gcongr
      _ = δ := by
        rw [exp_neg, exp_log (by positivity)]
        field_simp
  -- Step 4: the test algorithm and its errors
  have : StandardBorelSpace 𝒳 := h𝒳.isClosed.measurableSet.standardBorel
  have := hA.isMarkovKernel_output
  set alg := A.testAlg n with halg
  have hrun : ∀ θ, IsAlgEnvSeq IT.action IT.feedback alg (linearGaussianEnv 𝒳 θ)
      (trajMeasure alg (linearGaussianEnv 𝒳 θ)) := fun θ ↦ IT.isAlgEnvSeq_trajMeasure alg _
  obtain ⟨w, hw⟩ := exists_isGOptimalDesign h𝒳 hspan
  set N := n + m with hN
  set g : (Iic N → 𝒳 × ℝ) → ℝ := fun h ↦
    (∑ s ∈ range m, (h ⟨min (n + 1 + s) N, Finset.mem_Iic.2 (min_le_right _ _)⟩).2) / m with hg
  have hg_meas : Measurable g :=
    (Finset.measurable_sum _ fun s _ ↦ (measurable_pi_apply _).snd).div_const _
  have hg_comp : g ∘ IT.hist N = phaseMean IT.feedback n m := by
    ext ω
    simp only [Function.comp_apply, hg, phaseMean, IT.hist, IT.feedback]
    congr 1
    refine sum_congr rfl fun s hs ↦ ?_
    rw [min_eq_left (by simp only [mem_range] at hs; omega)]
  set E' : Set (Iic N → 𝒳 × ℝ) := {h | ε < g h} with hE'
  have hE'm : MeasurableSet E' := measurableSet_lt measurable_const hg_meas
  have hpre : IT.hist N ⁻¹' E' = {ω | ε < phaseMean IT.feedback n m ω} := by
    rw [← hg_comp]
    rfl
  have hpre' : IT.hist N ⁻¹' E'ᶜ = {ω | phaseMean IT.feedback n m ω ≤ ε} := by
    rw [Set.preimage_compl, hpre]
    ext ω
    simp [not_lt]
  have hα : (histLaw alg N 0).real E' ≤ δ := by
    rw [histLaw_real_apply _ _ _ hE'm, hpre]
    exact (measureReal_lt_phaseMean_le_of_testAlg (hrun 0) hm_pos hε).trans hconc
  have hβ : ∀ x ∈ w.support, (histLaw alg N (mixtureParam w ε x)).real E'ᶜ ≤ 2 * δ := by
    intro x hx
    rw [histLaw_real_apply _ _ _ hE'm.compl, hpre']
    refine (measureReal_phaseMean_le_le_of_testAlg hR hε hpac hA
      (hw.isDesign.mem_of_mem_support hx) (hw.inner_mixtureParam_self ε hx).ge (hrun _)
      hm_pos).trans ?_
    linarith
  -- Step 5: the testing lower bound
  have hbh := hw.exp_neg_le_of_mixture alg N hR ε hE'm (by positivity) hα hβ
  have hexp : exp (-((N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)))) ≤ 8 * δ := by linarith
  have hlog : log (1 / (8 * δ)) ≤ (N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)) := by
    rw [one_div, log_inv, neg_le]
    exact (le_log_iff_exp_le (by positivity)).2 hexp
  have hd0 : (0 : ℝ) < Fintype.card ι := by positivity
  have hi : Fintype.card ι * L ≤ 18 * (ε ^ 2 * (N + 1)) := by
    rw [hlog8, mul_div_assoc', le_div_iff₀ (by positivity)] at hlog
    have h1 : Fintype.card ι * L / 2 ≤ (L - 3 * log 2) * (2 * Fintype.card ι) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ L - 3 * log 2 - L / 4) hd0.le]
    linarith
  -- Step 6: the constant
  have hii : ε ^ 2 * m ≤ 10 * L + ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hm_le (sq_nonneg ε)
    have h2 : ε ^ 2 * (8 * log (2 / δ) / ε ^ 2 + 1) = 8 * log (2 / δ) + ε ^ 2 := by
      field_simp
    rw [h2, hlog2δ] at h1
    linarith
  have hε2T : ε ^ 2 ≤ ε ^ 2 * (n + 1) := le_mul_of_one_le_right (sq_nonneg _) (by linarith)
  have h180 : 2 * L ≤ 64 * (2 + √2) * (ε ^ 2 * (n + 1)) := by
    have h := mul_le_mul_of_nonneg_left hiii (by positivity : (0 : ℝ) ≤ 2 + √2)
    have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    push_cast at h
    linear_combination h + L * hs
  have hsqrt : √2 ≤ 1.4143 := by
    calc √2 ≤ √(1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 1.4143 := Real.sqrt_sq (by norm_num)
  have hX : 0 ≤ ε ^ 2 * (n + 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hsqrt hX
  have hfin : Fintype.card ι * L ≤ 20000 * (ε ^ 2 * (n + 1)) := by
    rw [hN] at hi
    push_cast at hi
    nlinarith [hi, hii, hε2T, h180, h1]
  rw [div_le_iff₀ (by positivity)]
  push_cast
  linarith

end COLT83
