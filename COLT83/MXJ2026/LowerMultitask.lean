/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.TwoPoint
public import COLT83.LeanMachineLearning.Run
public import COLT83.MXJ2026.MultitaskInstances

/-!
# The adaptive lower bound for multi-task bandits

On the multi-task action set with block sizes `dⱼ ≥ 2`, no identification algorithm — adaptive
or not — with budget `T ≤ S_d² / (20000 ε²)`, `S_d = ∑ⱼ √dⱼ`, can be `(ε, δ)`-PAC with
`δ < 2/5` (`le_of_isPAC_multitaskSet`).

The `∏ⱼ dⱼ` hard instances `mtParam d ε κ` are indexed by the arms `κ` of the set
(`COLT83/MXJ2026/MultitaskInstances.lean`). For a block `j`, the `dⱼ` instances obtained by
moving the position `κ j` inside the block are compared with the common alternative
`mtParam0 d ε κ j` through the two-point inequality
(`IsRun.abs_measureReal_sub_le_of_sum_le`), whose divergence term is `50 εⱼ²` times the expected
number of pulls of the coordinate; Cauchy–Schwarz over the block and the fact that the total
number of pulls is `T` then bound the average value of the block by
`(10 εⱼ / dⱼ) (1 + 5 εⱼ √(dⱼ T)) ≤ 5.36 εⱼ`. Summing over the blocks, the average value of the
recommendation is at most `5.36 ε`, while an `(ε, δ)`-PAC algorithm has expected value at least
`9 ε (1 - δ)` on every instance (`integral_simpleRegret_le_of_measureReal_le`).

Blueprint: `thm:lower_multitask`, `cor:lower_multitask_pac`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

/-- Cauchy–Schwarz: the sum of the square roots of `n` nonnegative numbers is at most the square
root of `n` times their sum. -/
lemma sum_sqrt_le_sqrt_card_mul_sum {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a, √(f a) ≤ √(Fintype.card α * ∑ a, f a) := by
  have hsum : 0 ≤ ∑ a, √(f a) := sum_nonneg fun a _ ↦ Real.sqrt_nonneg _
  rw [show ∑ a, √(f a) = √((∑ a, √(f a)) ^ 2) from (Real.sqrt_sq hsum).symm]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ : α ↦ (1 : ℝ)) fun a ↦ √(f a)
  have h1 : ∑ a : α, (1 : ℝ) * √(f a) = ∑ a, √(f a) := by simp
  have h2 : ∑ _a : α, (1 : ℝ) ^ 2 = (Fintype.card α : ℝ) := by
    simp [Finset.card_univ]
  have h3 : ∑ a : α, (√(f a)) ^ 2 = ∑ a, f a :=
    Finset.sum_congr rfl fun a _ ↦ Real.sq_sqrt (hf a)
  rwa [h1, h2, h3] at h

variable {m : ℕ} {d : Fin m → ℕ}

/-- **The adaptive lower bound for multi-task bandits** (blueprint `thm:lower_multitask`): an
identification algorithm on the multi-task set with block sizes `dⱼ ≥ 2` and budget
`T ≤ S_d² / (20000 ε²)` which is `(ε, δ)`-PAC has `δ ≥ 2/5`. -/
lemma le_of_isPAC_multitaskSet (hm : 0 < m) (hd : ∀ j, 2 ≤ d j) {ε δ : ℝ} (hε : 0 < ε) {T : ℕ}
    (A : IdentAlg (multitaskSet d) ℝ (multitaskSet d)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (multitaskSet d) A ε δ)
    (hbudget : (T : ℝ) ≤ mtSum d ^ 2 / (20000 * ε ^ 2)) :
    2 / 5 ≤ δ := by
  classical
  have hmk := hA.isMarkovKernel_output
  have hd0 : ∀ j, 0 < d j := fun j ↦ lt_of_lt_of_le two_pos (hd j)
  have hdR : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd0 j
  have hS : 0 < mtSum d := mtSum_pos hm hd0
  have hEps : ∀ j, 0 < mtEps d ε j := fun j ↦ by
    rw [mtEps]
    have : (0 : ℝ) < √(d j) := Real.sqrt_pos.2 (hdR j)
    positivity
  have hEps0 : ∀ j, 0 ≤ mtEps d ε j := fun j ↦ (hEps j).le
  -- the canonical runs of the instances and of the alternatives
  have hrun := fun κ ↦ hA.isRun_fixedBudgetRunMeasure
    (env := linearGaussianEnv (multitaskSet d) (mtParam d ε κ))
  have hrun0 := fun (κ : ∀ j, Fin (d j)) (j : Fin m) ↦ hA.isRun_fixedBudgetRunMeasure
    (env := linearGaussianEnv (multitaskSet d) (mtParam0 d ε κ j))
  obtain ⟨P, hP⟩ : ∃ P : (∀ j, Fin (d j)) →
      Measure ((ℕ → multitaskSet d × ℝ) × multitaskSet d),
      ∀ κ, P κ = A.fixedBudgetRunMeasure (linearGaussianEnv (multitaskSet d) (mtParam d ε κ)) T :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : (∀ j, Fin (d j)) → Fin m →
      Measure ((ℕ → multitaskSet d × ℝ) × multitaskSet d),
      ∀ κ j, Q κ j =
        A.fixedBudgetRunMeasure (linearGaussianEnv (multitaskSet d) (mtParam0 d ε κ j)) T :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hprobP : ∀ κ, IsProbabilityMeasure (P κ) := fun κ ↦ by rw [hP]; infer_instance
  have hprobQ : ∀ κ j, IsProbabilityMeasure (Q κ j) := fun κ j ↦ by rw [hQ]; infer_instance
  -- coordinates of a point of the multi-task set
  have hcoord : ∀ i : Σ j, Fin (d j),
      Continuous fun y : multitaskSet d ↦ (y : EuclideanSpace ℝ (Σ j, Fin (d j))) i :=
    fun i ↦ ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp continuous_subtype_val
  set Ev : ∀ j : Fin m, Fin (d j) → Set (multitaskSet d) :=
    fun j i ↦ {y | (y : EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ = 1} with hEv
  have hEvm : ∀ (j : Fin m) (i : Fin (d j)), MeasurableSet (Ev j i) := fun j i ↦
    (hcoord ⟨j, i⟩).measurable (measurableSet_singleton 1)
  have hEvm' : ∀ (j : Fin m) (i : Fin (d j)),
      MeasurableSet (Prod.snd ⁻¹' Ev j i :
        Set ((ℕ → multitaskSet d × ℝ) × multitaskSet d)) := fun j i ↦
    measurable_snd (hEvm j i)
  -- the indicator of `Ev j i` is the coordinate `⟨j, i⟩`
  have hind : ∀ (j : Fin m) (i : Fin (d j)) (y : multitaskSet d),
      Set.indicator (Ev j i) (fun _ ↦ (1 : ℝ)) y =
        (y : EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ := by
    intro j i y
    by_cases h : y ∈ Ev j i
    · rw [Set.indicator_of_mem h]
      exact (h : (y : EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ = 1).symm
    · rw [Set.indicator_of_notMem h]
      exact ((y.2.1 ⟨j, i⟩).resolve_right h).symm
  -- (A) the recommendation has exactly one nonzero coordinate in each block
  have hQsum : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m),
      ∑ i, (Q κ j).real (Prod.snd ⁻¹' Ev j i) = 1 := by
    intro κ j
    have := hprobQ κ j
    have hint : ∀ i : Fin (d j),
        Integrable (Set.indicator (Prod.snd ⁻¹' Ev j i) fun _ ↦ (1 : ℝ)) (Q κ j) :=
      fun i ↦ (integrable_const _).indicator (hEvm' j i)
    have hstep : ∀ i : Fin (d j), (Q κ j).real (Prod.snd ⁻¹' Ev j i) =
        ∫ ω, Set.indicator (Prod.snd ⁻¹' Ev j i) (fun _ ↦ (1 : ℝ)) ω ∂(Q κ j) := by
      intro i
      rw [integral_indicator_const _ (hEvm' j i)]
      simp [measureReal_def]
    simp_rw [hstep]
    rw [← integral_finsetSum _ fun i _ ↦ hint i]
    have hone : ∀ ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d,
        ∑ i, Set.indicator (Prod.snd ⁻¹' Ev j i) (fun _ ↦ (1 : ℝ)) ω = 1 := by
      intro ω
      have h1 : ∀ i : Fin (d j), Set.indicator (Prod.snd ⁻¹' Ev j i) (fun _ ↦ (1 : ℝ)) ω =
          (ω.2 : EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ := by
        intro i
        rw [← hind j i ω.2]
        by_cases h : ω.2 ∈ Ev j i
        · rw [Set.indicator_of_mem (show ω ∈ Prod.snd ⁻¹' Ev j i from h),
            Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem (show ω ∉ Prod.snd ⁻¹' Ev j i from h),
            Set.indicator_of_notMem h]
      simp_rw [h1]
      exact ω.2.2.2 j
    simp_rw [hone]
    simp
  -- (B) the expected number of pulls of the coordinates of a block sums to `T`
  have hmeasX : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m) (t : ℕ) (i : Σ j, Fin (d j)),
      Measurable fun ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d ↦
        ((IT.action t ω.1 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) i :=
    fun κ j t i ↦ (hcoord i).measurable.comp ((hrun0 κ j).isAlgEnvSeq.measurable_action t)
  have hintX : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m) (t : ℕ) (i : Σ j, Fin (d j)),
      Integrable (fun ω ↦ ((IT.action t ω.1 : multitaskSet d) :
        EuclideanSpace ℝ (Σ j, Fin (d j))) i) (Q κ j) := by
    intro κ j t i
    have := hprobQ κ j
    refine Integrable.of_bound (hmeasX κ j t i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rcases (IT.action t ω.1 : multitaskSet d).2.1 i with h | h <;> rw [h] <;> norm_num
  obtain ⟨Nb, hNb⟩ : ∃ Nb : (∀ j, Fin (d j)) → ∀ j : Fin m, Fin (d j) → ℝ, ∀ κ j i,
      Nb κ j i = ∑ t ∈ Finset.range T,
        ∫ ω, ((IT.action t ω.1 : multitaskSet d) :
          EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ ∂(Q κ j) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hNb0 : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m) (i : Fin (d j)), 0 ≤ Nb κ j i := by
    intro κ j i
    rw [hNb]
    refine Finset.sum_nonneg fun t _ ↦ integral_nonneg fun ω ↦ ?_
    rcases (IT.action t ω.1 : multitaskSet d).2.1 ⟨j, i⟩ with h | h <;> rw [h] <;> norm_num
  have hNbsum : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m), ∑ i, Nb κ j i = T := by
    intro κ j
    have := hprobQ κ j
    simp_rw [hNb]
    rw [Finset.sum_comm]
    have hrow : ∀ t ∈ Finset.range T,
        ∑ i, ∫ ω, ((IT.action t ω.1 : multitaskSet d) :
          EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ ∂(Q κ j) = 1 := by
      intro t _
      rw [← integral_finsetSum _ fun i _ ↦ hintX κ j t ⟨j, i⟩]
      have hb : ∀ ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d,
          ∑ i, ((IT.action t ω.1 : multitaskSet d) :
            EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ = 1 :=
        fun ω ↦ (IT.action t ω.1 : multitaskSet d).2.2 j
      simp_rw [hb]
      simp
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- (C) the two-point inequality for one coordinate of a block
  have hstepC : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m) (i : Fin (d j)),
      (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j i) ≤
        (Q κ j).real (Prod.snd ⁻¹' Ev j i) + 5 * mtEps d ε j * √(Nb κ j i) := by
    intro κ j i
    set κ' := Function.update κ j i with hκ'
    have hκ'j : κ' j = i := Function.update_self ..
    have hQeq : mtParam0 d ε κ' j = mtParam0 d ε κ j := mtParam0_update κ j i
    have hC : ∀ x ∈ multitaskSet d,
        ⟪x, mtParam0 d ε κ j - mtParam d ε κ'⟫ ^ 2 ≤ (10 * mtEps d ε j) ^ 2 := by
      intro x hx
      rw [← hQeq, inner_mtParam0_sub_mtParam, hκ'j]
      rcases hx.1 ⟨j, i⟩ with h | h <;> rw [h] <;> nlinarith [hEps0 j]
    have hK : ∑ t ∈ Finset.range T,
        ∫ ω, ⟪((IT.action t ω.1 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))),
          mtParam0 d ε κ j - mtParam d ε κ'⟫ ^ 2 / 2 ∂(Q κ j) ≤
        50 * mtEps d ε j ^ 2 * Nb κ j i := by
      have hpt : ∀ (t : ℕ) (ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d),
          ⟪((IT.action t ω.1 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))),
            mtParam0 d ε κ j - mtParam d ε κ'⟫ ^ 2 / 2 =
            50 * mtEps d ε j ^ 2 * ((IT.action t ω.1 : multitaskSet d) :
              EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, i⟩ := by
        intro t ω
        rw [← hQeq, inner_mtParam0_sub_mtParam, hκ'j]
        rcases (IT.action t ω.1 : multitaskSet d).2.1 ⟨j, i⟩ with h | h <;> rw [h] <;> ring
      simp_rw [hpt]
      rw [hNb]
      simp_rw [integral_const_mul]
      rw [← Finset.mul_sum]
    rw [hQ κ j] at hK
    have h2 := IsRun.abs_measureReal_sub_le_of_sum_le hC hK hA (hrun0 κ j) (hrun κ') (hEvm j i)
    have hsq : √(50 * mtEps d ε j ^ 2 * Nb κ j i / 2) = 5 * mtEps d ε j * √(Nb κ j i) := by
      have h5 : (0 : ℝ) ≤ 5 * mtEps d ε j := mul_nonneg (by norm_num) (hEps0 j)
      rw [show 50 * mtEps d ε j ^ 2 * Nb κ j i / 2 = (5 * mtEps d ε j) ^ 2 * Nb κ j i by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h5]
    rw [hsq] at h2
    rw [hP κ', hQ κ j]
    linarith [(abs_le.1 h2).1]
  -- (D) the average over a block
  have hstepD : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m),
      ∑ i, (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j i) ≤
        1 + 5 * mtEps d ε j * √(d j * T) := by
    intro κ j
    have hcs : ∑ i, √(Nb κ j i) ≤ √((d j : ℝ) * T) := by
      calc ∑ i, √(Nb κ j i) ≤ √(Fintype.card (Fin (d j)) * ∑ i, Nb κ j i) :=
            sum_sqrt_le_sqrt_card_mul_sum _ fun i ↦ hNb0 κ j i
        _ = √((d j : ℝ) * T) := by rw [Fintype.card_fin, hNbsum κ j]
    calc ∑ i, (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j i)
        ≤ ∑ i, ((Q κ j).real (Prod.snd ⁻¹' Ev j i) + 5 * mtEps d ε j * √(Nb κ j i)) :=
          Finset.sum_le_sum fun i _ ↦ hstepC κ j i
      _ = 1 + 5 * mtEps d ε j * ∑ i, √(Nb κ j i) := by
          rw [Finset.sum_add_distrib, hQsum κ j, ← Finset.mul_sum]
      _ ≤ 1 + 5 * mtEps d ε j * √((d j : ℝ) * T) := by
          have h5 : (0 : ℝ) ≤ 5 * mtEps d ε j := mul_nonneg (by norm_num) (hEps0 j)
          nlinarith [hcs]
  -- (E) the average over the instances
  have hprupd : ∀ (κ : ∀ j, Fin (d j)) (j : Fin m) (i : Fin (d j)),
      (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j (Function.update κ j i j)) =
        (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j i) := by
    intro κ j i
    rw [Function.update_self]
  have hsumE : ∀ j : Fin m, (d j : ℝ) * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j)) ≤
      (Fintype.card (∀ j, Fin (d j)) : ℝ) * (1 + 5 * mtEps d ε j * √((d j : ℝ) * T)) := by
    intro j
    have h1 := Fintype.sum_sum_update (β := fun j ↦ Fin (d j)) j
      fun κ ↦ (P κ).real (Prod.snd ⁻¹' Ev j (κ j))
    rw [Fintype.card_fin] at h1
    rw [← h1]
    calc ∑ κ : ∀ j, Fin (d j), ∑ i, (P (Function.update κ j i)).real
            (Prod.snd ⁻¹' Ev j (Function.update κ j i j))
        = ∑ κ : ∀ j, Fin (d j), ∑ i, (P (Function.update κ j i)).real (Prod.snd ⁻¹' Ev j i) :=
          Finset.sum_congr rfl fun κ _ ↦ Finset.sum_congr rfl fun i _ ↦ hprupd κ j i
      _ ≤ ∑ _κ : ∀ j, Fin (d j), (1 + 5 * mtEps d ε j * √((d j : ℝ) * T)) :=
          Finset.sum_le_sum fun κ _ ↦ hstepD κ j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- (F) the expected value of the recommendation
  obtain ⟨Val, hVal⟩ : ∃ Val : (∀ j, Fin (d j)) → ℝ, ∀ κ,
      Val κ = ∫ ω, ⟪((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))),
        mtParam d ε κ⟫ ∂(P κ) := ⟨_, fun _ ↦ rfl⟩
  have hValeq : ∀ κ, Val κ = ∑ j, 10 * mtEps d ε j * (P κ).real (Prod.snd ⁻¹' Ev j (κ j)) := by
    intro κ
    have := hprobP κ
    rw [hVal]
    have hpt : ∀ ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d,
        ⟪((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))), mtParam d ε κ⟫ =
          ∑ j, Set.indicator (Prod.snd ⁻¹' Ev j (κ j)) (fun _ ↦ 10 * mtEps d ε j) ω := by
      intro ω
      rw [inner_mtParam]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases h : ω.2 ∈ Ev j (κ j)
      · rw [Set.indicator_of_mem (show ω ∈ Prod.snd ⁻¹' Ev j (κ j) from h),
          show ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) ⟨j, κ j⟩ = 1 from h,
          mul_one]
      · rw [Set.indicator_of_notMem (show ω ∉ Prod.snd ⁻¹' Ev j (κ j) from h),
          (ω.2.2.1 ⟨j, κ j⟩).resolve_right h, mul_zero]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ ↦ (integrable_const _).indicator (hEvm' j (κ j))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_indicator_const _ (hEvm' j (κ j))]
    simp [measureReal_def, mul_comm]
  -- (G) the budget assumption, as a bound on `ε √T`
  have hsqrtT : ε * √T ≤ 0.0072 * mtSum d := by
    have h1 : (T : ℝ) ≤ (0.0072 * mtSum d / ε) ^ 2 := by
      refine hbudget.trans ?_
      rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (mtSum d)) (sq_nonneg ε)]
    have h2 : √T ≤ 0.0072 * mtSum d / ε := by
      rw [show (0.0072 * mtSum d / ε) = √((0.0072 * mtSum d / ε) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt h1
    rw [le_div_iff₀ hε] at h2
    linarith
  have hkey : ∀ j, mtEps d ε j * √((d j : ℝ) * T) ≤ 0.0072 * d j := by
    intro j
    have h1 : √((d j : ℝ) * T) = √(d j) * √T := Real.sqrt_mul (hdR j).le _
    have h2 : √(d j) * √(d j) = (d j : ℝ) := Real.mul_self_sqrt (hdR j).le
    rw [mtEps, h1, div_mul_eq_mul_div, div_le_iff₀ hS]
    have h3 : ε * √(d j) * (√(d j) * √T) = ε * √T * (d j : ℝ) := by
      linear_combination (ε * √T) * h2
    rw [h3]
    have h4 : ε * √T * (d j : ℝ) ≤ 0.0072 * mtSum d * (d j : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrtT (hdR j).le
    linarith
  have hterm : ∀ j, 10 * mtEps d ε j * (1 + 5 * mtEps d ε j * √((d j : ℝ) * T)) ≤
      5.36 * mtEps d ε j * (d j : ℝ) := by
    intro j
    have h1 := hkey j
    have h2 : (2 : ℝ) ≤ d j := by exact_mod_cast hd j
    have h3 : 0 ≤ mtEps d ε j := hEps0 j
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 50) h3),
      mul_nonneg h3 (by linarith : (0 : ℝ) ≤ (d j : ℝ) - 2)]
  -- (H) the PAC guarantee, as a lower bound on the expected value
  have hnorm : ∀ x ∈ multitaskSet d, ‖x‖ ≤ √m := fun _ hx ↦ norm_le_of_mem_multitaskSet hx
  have hPACval : ∀ κ, 9 * ε - 9 * ε * δ ≤ Val κ := by
    intro κ
    have := hprobP κ
    have hsup : supportFn (multitaskSet d) (mtParam d ε κ) = 10 * ε :=
      supportFn_mtParam hm hd0 hε.le κ
    have hsr : ∀ y : EuclideanSpace ℝ (Σ j, Fin (d j)),
        simpleRegret (multitaskSet d) (mtParam d ε κ) y = 10 * ε - ⟪y, mtParam d ε κ⟫ := by
      intro y
      rw [show simpleRegret (multitaskSet d) (mtParam d ε κ) y =
        supportFn (multitaskSet d) (mtParam d ε κ) - ⟪y, mtParam d ε κ⟫ from rfl, hsup]
    have h0 : ∀ y ∈ multitaskSet d, 0 ≤ simpleRegret (multitaskSet d) (mtParam d ε κ) y := by
      intro y hy
      rw [hsr, ← hsup]
      linarith [inner_le_supportFn hnorm hy (mtParam d ε κ)]
    have hZ : ∀ y ∈ multitaskSet d, simpleRegret (multitaskSet d) (mtParam d ε κ) y ≤ 10 * ε := by
      intro y hy
      rw [hsr]
      linarith [inner_mtParam_nonneg hε.le κ hy]
    have hpacs : 1 - δ ≤ (P κ).real {ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d |
        simpleRegret (multitaskSet d) (mtParam d ε κ)
          ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) ≤ ε} := by
      rw [hP κ]
      exact hpac (mtParam d ε κ) _ _ _ _ (hrun κ)
    have hint := integral_simpleRegret_le_of_measureReal_le (P := P κ) measurable_snd h0 hZ
      (by linarith) hpacs
    have hmeasR : Measurable fun ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d ↦
        simpleRegret (multitaskSet d) (mtParam d ε κ)
          ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) :=
      ((continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable).comp
        measurable_snd
    have hintR : Integrable (fun ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d ↦
        simpleRegret (multitaskSet d) (mtParam d ε κ)
          ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j)))) (P κ) :=
      Integrable.of_bound hmeasR.aestronglyMeasurable (10 * ε)
        (Filter.Eventually.of_forall fun ω ↦ by
          rw [Real.norm_of_nonneg (h0 _ (ω.2).2)]
          exact hZ _ (ω.2).2)
    have hVal2 : Val κ = 10 * ε - ∫ ω, simpleRegret (multitaskSet d) (mtParam d ε κ)
        ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) ∂(P κ) := by
      rw [hVal]
      have hpt : ∀ ω : (ℕ → multitaskSet d × ℝ) × multitaskSet d,
          ⟪((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))), mtParam d ε κ⟫ =
            10 * ε - simpleRegret (multitaskSet d) (mtParam d ε κ)
              ((ω.2 : multitaskSet d) : EuclideanSpace ℝ (Σ j, Fin (d j))) := fun ω ↦ by
        rw [hsr]; ring
      simp_rw [hpt]
      rw [integral_sub (integrable_const _) hintR]
      simp
    rw [hVal2]
    linarith [hint]
  -- (I) combining the two bounds on the average value
  have hNpos : (0 : ℝ) < Fintype.card (∀ j, Fin (d j)) := by
    have : Nonempty (∀ j, Fin (d j)) := ⟨fun j ↦ ⟨0, hd0 j⟩⟩
    exact_mod_cast Fintype.card_pos
  have hj : ∀ j : Fin m, 10 * mtEps d ε j * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j)) ≤
      (Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * mtEps d ε j) := by
    intro j
    have h1 := hsumE j
    have h3 : (0 : ℝ) ≤ 10 * mtEps d ε j := mul_nonneg (by norm_num) (hEps0 j)
    refine le_of_mul_le_mul_left ?_ (hdR j)
    calc (d j : ℝ) * (10 * mtEps d ε j * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j)))
        = 10 * mtEps d ε j * ((d j : ℝ) * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j))) := by ring
      _ ≤ 10 * mtEps d ε j * ((Fintype.card (∀ j, Fin (d j)) : ℝ) *
            (1 + 5 * mtEps d ε j * √((d j : ℝ) * T))) := mul_le_mul_of_nonneg_left h1 h3
      _ = (Fintype.card (∀ j, Fin (d j)) : ℝ) *
            (10 * mtEps d ε j * (1 + 5 * mtEps d ε j * √((d j : ℝ) * T))) := by ring
      _ ≤ (Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * mtEps d ε j * (d j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hterm j) hNpos.le
      _ = (d j : ℝ) * ((Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * mtEps d ε j)) := by ring
  have hhigh : ∑ κ, Val κ ≤ (Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * ε) := by
    have h1 : ∑ κ, Val κ =
        ∑ j, 10 * mtEps d ε j * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j)) := by
      simp_rw [hValeq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
    rw [h1]
    calc ∑ j, 10 * mtEps d ε j * ∑ κ, (P κ).real (Prod.snd ⁻¹' Ev j (κ j))
        ≤ ∑ j, (Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * mtEps d ε j) :=
          Finset.sum_le_sum fun j _ ↦ hj j
      _ = (Fintype.card (∀ j, Fin (d j)) : ℝ) * (5.36 * ε) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, sum_mtEps hm hd0]
  have hlow : (Fintype.card (∀ j, Fin (d j)) : ℝ) * (9 * ε - 9 * ε * δ) ≤ ∑ κ, Val κ := by
    calc (Fintype.card (∀ j, Fin (d j)) : ℝ) * (9 * ε - 9 * ε * δ)
        = ∑ _κ : ∀ j, Fin (d j), (9 * ε - 9 * ε * δ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ κ, Val κ := Finset.sum_le_sum fun κ _ ↦ hPACval κ
  have hfin : 9 * ε - 9 * ε * δ ≤ 5.36 * ε := le_of_mul_le_mul_left (hlow.trans hhigh) hNpos
  by_contra hcon
  push Not at hcon
  linarith [mul_pos hε (sub_pos.2 hcon)]

end COLT83
