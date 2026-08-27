/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.TwoPoint
public import COLT83.LeanMachineLearning.Run
public import COLT83.Mathlib.Data.Finset.PowersetCardSum
public import COLT83.MXJ2026.MSetInstances

/-!
# The adaptive lower bound for the `m`-sets

On the `m`-sets of `ℝ^d` with `n = d - m + 1 ≥ 20 m`, no identification algorithm — adaptive or
not — with budget `T ≤ m n / (2500 ε²)` can be `(ε, δ)`-PAC with `δ < 2/9`
(`le_of_isPAC_mSet`).

The hard instances are the `C(d, m)` vectors `msParam Δ S = Δ ⬝ 1_S`, `|S| = m`, `Δ = 10 ε / m`.
For an alternative `B` of size `m - 1`, a counting (Markov) argument shows that at least `n / 2`
of the `n` coordinates outside `B` are pulled at most `4 m T / n` times in expectation and are
recommended with probability at most `4 m / n` under `θ^(B)`
(`le_card_goodSet`); on those coordinates the two-point inequality
(`IsRun.abs_measureReal_sub_le_of_sum_le`) bounds the probability of recommending `i` under
`θ^(B ∪ {i})` by `0.4`, so the average over `i ∉ B` is at most `0.7`. Reindexing the pairs
`(S, i)`, `i ∈ S`, as the pairs `(B, i)`, `i ∉ B`
(`Finset.sum_powersetCard_succ_sum_mem`), the average value of the recommendation is at most
`7 ε`, while an `(ε, δ)`-PAC algorithm has expected value at least `9 ε (1 - δ)` on every
instance.

Blueprint: `lem:msets_good_set`, `lem:msets_pinsker_step`, `lem:msets_equivalent_sampling`,
`thm:lower_msets`, `cor:lower_msets_pac`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The adaptive lower bound for the `m`-sets** (blueprint `thm:lower_msets`): an
identification algorithm on the `m`-sets of `ℝ^d`, `m = k + 1`, `d = k + n` with `n ≥ 20 m`,
with budget `1 ≤ T ≤ m n / (2500 ε²)` which is `(ε, δ)`-PAC has `δ ≥ 2/9`. -/
lemma le_of_isPAC_mSet {k n m : ℕ} (hm_def : m = k + 1) (hn : Fintype.card ι = k + n)
    (hk : 20 * m ≤ n) {ε δ : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg (mSet ι m) ℝ (mSet ι m)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (mSet ι m) A ε δ)
    (hbudget : (T : ℝ) ≤ m * n / (2500 * ε ^ 2)) :
    2 / 9 ≤ δ := by
  classical
  have hmk := hA.isMarkovKernel_output
  have hmR : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmd : m ≤ Fintype.card ι := by omega
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set Δ : ℝ := 10 * ε / m with hΔ_def
  have hΔ : 0 < Δ := by rw [hΔ_def]; positivity
  have hΔm : Δ * m = 10 * ε := by rw [hΔ_def]; field_simp
  -- the canonical runs
  have hrun := fun S : Finset ι ↦ hA.isRun_fixedBudgetRunMeasure
    (env := linearGaussianEnv (mSet ι m) (msParam Δ S))
  obtain ⟨P, hP⟩ : ∃ P : Finset ι → Measure ((ℕ → mSet ι m × ℝ) × mSet ι m),
      ∀ S, P S = A.fixedBudgetRunMeasure (linearGaussianEnv (mSet ι m) (msParam Δ S)) T :=
    ⟨_, fun _ ↦ rfl⟩
  have hprob : ∀ S, IsProbabilityMeasure (P S) := fun S ↦ by rw [hP]; infer_instance
  -- the events "the coordinate `i` of the recommendation is `1`"
  have hcoord : ∀ i : ι, Continuous fun y : mSet ι m ↦ (y : EuclideanSpace ℝ ι) i :=
    fun i ↦ ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp continuous_subtype_val
  set Aset : ι → Set (mSet ι m) := fun i ↦ {y | (y : EuclideanSpace ℝ ι) i = 1} with hAset
  have hAm : ∀ i, MeasurableSet (Aset i) := fun i ↦
    (hcoord i).measurable (measurableSet_singleton 1)
  have hAm' : ∀ i, MeasurableSet (Prod.snd ⁻¹' Aset i :
      Set ((ℕ → mSet ι m × ℝ) × mSet ι m)) := fun i ↦ measurable_snd (hAm i)
  have hind : ∀ (i : ι) (y : mSet ι m),
      Set.indicator (Aset i) (fun _ ↦ (1 : ℝ)) y = (y : EuclideanSpace ℝ ι) i := by
    intro i y
    by_cases h : y ∈ Aset i
    · rw [Set.indicator_of_mem h]
      exact (h : (y : EuclideanSpace ℝ ι) i = 1).symm
    · rw [Set.indicator_of_notMem h]
      exact ((y.2.1 i).resolve_right h).symm
  obtain ⟨pr, hpr⟩ : ∃ pr : Finset ι → ι → ℝ, ∀ S i,
      pr S i = (P S).real (Prod.snd ⁻¹' Aset i) := ⟨_, fun _ _ ↦ rfl⟩
  have hpr0 : ∀ S i, 0 ≤ pr S i := fun S i ↦ by rw [hpr]; exact measureReal_nonneg
  have hpr1 : ∀ S i, pr S i ≤ 1 := fun S i ↦ by
    have := hprob S
    rw [hpr]
    exact measureReal_le_one
  -- (1) the recommendation has exactly `m` coordinates equal to `1`
  have hprsum : ∀ S, ∑ i, pr S i = m := by
    intro S
    have := hprob S
    have hstep : ∀ i, pr S i = ∫ ω, Set.indicator (Prod.snd ⁻¹' Aset i) (fun _ ↦ (1 : ℝ)) ω
        ∂(P S) := by
      intro i
      rw [hpr, integral_indicator_const _ (hAm' i)]
      simp [measureReal_def]
    simp_rw [hstep]
    rw [← integral_finsetSum _ fun i _ ↦ (integrable_const _).indicator (hAm' i)]
    have hone : ∀ ω : (ℕ → mSet ι m × ℝ) × mSet ι m,
        ∑ i, Set.indicator (Prod.snd ⁻¹' Aset i) (fun _ ↦ (1 : ℝ)) ω = m := by
      intro ω
      have h1 : ∀ i, Set.indicator (Prod.snd ⁻¹' Aset i) (fun _ ↦ (1 : ℝ)) ω =
          (ω.2 : EuclideanSpace ℝ ι) i := by
        intro i
        rw [← hind i ω.2]
        by_cases h : ω.2 ∈ Aset i
        · rw [Set.indicator_of_mem (show ω ∈ Prod.snd ⁻¹' Aset i from h),
            Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem (show ω ∉ Prod.snd ⁻¹' Aset i from h),
            Set.indicator_of_notMem h]
      simp_rw [h1]
      exact ω.2.2.2
    simp_rw [hone]
    simp
  -- (2) the total number of pulls is `m T`
  have hmeasX : ∀ (S : Finset ι) (t : ℕ) (i : ι),
      Measurable fun ω : (ℕ → mSet ι m × ℝ) × mSet ι m ↦
        ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i :=
    fun S t i ↦ (hcoord i).measurable.comp ((hrun S).isAlgEnvSeq.measurable_action t)
  have hintX : ∀ (S : Finset ι) (t : ℕ) (i : ι),
      Integrable (fun ω ↦ ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i) (P S) := by
    intro S t i
    have := hprob S
    refine Integrable.of_bound (hmeasX S t i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rcases (IT.action t ω.1 : mSet ι m).2.1 i with h | h <;> rw [h] <;> norm_num
  obtain ⟨Nb, hNb⟩ : ∃ Nb : Finset ι → ι → ℝ, ∀ S i, Nb S i = ∑ t ∈ Finset.range T,
      ∫ ω, ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i ∂(P S) := ⟨_, fun _ _ ↦ rfl⟩
  have hNb0 : ∀ S i, 0 ≤ Nb S i := by
    intro S i
    rw [hNb]
    refine Finset.sum_nonneg fun t _ ↦ integral_nonneg fun ω ↦ ?_
    rcases (IT.action t ω.1 : mSet ι m).2.1 i with h | h <;> rw [h] <;> norm_num
  have hNbsum : ∀ S, ∑ i, Nb S i = m * T := by
    intro S
    have := hprob S
    simp_rw [hNb]
    rw [Finset.sum_comm]
    have hrow : ∀ t ∈ Finset.range T,
        ∑ i, ∫ ω, ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i ∂(P S) = m := by
      intro t _
      rw [← integral_finsetSum _ fun i _ ↦ hintX S t i]
      have hb : ∀ ω : (ℕ → mSet ι m × ℝ) × mSet ι m,
          ∑ i, ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i = m :=
        fun ω ↦ (IT.action t ω.1 : mSet ι m).2.2
      simp_rw [hb]
      simp
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  -- (3) the good coordinates of an alternative
  have hTpos : (0 : ℝ) < T := by linarith
  set G : Finset ι → Finset ι := fun B ↦
    Bᶜ.filter fun i ↦ Nb B i ≤ 4 * m * T / n ∧ pr B i ≤ 4 * m / n with hG
  have hcardG : ∀ B : Finset ι, B.card = k → (n : ℝ) / 2 ≤ (G B).card := by
    intro B hB
    have hcompl : Bᶜ.card = n := by rw [Finset.card_compl, hB, hn]; omega
    set C1 := Bᶜ.filter fun i ↦ ¬ Nb B i ≤ 4 * m * T / n with hC1
    set C2 := Bᶜ.filter fun i ↦ ¬ pr B i ≤ 4 * m / n with hC2
    have hsub : Bᶜ ⊆ G B ∪ (C1 ∪ C2) := by
      intro i hi
      by_cases h1 : Nb B i ≤ 4 * m * T / n
      · by_cases h2 : pr B i ≤ 4 * m / n
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, h1, h2⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hi, h2⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, h1⟩))
    have hC1card : (C1.card : ℝ) ≤ n / 4 := by
      have hge : (C1.card : ℝ) * (4 * m * T / n) ≤ ∑ i ∈ C1, Nb B i := by
        calc (C1.card : ℝ) * (4 * m * T / n) = ∑ _i ∈ C1, (4 * (m : ℝ) * T / n) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ C1, Nb B i :=
              Finset.sum_le_sum fun i hi ↦ le_of_lt (not_le.1 (Finset.mem_filter.1 hi).2)
      have hle : ∑ i ∈ C1, Nb B i ≤ m * T := by
        calc ∑ i ∈ C1, Nb B i ≤ ∑ i, Nb B i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hNb0 B i
          _ = m * T := hNbsum B
      have h := hge.trans hle
      rw [mul_div_assoc', div_le_iff₀ hnR] at h
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [h, mul_pos hmR hTpos]
    have hC2card : (C2.card : ℝ) ≤ n / 4 := by
      have hge : (C2.card : ℝ) * (4 * m / n) ≤ ∑ i ∈ C2, pr B i := by
        calc (C2.card : ℝ) * (4 * (m : ℝ) / n) = ∑ _i ∈ C2, (4 * (m : ℝ) / n) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ C2, pr B i :=
              Finset.sum_le_sum fun i hi ↦ le_of_lt (not_le.1 (Finset.mem_filter.1 hi).2)
      have hle : ∑ i ∈ C2, pr B i ≤ m := by
        calc ∑ i ∈ C2, pr B i ≤ ∑ i, pr B i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hpr0 B i
          _ = m := hprsum B
      have h := hge.trans hle
      rw [mul_div_assoc', div_le_iff₀ hnR] at h
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [h, hmR]
    have hcards : (n : ℝ) ≤ (G B).card + C1.card + C2.card := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (G B) (C1 ∪ C2)
      have h3 := Finset.card_union_le C1 C2
      rw [hcompl] at h1
      have : n ≤ (G B).card + C1.card + C2.card := by omega
      exact_mod_cast this
    linarith
  -- (4) the two-point inequality for one coordinate outside the alternative
  have hstepC : ∀ (B : Finset ι) (i : ι), i ∉ B →
      pr (insert i B) i ≤ pr B i + Δ / 2 * √(Nb B i) := by
    intro B i hi
    have hC : ∀ x ∈ mSet ι m, ⟪x, msParam Δ B - msParam Δ (insert i B)⟫ ^ 2 ≤ Δ ^ 2 := by
      intro x hx
      rw [inner_msParam_sub_insert Δ hi]
      rcases hx.1 i with h | h <;> rw [h] <;> nlinarith [hΔ.le]
    have hK : ∑ t ∈ Finset.range T,
        ∫ ω, ⟪((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι),
          msParam Δ B - msParam Δ (insert i B)⟫ ^ 2 / 2 ∂(P B) ≤ Δ ^ 2 / 2 * Nb B i := by
      have hpt : ∀ (t : ℕ) (ω : (ℕ → mSet ι m × ℝ) × mSet ι m),
          ⟪((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι),
            msParam Δ B - msParam Δ (insert i B)⟫ ^ 2 / 2 =
            Δ ^ 2 / 2 * ((IT.action t ω.1 : mSet ι m) : EuclideanSpace ℝ ι) i := by
        intro t ω
        rw [inner_msParam_sub_insert Δ hi]
        rcases (IT.action t ω.1 : mSet ι m).2.1 i with h | h <;> rw [h] <;> ring
      simp_rw [hpt]
      rw [hNb]
      simp_rw [integral_const_mul]
      rw [← Finset.mul_sum]
    rw [hP B] at hK
    have h2 := IsRun.abs_measureReal_sub_le_of_sum_le hC hK hA (hrun B) (hrun (insert i B))
      (hAm i)
    have hsq : √(Δ ^ 2 / 2 * Nb B i / 2) = Δ / 2 * √(Nb B i) := by
      rw [show Δ ^ 2 / 2 * Nb B i / 2 = (Δ / 2) ^ 2 * Nb B i by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hsq] at h2
    rw [hpr, hpr, hP B, hP (insert i B)]
    linarith [(abs_le.1 h2).1]
  -- (5) the average over the coordinates outside the alternative
  have hmn : 4 * (m : ℝ) / n ≤ 0.2 := by
    rw [div_le_iff₀ hnR]
    have : (20 * m : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have hΔbnd : Δ * √((m : ℝ) * T / n) ≤ 0.2 := by
    have hT2 : (T : ℝ) * (2500 * ε ^ 2) ≤ m * n := (le_div_iff₀ (by positivity)).1 hbudget
    have h1 : Δ ^ 2 * ((m : ℝ) * T / n) ≤ 0.04 := by
      have key : (10 * ε / m) ^ 2 * ((m : ℝ) * T / n) = 100 * ε ^ 2 * T / (m * n) := by
        field_simp
        ring
      rw [hΔ_def, key, div_le_iff₀ (by positivity)]
      nlinarith [hT2]
    calc Δ * √((m : ℝ) * T / n) = √(Δ ^ 2 * ((m : ℝ) * T / n)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΔ.le]
      _ ≤ √0.04 := Real.sqrt_le_sqrt h1
      _ = 0.2 := by rw [show (0.04 : ℝ) = 0.2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hgood : ∀ (B : Finset ι) (i : ι), i ∈ G B → pr (insert i B) i ≤ 0.4 := by
    intro B i hiG
    have hmem := Finset.mem_filter.1 hiG
    have hi : i ∉ B := Finset.mem_compl.1 hmem.1
    have h1 := hstepC B i hi
    have h2 : Δ / 2 * √(Nb B i) ≤ Δ / 2 * √(4 * (m : ℝ) * T / n) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmem.2.1) (by positivity)
    have h3 : √(4 * (m : ℝ) * T / n) = 2 * √((m : ℝ) * T / n) := by
      rw [show 4 * (m : ℝ) * T / n = 2 ^ 2 * ((m : ℝ) * T / n) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h3, show Δ / 2 * (2 * √((m : ℝ) * T / n)) = Δ * √((m : ℝ) * T / n) by ring] at h2
    linarith [hmem.2.2, hmn, hΔbnd]
  have hstepD : ∀ B : Finset ι, B.card = k → ∑ i ∈ Bᶜ, pr (insert i B) i ≤ 0.7 * n := by
    intro B hB
    have hcompl : Bᶜ.card = n := by rw [Finset.card_compl, hB, hn]; omega
    have hGsub : G B ⊆ Bᶜ := Finset.filter_subset _ _
    have h1 : ∑ i ∈ G B, pr (insert i B) i ≤ 0.4 * (G B).card := by
      calc ∑ i ∈ G B, pr (insert i B) i ≤ ∑ _i ∈ G B, (0.4 : ℝ) :=
            Finset.sum_le_sum fun i hi ↦ hgood B i hi
        _ = 0.4 * (G B).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h2 : ∑ i ∈ Bᶜ \ G B, pr (insert i B) i ≤ ((Bᶜ \ G B).card : ℝ) := by
      calc ∑ i ∈ Bᶜ \ G B, pr (insert i B) i ≤ ∑ _i ∈ Bᶜ \ G B, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ hpr1 _ _
        _ = ((Bᶜ \ G B).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard2 : ((Bᶜ \ G B).card : ℝ) = n - (G B).card := by
      have h := Finset.card_sdiff_add_card_eq_card hGsub
      rw [hcompl] at h
      have h' : ((Bᶜ \ G B).card : ℝ) + (G B).card = n := by exact_mod_cast h
      linarith
    have hGn := hcardG B hB
    rw [← Finset.sum_sdiff hGsub]
    linarith
  -- (6) the expected value of the recommendation
  obtain ⟨Val, hVal⟩ : ∃ Val : Finset ι → ℝ, ∀ S,
      Val S = ∫ ω, ⟪((ω.2 : mSet ι m) : EuclideanSpace ℝ ι), msParam Δ S⟫ ∂(P S) :=
    ⟨_, fun _ ↦ rfl⟩
  have hValeq : ∀ S, Val S = Δ * ∑ i ∈ S, pr S i := by
    intro S
    have := hprob S
    rw [hVal]
    have hpt : ∀ ω : (ℕ → mSet ι m × ℝ) × mSet ι m,
        ⟪((ω.2 : mSet ι m) : EuclideanSpace ℝ ι), msParam Δ S⟫ =
          ∑ i ∈ S, Set.indicator (Prod.snd ⁻¹' Aset i) (fun _ ↦ Δ) ω := by
      intro ω
      rw [inner_msParam, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases h : ω.2 ∈ Aset i
      · rw [Set.indicator_of_mem (show ω ∈ Prod.snd ⁻¹' Aset i from h),
          show ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι) i = 1 from h, mul_one]
      · rw [Set.indicator_of_notMem (show ω ∉ Prod.snd ⁻¹' Aset i from h),
          (ω.2.2.1 i).resolve_right h, mul_zero]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ ↦ (integrable_const _).indicator (hAm' i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_indicator_const _ (hAm' i), hpr]
    simp [measureReal_def, mul_comm]
  -- (7) the PAC guarantee
  have hPACval : ∀ S : Finset ι, S.card = m → 9 * ε - 9 * ε * δ ≤ Val S := by
    intro S hS
    have := hprob S
    have hsup : supportFn (mSet ι m) (msParam Δ S) = 10 * ε := by
      rw [supportFn_msParam hΔ.le hS hmd, hΔm]
    have hsr : ∀ y : EuclideanSpace ℝ ι,
        simpleRegret (mSet ι m) (msParam Δ S) y = 10 * ε - ⟪y, msParam Δ S⟫ := by
      intro y
      rw [show simpleRegret (mSet ι m) (msParam Δ S) y =
        supportFn (mSet ι m) (msParam Δ S) - ⟪y, msParam Δ S⟫ from rfl, hsup]
    have h0 : ∀ y ∈ mSet ι m, 0 ≤ simpleRegret (mSet ι m) (msParam Δ S) y := by
      intro y hy
      rw [hsr, ← hsup]
      linarith [inner_le_supportFn (fun x hx ↦ norm_le_of_mem_mSet hx) hy (msParam Δ S)]
    have hZ : ∀ y ∈ mSet ι m, simpleRegret (mSet ι m) (msParam Δ S) y ≤ 10 * ε := by
      intro y hy
      rw [hsr]
      linarith [inner_msParam_nonneg hΔ.le S hy]
    have hpacs : 1 - δ ≤ (P S).real {ω : (ℕ → mSet ι m × ℝ) × mSet ι m |
        simpleRegret (mSet ι m) (msParam Δ S)
          ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι) ≤ ε} := by
      rw [hP S]
      exact hpac (msParam Δ S) _ _ _ _ (hrun S)
    have hint := integral_simpleRegret_le_of_measureReal_le (P := P S) measurable_snd h0 hZ
      (by linarith) hpacs
    have hmeasR : Measurable fun ω : (ℕ → mSet ι m × ℝ) × mSet ι m ↦
        simpleRegret (mSet ι m) (msParam Δ S)
          ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι) :=
      ((continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable).comp
        measurable_snd
    have hintR : Integrable (fun ω : (ℕ → mSet ι m × ℝ) × mSet ι m ↦
        simpleRegret (mSet ι m) (msParam Δ S)
          ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι)) (P S) :=
      Integrable.of_bound hmeasR.aestronglyMeasurable (10 * ε)
        (Filter.Eventually.of_forall fun ω ↦ by
          rw [Real.norm_of_nonneg (h0 _ (ω.2).2)]
          exact hZ _ (ω.2).2)
    have hVal2 : Val S = 10 * ε - ∫ ω, simpleRegret (mSet ι m) (msParam Δ S)
        ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι) ∂(P S) := by
      rw [hVal]
      have hpt : ∀ ω : (ℕ → mSet ι m × ℝ) × mSet ι m,
          ⟪((ω.2 : mSet ι m) : EuclideanSpace ℝ ι), msParam Δ S⟫ =
            10 * ε - simpleRegret (mSet ι m) (msParam Δ S)
              ((ω.2 : mSet ι m) : EuclideanSpace ℝ ι) := fun ω ↦ by rw [hsr]; ring
      simp_rw [hpt]
      rw [integral_sub (integrable_const _) hintR]
      simp
    rw [hVal2]
    linarith [hint]
  -- (8) combining the two bounds on the average value
  have hDpos : 0 < (Fintype.card ι).choose m := Nat.choose_pos hmd
  have hDR : (0 : ℝ) < (Fintype.card ι).choose m := by exact_mod_cast hDpos
  have hchoose : ((Fintype.card ι).choose m : ℝ) * m = ((Fintype.card ι).choose k : ℝ) * n := by
    have h := Nat.choose_succ_right_eq (Fintype.card ι) k
    have hcard : Fintype.card ι - k = n := by omega
    rw [hcard, ← hm_def] at h
    exact_mod_cast h
  have hhigh : ∑ S ∈ Finset.powersetCard m univ, Val S ≤
      Δ * (0.7 * n) * ((Fintype.card ι).choose k : ℝ) := by
    have h1 : ∑ S ∈ Finset.powersetCard m univ, Val S =
        Δ * ∑ S ∈ Finset.powersetCard m univ, ∑ i ∈ S, pr S i := by
      simp_rw [hValeq]
      rw [Finset.mul_sum]
    have h2 : ∑ S ∈ Finset.powersetCard m univ, ∑ i ∈ S, pr S i =
        ∑ B ∈ Finset.powersetCard k univ, ∑ i ∈ Bᶜ, pr (insert i B) i := by
      rw [hm_def, ← Finset.sum_powersetCard_succ_sum_mem k fun B i ↦ pr (insert i B) i]
      refine Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.insert_erase hi]
    rw [h1, h2]
    calc Δ * ∑ B ∈ Finset.powersetCard k univ, ∑ i ∈ Bᶜ, pr (insert i B) i
        ≤ Δ * ∑ _B ∈ Finset.powersetCard k (univ : Finset ι), (0.7 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun B hB ↦ hstepD B (Finset.mem_powersetCard.1 hB).2) hΔ.le
      _ = Δ * (0.7 * n) * ((Fintype.card ι).choose k : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
          ring
  have hlow : ((Fintype.card ι).choose m : ℝ) * (9 * ε - 9 * ε * δ) ≤
      ∑ S ∈ Finset.powersetCard m univ, Val S := by
    calc ((Fintype.card ι).choose m : ℝ) * (9 * ε - 9 * ε * δ)
        = ∑ _S ∈ Finset.powersetCard m (univ : Finset ι), (9 * ε - 9 * ε * δ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun S hS ↦ hPACval S (Finset.mem_powersetCard.1 hS).2
  have hprod : Δ * (0.7 * n) * ((Fintype.card ι).choose k : ℝ) =
      7 * ε * ((Fintype.card ι).choose m : ℝ) := by
    calc Δ * (0.7 * n) * ((Fintype.card ι).choose k : ℝ)
        = 0.7 * Δ * (((Fintype.card ι).choose k : ℝ) * n) := by ring
      _ = 0.7 * Δ * (((Fintype.card ι).choose m : ℝ) * m) := by rw [hchoose]
      _ = 0.7 * ((Fintype.card ι).choose m : ℝ) * (Δ * m) := by ring
      _ = 0.7 * ((Fintype.card ι).choose m : ℝ) * (10 * ε) := by rw [hΔm]
      _ = 7 * ε * ((Fintype.card ι).choose m : ℝ) := by ring
  have hcomb := hlow.trans hhigh
  rw [hprod] at hcomb
  have hfin : 9 * ε - 9 * ε * δ ≤ 7 * ε :=
    le_of_mul_le_mul_right (by linarith) hDR
  by_contra hcon
  push Not at hcon
  linarith [mul_pos hε (sub_pos.2 hcon)]

end COLT83
