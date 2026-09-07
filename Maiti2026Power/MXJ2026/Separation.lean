/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.LinearBandit
public import Maiti2026Power.MXJ2026.StructuredSets
public import Maiti2026Power.MXJ2026.Width
public import Maiti2026Power.MXJ2026.BlockBall
public import Maiti2026Power.MXJ2026.WidthBall
public import Maiti2026Power.MXJ2026.LowerNonadaptive
public import Maiti2026Power.MXJ2026.LowerAdaptive
public import Maiti2026Power.LeanMachineLearning.FixedDesignTransport
public import Maiti2026Power.MXJ2026.BlockProof

/-!
# Polynomial separation between adaptive and non-adaptive algorithms (Theorem 7)

On the block-ball set `𝒳 ⊆ ℝ^{kd}` (the union of the unit balls of `k` coordinate blocks of
dimension `d`):

* every fixed-design `(ε, δ)`-PAC algorithm with `δ ≤ 1/10` has budget `T ≥ k d² / (210 ε²)`
  (`blockBallSet_le_budget_of_isFixedDesign_of_isPAC`), and every `(ε, δ)`-PAC algorithm with
  `δ < 1/16` has budget `T ≥ kd log(1/δ) / (20000 ε²)` (`blockBallSet_le_budget_of_isPAC`,
  from Theorem 2);
* there is an adaptive `(ε, δ)`-PAC algorithm with budget
  `T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²` (`exists_isPAC_blockBallSet`).

For `d ≤ k` the adaptive budget is `O(kd (log(1/δ) + log k) / ε²)`, polynomially smaller than the
non-adaptive `Ω(kd log(1/δ) / ε² + kd² / ε²)`.

The non-adaptive lower bound restricts the design to a block `i` receiving at most `T / k`
design points (pigeonhole, `exists_mul_card_blockRounds_le`): the projected design `π_i x_t` on
the unit ball of `ℝ^d`, with the recommendation of `A` projected on block `i`, is `(ε, δ)`-PAC
on the unit ball (`isPAC_fixedDesignTransport_blockProjBall`, from the transport lemma
`isPAC_fixedDesignTransport`: the observations under `ι_i ϑ` and under `ϑ` coincide and the
simple regrets agree, `simpleRegret_blockBallSet_blockEmb`). Its design matrix `M` is positive
definite (`posDef_of_isFixedDesign_of_isPAC_of_zero_mem`), the Bayesian step of Theorem 3 gives
`0.12 w(ball, M) ≤ ε` (`gwMat_le_of_isFixedDesign_of_isPAC`), and
`w(ball, M) ≥ √(2/π) d / √(tr M)` with `tr M ≤ T / k` (`le_gwMat_unitBall`,
`trace_sum_outerSelf_blockDesign_le`).

Blueprint: `thm:separation_lower_nonadaptive`, `thm:separation` (stated there for an explicit block
algorithm, of which `exists_isPAC_blockBallSet` is the existence form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit Finset
open scoped RealInnerProductSpace

namespace Maiti2026Power

/-- **Restriction of a fixed design to a block** (blueprint `lem:block_restriction`): if the
fixed-design algorithm `A` with design `x` is `(ε, δ)`-PAC on the block-ball set, the projected
design `blockDesign i x` on the unit ball of `ℝ^d`, with the recommendation of `A` projected on
block `i`, is `(ε, δ)`-PAC on the unit ball. -/
lemma isPAC_fixedDesignTransport_blockProjBall {k d T : ℕ}
    {A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d)} [IsMarkovKernel (A.output T)]
    (hA : A.IsFixedBudget T) {x : ℕ → blockBallSet k d} (hx : A.alg = fixedDesignAlg x)
    {ε δ : ℝ} (hpac : IsPAC (blockBallSet k d) A ε δ) (i : Fin k) :
    IsPAC (unitBall (Fin d))
      (fixedDesignTransport A T x (blockDesign i x) (measurable_blockProjBall i)) ε δ :=
  isPAC_fixedDesignTransport hA hx hpac (blockEmb i)
    (fun _ ϑ ↦ (inner_blockEmb_right i _ ϑ).symm) (measurable_blockProjBall i)
    (fun ϑ y ↦ (simpleRegret_blockBallSet_blockEmb i ϑ y).symm.le)

/-- **Theorem 7, non-adaptive lower bound**: a fixed-design (non-adaptive) identification
algorithm which is `(ε, δ)`-PAC on the block-ball set of `ℝ^{kd}`, with `ε ∈ (0, 1]` and
`δ ≤ 1/10`, has budget `T ≥ k d² / (210 ε²)`. -/
theorem blockBallSet_le_budget_of_isFixedDesign_of_isPAC (k d : ℕ) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioc 0 (1 / 10)) {T : ℕ}
    (A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d)) (hA : A.IsFixedBudget T)
    (hdes : A.IsFixedDesign)
    (hpac : IsPAC (blockBallSet k d) A ε δ) :
    k * (d : ℝ) ^ 2 / (210 * ε ^ 2) ≤ T := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hε0 : 0 < ε := hε.1
  obtain ⟨x, hx⟩ := hdes
  have := hA.isMarkovKernel_output
  -- pigeonhole: some block receives at most `T / k` rounds
  obtain ⟨i, hi⟩ := exists_mul_card_blockRounds_le hk x T
  -- the transported algorithm on the unit ball of `ℝ^d` is PAC
  have hpac' := isPAC_fixedDesignTransport_blockProjBall hA hx hpac i
  -- its design matrix is positive definite
  set M := ∑ t : Fin T, outerSelf (blockDesign i x t : EuclideanSpace ℝ (Fin d)) with hM_def
  have hS : M.PosDef :=
    posDef_of_isFixedDesign_of_isPAC_of_zero_mem isCompact_unitBall span_unitBall
      zero_mem_unitBall hε0 (hδ.2.trans_lt (by norm_num)) _ isFixedBudget_fixedDesignTransport
      alg_fixedDesignTransport hpac'
  -- the Bayesian step and the width of the unit ball
  have hw := gwMat_le_of_isFixedDesign_of_isPAC isCompact_unitBall unitBall_nonempty hε0.le hδ _
    isFixedBudget_fixedDesignTransport alg_fixedDesignTransport hpac' hS
  have hlow := le_gwMat_unitBall hS
  -- the trace of the design matrix is at most the number of rounds in block `i`
  have htr : M.trace ≤ (blockRounds i x T).card := trace_sum_outerSelf_blockDesign_le i x
  have htr0 : 0 < M.trace := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact hS.trace_pos
  have hcard : (0 : ℝ) < (blockRounds i x T).card := htr0.trans_le htr
  -- arithmetic
  set n : ℝ := ((blockRounds i x T).card : ℝ) with hn_def
  set w := gwMat (unitBall (Fin d)) M with hw_def
  have h1 : √(2 / π) * d / √n ≤ w := by
    refine le_trans ?_ hlow
    rw [Fintype.card_fin]
    gcongr
  have h2 : 0.12 * (√(2 / π) * d) ≤ ε * √n := by
    have hn : 0 < √n := Real.sqrt_pos.2 hcard
    rw [div_le_iff₀ hn] at h1
    calc 0.12 * (√(2 / π) * d) ≤ 0.12 * (w * √n) := by gcongr
      _ = (0.12 * w) * √n := by ring
      _ ≤ ε * √n := by gcongr
  have h3 : (0.12 * (√(2 / π) * d)) ^ 2 ≤ (ε * √n) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  simp only [mul_pow] at h3
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hcard.le] at h3
  have hπ4 : 1 / 2 ≤ 2 / π := by
    rw [div_le_div_iff₀ (by norm_num) Real.pi_pos]
    have := Real.pi_le_four
    linarith
  have h4 : (d : ℝ) ^ 2 ≤ 210 * ε ^ 2 * n := by
    have hd2 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have h5 := mul_le_mul_of_nonneg_right hπ4 hd2
    have h6 : 0 ≤ ε ^ 2 * n := by positivity
    norm_num at h3
    linarith
  have h5 : (k : ℝ) * n ≤ T := by
    rw [hn_def]
    exact_mod_cast hi
  rw [div_le_iff₀ (by positivity)]
  calc (k : ℝ) * d ^ 2 ≤ k * (210 * ε ^ 2 * n) := by gcongr
    _ = 210 * ε ^ 2 * (k * n) := by ring
    _ ≤ 210 * ε ^ 2 * T := by gcongr
    _ = T * (210 * ε ^ 2) := by ring

/-- **Theorem 7, adaptive lower bound** (from Theorem 2): an identification algorithm which is
`(ε, δ)`-PAC on the block-ball set of `ℝ^{kd}`, `kd ≥ 2`, with `δ < 1/16`, has budget
`T ≥ kd log(1/δ) / (20000 ε²)`. -/
theorem blockBallSet_le_budget_of_isPAC (k d : ℕ) (hkd : 2 ≤ k * d) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioo 0 (1 / 16)) {T : ℕ}
    (A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (blockBallSet k d) A ε δ) :
    k * d * log (1 / δ) / (20000 * ε ^ 2) ≤ T := by
  have hcard : Fintype.card (Fin k × Fin d) = k * d := by simp [Fintype.card_prod]
  have := le_budget_of_isPAC (blockBallSet k d) isCompact_blockBallSet span_blockBallSet
    (hcard ▸ hkd) hε hδ A hA hpac
  rw [hcard] at this
  push_cast at this
  exact this

/-- **Theorem 7, adaptive upper bound**: for `k ≥ 1`, `ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is an
(adaptive) `(ε, δ)`-PAC identification algorithm on the block-ball set of `ℝ^{kd}` with budget
`T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²`. -/
theorem exists_isPAC_blockBallSet (k d : ℕ) (hk : 1 ≤ k) {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 2000000 * (k * d * log (8 * k / δ) + (d : ℝ) ^ 2) / ε ^ 2 ∧
      ∃ A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d), A.IsFixedBudget T ∧
        IsPAC (blockBallSet k d) A ε δ := by
  classical
  let Q : BlockParam := ⟨k, hk, ε, δ, hε, hδ⟩
  have hgood : ∀ θ : EuclideanSpace ℝ (Fin k × Fin d),
      MeasurableSet {x : blockBallSet k d | simpleRegret (blockBallSet k d) θ x ≤ ε} := fun θ ↦
    measurableSet_le (measurable_const.sub (measurable_subtype_coe.inner measurable_const))
      measurable_const
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- degenerate case `d = 0`: every reward vector is `0` and every recommendation is optimal
    refine ⟨0, by simp, IdentAlg.fixedBudget (Q.alg 0).toAlgorithm 0
      (Kernel.deterministic (fun _ ↦ Q.zeroBB 0) measurable_const),
      IdentAlg.isFixedBudget_fixedBudget _ _ _, ?_⟩
    refine SeededAlg.linearBandit_isPAC_fixedBudget_deterministic (Q.alg 0) measurable_const hgood
      fun θ ↦ ?_
    have hθ : θ = 0 := by
      ext p
      exact isEmptyElim p
    have huniv : {ω : ℕ → (Fin 0 → Bool) × ℝ |
        simpleRegret (blockBallSet k 0) θ (Q.zeroBB 0) ≤ ε} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ by
        have : Nonempty (blockBallSet k 0) := (blockBallSet_nonempty ⟨0, hk⟩).to_subtype
        simp [simpleRegret, hθ, hε.1.le]
    rw [huniv, probReal_univ]
    linarith [hδ.1]
  · refine ⟨Q.T d, Q.T_le hd, IdentAlg.fixedBudget (Q.alg d).toAlgorithm (Q.T d)
      (Kernel.deterministic (Q.output d) Q.measurable_output),
      IdentAlg.isFixedBudget_fixedBudget _ _ _, ?_⟩
    exact SeededAlg.linearBandit_isPAC_fixedBudget_deterministic (Q.alg d) Q.measurable_output
      hgood fun θ ↦ Q.one_sub_le_seedMeasure_real_output hd θ

end Maiti2026Power
