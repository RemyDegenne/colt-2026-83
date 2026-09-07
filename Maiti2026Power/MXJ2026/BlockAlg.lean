/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.NormEstProof
public import Maiti2026Power.MXJ2026.BlockBall

/-!
# The adaptive block algorithm on the block-ball set (Theorem 7, upper bound)

The block algorithm (blueprint `def:block_algorithm`) with parameters `ε ∈ (0, 1]`, `δ ∈ (0, 1)`
on the block-ball set of `ℝ^{k × d}`:

* phase 1 (rounds `t < k N`): for each block `i < k`, the rounds `[i N, (i + 1) N)` run the
  norm-estimation meta-algorithm `NormEst (ε/4, δ/(2k))` (budget `N`) on block `i`, that is,
  every action of the meta-algorithm is embedded on block `i`; the estimate `r̂ i` of `‖θ^(i)‖`
  is computed from the observations of these rounds;
* phase 2 (rounds `k N ≤ t < k N + d n₂`): on the block `î` maximizing `r̂ i`, play each basis
  vector `n₂` times, and recommend `ι_î (ϑ̂ / ‖ϑ̂‖)` where `ϑ̂` is the vector of empirical means.

It is a seeded algorithm (`BlockParam.alg`) with the same seeds as the meta-algorithm (uniform
Boolean vectors, one per round), with a deterministic output `BlockParam.output`.
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning
open scoped RealInnerProductSpace

namespace Maiti2026Power

variable {k d : ℕ}

/-- Embedding of an action of the unit ball of `ℝ^d` on block `i` of the block-ball set. -/
noncomputable def blockEmbBall (i : Fin k) (x : unitBall (Fin d)) : blockBallSet k d :=
  ⟨blockEmb i x, blockEmb_mem_blockBallSet (mem_unitBall_iff.1 x.2) i⟩

@[simp]
lemma coe_blockEmbBall (i : Fin k) (x : unitBall (Fin d)) :
    (blockEmbBall i x : EuclideanSpace ℝ (Fin k × Fin d)) = blockEmb i x := rfl

lemma blockProjBall_blockEmbBall (i : Fin k) (x : unitBall (Fin d)) :
    blockProjBall i (blockEmbBall i x) = x :=
  Subtype.ext (by rw [coe_blockProjBall, coe_blockEmbBall, blockProj_blockEmb_same])

lemma measurable_blockEmbBall (i : Fin k) : Measurable (blockEmbBall (d := d) i) :=
  ((continuous_blockEmb i).measurable.comp measurable_subtype_coe).subtype_mk

variable {ι : Type*} [Fintype ι]

/-- Normalization to the unit ball: `‖v‖⁻¹ • v` (which is `0` if `v = 0`). -/
noncomputable def normalizeBall (v : EuclideanSpace ℝ ι) : unitBall ι :=
  ⟨‖v‖⁻¹ • v, by
    rw [mem_unitBall_iff, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]⟩

@[simp]
lemma coe_normalizeBall (v : EuclideanSpace ℝ ι) :
    (normalizeBall v : EuclideanSpace ℝ ι) = ‖v‖⁻¹ • v := rfl

lemma measurable_normalizeBall : Measurable (normalizeBall (ι := ι)) :=
  (measurable_norm.inv.smul measurable_id).subtype_mk

/-- Parameters of the block algorithm: the number of blocks `k ≥ 1`, the accuracy `ε ∈ (0, 1]`
and the confidence `δ ∈ (0, 1)`. -/
structure BlockParam where
  /-- The number of blocks. -/
  k : ℕ
  hk : 0 < k
  /-- The accuracy. -/
  ε : ℝ
  /-- The confidence. -/
  δ : ℝ
  hε : ε ∈ Set.Ioc 0 1
  hδ : δ ∈ Set.Ioo 0 1

namespace BlockParam

variable (Q : BlockParam)

/-- The parameters `(ε/4, δ/(2k))` of the norm estimator run on each block. -/
noncomputable def P : NormEstParam where
  ε := Q.ε / 4
  δ := Q.δ / (2 * Q.k)
  hε := ⟨by have := Q.hε.1; positivity, by have := Q.hε.2; linarith⟩
  hδ := ⟨by have := Q.hδ.1; have := Q.hk; positivity, by
    have h1 := Q.hδ.2
    have h2 : (1 : ℝ) ≤ Q.k := Nat.one_le_cast.2 Q.hk
    rw [div_lt_one (by positivity)]
    linarith⟩

lemma P_ε : Q.P.ε = Q.ε / 4 := rfl
lemma P_δ : Q.P.δ = Q.δ / (2 * Q.k) := rfl

/-- The number of rounds of the norm estimator on one block. -/
noncomputable def N (d : ℕ) : ℕ := Q.P.T (Fin d)

/-- The number of repetitions of each basis vector in the second phase. -/
noncomputable def n₂ (d : ℕ) : ℕ := ⌈4 * (8 * d + 48 * log (2 / Q.δ)) / Q.ε ^ 2⌉₊

/-- The start of the second phase. -/
noncomputable def T₂ (d : ℕ) : ℕ := Q.k * Q.N d

/-- The total budget. -/
noncomputable def T (d : ℕ) : ℕ := Q.T₂ d + d * Q.n₂ d

lemma log_two_div_pos : 0 < log (2 / Q.δ) := by
  have := Q.hδ
  exact Real.log_pos (by rw [lt_div_iff₀ this.1]; linarith [this.2])

lemma n₂_pos : 0 < Q.n₂ d := by
  have := Q.log_two_div_pos
  have := Q.hε.1
  exact Nat.ceil_pos.2 (by positivity)

/-- The block of a round `t < k N`. -/
noncomputable def blockOf (d : ℕ) (t : ℕ) : Fin Q.k := ⟨t / Q.N d % Q.k, Nat.mod_lt _ Q.hk⟩

/-- The basis vector played at round `t` of the second phase, if any. -/
noncomputable def basisRound (d : ℕ) (t : ℕ) : Option (Fin d) :=
  if h : Q.T₂ d ≤ t ∧ t - Q.T₂ d < d * Q.n₂ d then
    some ((Fintype.equivFin (Fin d)).symm ⟨(t - Q.T₂ d) / Q.n₂ d, by
      rw [Fintype.card_fin]
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h.2)⟩)
  else none

/-- The zero action. -/
noncomputable def zeroBB (d : ℕ) : blockBallSet Q.k d := blockEmbBall ⟨0, Q.hk⟩ unitBallZero

/-! ### Statistics of an observation sequence -/

/-- The estimate of the norm of block `m` (for `m < k`), computed by the meta-algorithm from the
observations of the rounds `[m N, (m + 1) N)`. -/
noncomputable def estN (d : ℕ) (m : ℕ) (y : ℕ → ℝ) : ℝ :=
  Q.P.estimate (Fin d) fun r ↦ y (m * Q.N d + r)

lemma measurable_estN (m : ℕ) : Measurable (Q.estN d m) :=
  (Q.P.measurable_estimate).comp (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)

lemma exists_argmax (d : ℕ) (y : ℕ → ℝ) :
    ∃ m, m < Q.k ∧ ∀ j < Q.k, Q.estN d j y ≤ Q.estN d m y := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range Q.k) (fun m ↦ Q.estN d m y)
    ⟨0, mem_range.2 Q.hk⟩
  exact ⟨m, mem_range.1 hm, fun j hj ↦ hmax j (mem_range.2 hj)⟩

open Classical in
/-- The selected block: the smallest index maximizing the estimated norm. -/
noncomputable def iHat (d : ℕ) (y : ℕ → ℝ) : Fin Q.k :=
  ⟨Nat.find (Q.exists_argmax d y), (Nat.find_spec (Q.exists_argmax d y)).1⟩

lemma estN_le_iHat (y : ℕ → ℝ) (j : Fin Q.k) : Q.estN d j y ≤ Q.estN d (Q.iHat d y) y :=
  (Nat.find_spec (Q.exists_argmax d y)).2 j j.2

lemma iHat_congr {y y' : ℕ → ℝ} (h : ∀ m < Q.k, Q.estN d m y = Q.estN d m y') :
    Q.iHat d y = Q.iHat d y' := by
  unfold iHat
  refine Fin.ext (Nat.find_congr' fun {m} ↦ ?_)
  constructor
  · rintro ⟨hm, hj⟩
    exact ⟨hm, fun j hjk ↦ by rw [← h j hjk, ← h m hm]; exact hj j hjk⟩
  · rintro ⟨hm, hj⟩
    exact ⟨hm, fun j hjk ↦ by rw [h j hjk, h m hm]; exact hj j hjk⟩

open Classical in
lemma measurable_iHat : Measurable (Q.iHat d) := by
  have hp : ∀ n, MeasurableSet {y : ℕ → ℝ | n < Q.k ∧ ∀ j < Q.k, Q.estN d j y ≤ Q.estN d n y} := by
    intro n
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ measurableSet_le (Q.measurable_estN j) (Q.measurable_estN n))
  have hfind : Measurable fun y : ℕ → ℝ ↦ Nat.find (Q.exists_argmax d y) :=
    Measurable.find (f := fun n (_ : ℕ → ℝ) ↦ n)
      (p := fun n y ↦ n < Q.k ∧ ∀ j < Q.k, Q.estN d j y ≤ Q.estN d n y) (fun _ ↦ measurable_const)
      hp (Q.exists_argmax d)
  refine measurable_to_countable' fun i ↦ ?_
  have : Q.iHat d ⁻¹' {i} = (fun y ↦ Nat.find (Q.exists_argmax d y)) ⁻¹' {(i : ℕ)} := by
    ext y
    simp [iHat, Fin.ext_iff]
  rw [this]
  exact hfind (measurableSet_singleton _)

/-- The vector of empirical means of the second phase. -/
noncomputable def thetaHat (d : ℕ) (y : ℕ → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun m ↦
    (∑ ℓ : Fin (Q.n₂ d), y (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)) / Q.n₂ d

lemma measurable_thetaHat : Measurable (Q.thetaHat d) := by
  unfold thetaHat
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun m ↦ ?_)
  refine (Finset.measurable_sum _ fun ℓ _ ↦ ?_).div_const _
  exact measurable_pi_apply (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)

/-- The recommendation: the normalized empirical mean vector, embedded on the selected block. -/
noncomputable def recommend (d : ℕ) (y : ℕ → ℝ) : blockBallSet Q.k d :=
  blockEmbBall (Q.iHat d y) (normalizeBall (Q.thetaHat d y))

lemma measurable_recommend : Measurable (Q.recommend d) := by
  have h : Measurable fun p : Fin Q.k × (ℕ → ℝ) ↦
      blockEmbBall p.1 (normalizeBall (Q.thetaHat d p.2)) :=
    measurable_from_prod_countable_right fun i ↦
      (measurable_blockEmbBall i).comp (measurable_normalizeBall.comp (Q.measurable_thetaHat))
  exact h.comp ((Q.measurable_iHat).prodMk measurable_id)

/-! ### The seeded algorithm -/

/-- The past actions of block `i` in a history of rounds `0..n`, extended by `0`. -/
noncomputable def pastOfBlock (d : ℕ) (i : Fin Q.k) {n : ℕ}
    (h : Iic n → blockBallSet Q.k d × ℝ) : ℕ → unitBall (Fin d) :=
  fun r ↦ if hr : i * Q.N d + r ∈ Iic n then blockProjBall i (h ⟨i * Q.N d + r, hr⟩).1
    else unitBallZero

/-- The observations of block `i` in a history of rounds `0..n`, extended by `0`. -/
noncomputable def yOfBlock (d : ℕ) (i : Fin Q.k) {n : ℕ} (h : Iic n → blockBallSet Q.k d × ℝ) :
    ℕ → ℝ :=
  fun r ↦ if hr : i * Q.N d + r ∈ Iic n then (h ⟨i * Q.N d + r, hr⟩).2 else 0

lemma measurable_pastOfBlock_apply (i : Fin Q.k) {n : ℕ} (r : ℕ) :
    Measurable fun h : Iic n → blockBallSet Q.k d × ℝ ↦ Q.pastOfBlock d i h r := by
  unfold pastOfBlock
  split_ifs
  exacts [(measurable_blockProjBall i).comp (measurable_pi_apply _).fst, measurable_const]

lemma measurable_yOfBlock (i : Fin Q.k) {n : ℕ} :
    Measurable fun h : Iic n → blockBallSet Q.k d × ℝ ↦ Q.yOfBlock d i h := by
  refine measurable_pi_lambda _ fun r ↦ ?_
  unfold yOfBlock
  split_ifs
  exacts [(measurable_pi_apply _).snd, measurable_const]

/-- The action of round `t` computed from the history of rounds `0..n` and the fresh seed `u`:
in phase 1, the action of the meta-algorithm of the block of `t` embedded on that block; in
phase 2, the basis vector of the round on the selected block. -/
noncomputable def nextAction (d : ℕ) (t : ℕ) {n : ℕ} (h : Iic n → blockBallSet Q.k d × ℝ)
    (u : Fin d → Bool) : blockBallSet Q.k d :=
  if t < Q.T₂ d then
    blockEmbBall (Q.blockOf d t) (Q.P.nextAction (t % Q.N d) (Q.pastOfBlock d (Q.blockOf d t) h)
      (Q.P.jStar (Fin d) (Q.yOfBlock d (Q.blockOf d t) h)) u)
  else match Q.basisRound d t with
    | some m => blockEmbBall (Q.iHat d (NormEstParam.yOfIic h))
        ⟨EuclideanSpace.single m 1, single_mem_unitBall m⟩
    | none => Q.zeroBB d

lemma measurable_nextAction (t : ℕ) {n : ℕ} :
    Measurable fun p : (Iic n → blockBallSet Q.k d × ℝ) × (Fin d → Bool) ↦
      Q.nextAction d t p.1 p.2 := by
  unfold nextAction
  split_ifs with ht
  · have h1 : Measurable fun q : ℕ × ((Iic n → blockBallSet Q.k d × ℝ) × (Fin d → Bool)) ↦
        Q.P.nextAction (t % Q.N d) (Q.pastOfBlock d (Q.blockOf d t) q.2.1) q.1 q.2.2 :=
      measurable_from_prod_countable_right fun js ↦
        Q.P.measurable_nextAction_of (t % Q.N d) js (Q.measurable_pastOfBlock_apply (Q.blockOf d t))
    have h2 : Measurable fun p : (Iic n → blockBallSet Q.k d × ℝ) × (Fin d → Bool) ↦
        (Q.P.jStar (Fin d) (Q.yOfBlock d (Q.blockOf d t) p.1), p) :=
      ((Q.P.measurable_jStar).comp ((Q.measurable_yOfBlock (Q.blockOf d t)).comp
        measurable_fst)).prodMk measurable_id
    exact (measurable_blockEmbBall _).comp (h1.comp h2)
  · rcases Q.basisRound d t with _ | m
    · exact measurable_const
    · exact (measurable_of_countable fun i : Fin Q.k ↦
        blockEmbBall i ⟨EuclideanSpace.single m 1, single_mem_unitBall m⟩).comp
        ((Q.measurable_iHat).comp ((NormEstParam.measurable_yOfIic n).comp measurable_fst))

/-- The block algorithm as a seeded algorithm on the block-ball set, with uniform Boolean seeds. -/
noncomputable def alg (d : ℕ) : SeededAlg (blockBallSet Q.k d) ℝ (Fin d → Bool) where
  seed := uniformBoolVec (Fin d)
  act0 u := blockEmbBall ⟨0, Q.hk⟩ ((Q.P.alg (Fin d)).act0 u)
  measurable_act0 := (measurable_blockEmbBall _).comp (Q.P.alg (Fin d)).measurable_act0
  next n h u := Q.nextAction d (n + 1) h u
  measurable_next n := Q.measurable_nextAction (n + 1)

/-- The deterministic output: the recommendation computed from the observations of the
history of the `T` rounds. -/
noncomputable def output (d : ℕ) (h : Fin (Q.T d) → blockBallSet Q.k d × ℝ) : blockBallSet Q.k d :=
  Q.recommend d (NormEstParam.yOf h)

lemma measurable_output : Measurable (Q.output d) :=
  (Q.measurable_recommend).comp (NormEstParam.measurable_yOf _)

end BlockParam

end Maiti2026Power
