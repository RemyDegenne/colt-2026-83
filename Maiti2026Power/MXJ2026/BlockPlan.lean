/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.BlockAlg

/-!
# The run of the block algorithm on the seed space

On the product space of seeds and noises, the run of the block algorithm on block `i` is the
run of the norm-estimation meta-algorithm against the reward vector `θ^(i)` on the shifted
seed sequence (`seedStep_block`), and in the second phase the actions are the basis vectors on
the selected block (`seedAction_of_T₂_le`). Consequently the estimates of the blocks are the
estimates of the meta-algorithm (`estN_eq`) and the vector of empirical means is
`θ^(î) + Δ` with `Δ` the noise average of the basis window (`thetaHat_eq`).
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning
open scoped RealInnerProductSpace

namespace Maiti2026Power

/-- The shift of a sequence. -/
def shiftSeq {α : Type*} (a : ℕ) (ω : ℕ → α) : ℕ → α := fun t ↦ ω (a + t)

lemma measurable_shiftSeq {α : Type*} [MeasurableSpace α] (a : ℕ) :
    Measurable (shiftSeq (α := α) a) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

variable {ι : Type*} [Fintype ι]

/-- The seed measure is shift-invariant. -/
lemma nsMeasure_map_shiftSeq (a : ℕ) : (nsMeasure ι).map (shiftSeq a) = nsMeasure ι :=
  Measure.infinitePi_map_eval_comp' _ (add_right_injective a)

lemma nsMeasure_real_shiftSeq_preimage (a : ℕ) {S : Set (ℕ → (ι → Bool) × ℝ)}
    (hS : MeasurableSet S) : (nsMeasure ι).real (shiftSeq a ⁻¹' S) = (nsMeasure ι).real S := by
  rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_shiftSeq a) hS,
    nsMeasure_map_shiftSeq]

namespace BlockParam

variable {d : ℕ} (Q : BlockParam)

/-- The noise function of the linear Gaussian bandit on the block-ball set. -/
noncomputable abbrev F (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) : blockBallSet Q.k d → ℝ → ℝ :=
  LinearBandit.linearNoise (blockBallSet Q.k d) θ

lemma F_blockEmbBall (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (i : Fin Q.k) (x : unitBall (Fin d))
    (e : ℝ) : Q.F θ (blockEmbBall i x) e = NormEstParam.F (blockProj i θ) x e := by
  simp only [F, NormEstParam.F, LinearBandit.linearNoise, coe_blockEmbBall, inner_blockEmb_left]

/-- The observation sequence of the run on the seed space. -/
noncomputable def yω (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (ω : ℕ → (Fin d → Bool) × ℝ) :
    ℕ → ℝ :=
  fun t ↦ (Q.alg d).seedFeedback (Q.F θ) t ω

lemma measurable_yω (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) : Measurable (Q.yω θ) :=
  measurable_pi_lambda _ fun t ↦
    (SeededAlg.measurable_seedStep (LinearBandit.measurable_uncurry_linearNoise _ θ) t).snd

lemma N_pos (hd : 0 < d) : 0 < Q.N d := by
  have h := Q.P.T₁_pos (ι := Fin d) (by simpa using hd)
  unfold N
  rw [NormEstParam.T_eq]
  omega

lemma T₂_pos (hd : 0 < d) : 0 < Q.T₂ d := Nat.mul_pos Q.hk (Q.N_pos hd)

lemma block_round_lt (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) : i * Q.N d + t < Q.T₂ d := by
  have h1 : (i : ℕ) + 1 ≤ Q.k := i.2
  calc i * Q.N d + t < i * Q.N d + Q.N d := by omega
    _ = ((i : ℕ) + 1) * Q.N d := by ring
    _ ≤ Q.k * Q.N d := Nat.mul_le_mul_right _ h1

lemma blockOf_eq (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) : Q.blockOf d (i * Q.N d + t) = i := by
  have hN : 0 < Q.N d := by omega
  ext
  simp only [blockOf]
  rw [show (i : ℕ) * Q.N d + t = t + Q.N d * i by ring, Nat.add_mul_div_left _ _ hN,
    Nat.div_eq_of_lt ht, zero_add, Nat.mod_eq_of_lt i.2]

lemma block_round_mod (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) : (i * Q.N d + t) % Q.N d = t := by
  rw [show (i : ℕ) * Q.N d + t = t + Q.N d * i by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ht]

lemma nextAction_of_lt (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) {n : ℕ}
    (h : Fin n → blockBallSet Q.k d × ℝ) (u : Fin d → Bool) :
    Q.nextAction d (i * Q.N d + t) h u = blockEmbBall i (Q.P.nextAction t (Q.pastOfBlock d i h)
      (Q.P.jStar (Fin d) (Q.yOfBlock d i h)) u) := by
  unfold nextAction
  rw [ite_eq_left (Q.block_round_lt i ht), Q.blockOf_eq i ht, Q.block_round_mod i ht]

/-- **The block algorithm simulates the meta-algorithm on each block**: the step of round
`i N + t`, `t < N`, of the run on the seed space is the step of round `t` of the meta-algorithm
against `θ^(i)` on the seed sequence shifted by `i N`, embedded on block `i`. -/
theorem seedStep_block (θ : EuclideanSpace ℝ (Fin Q.k × Fin d))
    (ω : ℕ → (Fin d → Bool) × ℝ) (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) :
    (Q.alg d).seedStep (Q.F θ) (i * Q.N d + t) ω
      = (blockEmbBall i ((Q.P.alg (Fin d)).seedStep (NormEstParam.F (blockProj i θ)) t
            (shiftSeq (i * Q.N d) ω)).1,
        ((Q.P.alg (Fin d)).seedStep (NormEstParam.F (blockProj i θ)) t
            (shiftSeq (i * Q.N d) ω)).2) := by
  suffices hact : ∀ t, t < Q.N d → ((Q.alg d).seedStep (Q.F θ) (i * Q.N d + t) ω).1
      = blockEmbBall i ((Q.P.alg (Fin d)).seedStep (NormEstParam.F (blockProj i θ)) t
          (shiftSeq (i * Q.N d) ω)).1 by
    refine Prod.ext (hact t ht) ?_
    rw [SeededAlg.seedFeedback_eq, SeededAlg.seedFeedback_eq, hact t ht, Q.F_blockEmbBall]
    rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    have ihp : ∀ r, r < t → r < Q.N d → (Q.alg d).seedStep (Q.F θ) (i * Q.N d + r) ω
        = (blockEmbBall i ((Q.P.alg (Fin d)).seedStep (NormEstParam.F (blockProj i θ)) r
              (shiftSeq (i * Q.N d) ω)).1,
          ((Q.P.alg (Fin d)).seedStep (NormEstParam.F (blockProj i θ)) r
              (shiftSeq (i * Q.N d) ω)).2) := by
      intro r hr hrN
      refine Prod.ext (ih r hr hrN) ?_
      rw [SeededAlg.seedFeedback_eq, SeededAlg.seedFeedback_eq, ih r hr hrN, Q.F_blockEmbBall]
      rfl
    rw [SeededAlg.seedStep_eq, SeededAlg.seedStep_eq]
    change Q.nextAction d (i * Q.N d + t) _ _ = blockEmbBall i (Q.P.nextAction t _ _ _)
    rw [Q.nextAction_of_lt i ht]
    have hpast : Q.pastOfBlock d i
          (fun j : Fin (i * Q.N d + t) ↦ (Q.alg d).seedStep (Q.F θ) j ω)
        = NormEstParam.pastOf fun j : Fin t ↦ (Q.P.alg (Fin d)).seedStep
          (NormEstParam.F (blockProj i θ)) j (shiftSeq (i * Q.N d) ω) := by
      funext r
      simp only [pastOfBlock, NormEstParam.pastOf]
      split_ifs with h1 h2 h2
      · rw [ihp r (by omega) (by omega), blockProjBall_blockEmbBall]
      · omega
      · omega
      · rfl
    have hy : Q.yOfBlock d i
          (fun j : Fin (i * Q.N d + t) ↦ (Q.alg d).seedStep (Q.F θ) j ω)
        = NormEstParam.yOf fun j : Fin t ↦ (Q.P.alg (Fin d)).seedStep
          (NormEstParam.F (blockProj i θ)) j (shiftSeq (i * Q.N d) ω) := by
      funext r
      simp only [yOfBlock, NormEstParam.yOf]
      split_ifs with h1 h2 h2
      · rw [ihp r (by omega) (by omega)]
      · omega
      · omega
      · rfl
    rw [hpast, hy]
    rfl

/-- The observation of round `i N + t` of block `i` is the observation of round `t` of the
meta-algorithm against `θ^(i)` on the shifted seed sequence. -/
lemma yω_block (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (ω : ℕ → (Fin d → Bool) × ℝ)
    (i : Fin Q.k) {t : ℕ} (ht : t < Q.N d) :
    Q.yω θ ω (i * Q.N d + t) = Q.P.yω (blockProj i θ) (shiftSeq (i * Q.N d) ω) t := by
  unfold yω SeededAlg.seedFeedback
  rw [Q.seedStep_block θ ω i ht]
  rfl

/-- The estimate of block `i` is the estimate of the meta-algorithm against `θ^(i)` on the
shifted seed sequence. -/
theorem estN_eq (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (ω : ℕ → (Fin d → Bool) × ℝ)
    (i : Fin Q.k) :
    Q.estN d i (Q.yω θ ω)
      = Q.P.estimate (Fin d) (Q.P.yω (blockProj i θ) (shiftSeq (i * Q.N d) ω)) :=
  Q.P.estimate_congr fun _ hr ↦ Q.yω_block θ ω i hr

/-! ### The second phase -/

lemma estN_congr {y y' : ℕ → ℝ} (h : ∀ r < Q.T₂ d, y r = y' r) {m : ℕ} (hm : m < Q.k) :
    Q.estN d m y = Q.estN d m y' := by
  refine Q.P.estimate_congr fun r hr ↦ h _ ?_
  have : (m + 1) * Q.N d ≤ Q.k * Q.N d := Nat.mul_le_mul_right _ hm
  change r < Q.N d at hr
  unfold T₂
  nlinarith

lemma basisRound_basis (m : Fin d) {ℓ : ℕ} (hℓ : ℓ < Q.n₂ d) :
    Q.basisRound d (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ) = some m := by
  have hm : (Fintype.equivFin (Fin d) m : ℕ) + 1 ≤ d :=
    Nat.lt_of_lt_of_eq (Fintype.equivFin (Fin d) m).2 (Fintype.card_fin d)
  have hlt : Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ < d * Q.n₂ d :=
    calc Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ
        < ((Fintype.equivFin (Fin d) m : ℕ) + 1) * Q.n₂ d := by rw [add_mul, one_mul]; omega
      _ ≤ d * Q.n₂ d := Nat.mul_le_mul_right _ hm
  unfold basisRound
  rw [dite_eq_left ⟨by omega, by rw [Nat.add_assoc, Nat.add_sub_cancel_left]; exact hlt⟩]
  congr 1
  rw [Equiv.symm_apply_eq]
  ext
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [mul_comm, Nat.mul_add_div Q.n₂_pos, Nat.div_eq_of_lt hℓ, add_zero]

/-- The action of a round of the second phase: the basis vector of the round on the selected
block, or `0`. -/
theorem seedAction_of_T₂_le (θ : EuclideanSpace ℝ (Fin Q.k × Fin d))
    (ω : ℕ → (Fin d → Bool) × ℝ) {t : ℕ} (ht : Q.T₂ d ≤ t) :
    (Q.alg d).seedAction (Q.F θ) t ω = match Q.basisRound d t with
      | some m => blockEmbBall (Q.iHat d (Q.yω θ ω))
          ⟨EuclideanSpace.single m 1, single_mem_unitBall m⟩
      | none => Q.zeroBB d := by
  rw [SeededAlg.seedAction, SeededAlg.seedStep_eq]
  change Q.nextAction d t (fun j : Fin t ↦ (Q.alg d).seedStep (Q.F θ) j ω) (ω t).1 = _
  unfold nextAction
  rw [ite_eq_right (not_lt.2 ht)]
  have : Q.iHat d (NormEstParam.yOf fun j : Fin t ↦ (Q.alg d).seedStep (Q.F θ) j ω)
      = Q.iHat d (Q.yω θ ω) := by
    refine Q.iHat_congr fun m' hm' ↦ Q.estN_congr (fun r hr ↦ ?_) hm'
    have hr' : r < t := by omega
    rw [NormEstParam.yOf, dite_eq_left hr']
    rfl
  rw [this]
  rcases Q.basisRound d t with _ | m' <;> rfl

lemma yω_basis (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (ω : ℕ → (Fin d → Bool) × ℝ)
    (m : Fin d) {ℓ : ℕ} (hℓ : ℓ < Q.n₂ d) :
    Q.yω θ ω (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)
      = θ (Q.iHat d (Q.yω θ ω), m) + (ω (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)).2 := by
  have h1 : Q.yω θ ω (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)
      = Q.F θ ((Q.alg d).seedAction (Q.F θ) (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ) ω)
        (ω (Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ)).2 :=
    SeededAlg.seedFeedback_eq (Q.alg d) (Q.F θ) _ _
  rw [h1, Q.seedAction_of_T₂_le θ ω (Nat.le_add_right_of_le (Nat.le_add_right _ _)),
    Q.basisRound_basis m hℓ]
  simp [F_blockEmbBall, NormEstParam.F, LinearBandit.linearNoise, EuclideanSpace.inner_single_left]

/-- The vector of empirical means of the second phase is `θ^(î) + Δ`, where `Δ` is the
noise average of the basis window. -/
theorem thetaHat_eq (θ : EuclideanSpace ℝ (Fin Q.k × Fin d))
    (ω : ℕ → (Fin d → Bool) × ℝ) :
    Q.thetaHat d (Q.yω θ ω)
      = blockProj (Q.iHat d (Q.yω θ ω)) θ + lnDelta (Q.n₂ d) (lnProj (Q.T₂ d) (Q.n₂ d) ω) := by
  have hn : (Q.n₂ d : ℝ) ≠ 0 := by have := Q.n₂_pos (d := d); positivity
  ext m
  simp only [thetaHat, lnDelta, lnProj, PiLp.toLp_apply, PiLp.add_apply, blockProj_apply]
  rw [Finset.sum_congr rfl fun ℓ _ ↦ Q.yω_basis θ ω m ℓ.2, Finset.sum_add_distrib, add_div,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hn]

/-! ### The output only depends on the observations of the `T` rounds -/

lemma basis_round_lt (m : Fin d) {ℓ : ℕ} (hℓ : ℓ < Q.n₂ d) :
    Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ < Q.T d := by
  have hm : (Fintype.equivFin (Fin d) m : ℕ) + 1 ≤ d :=
    Nat.lt_of_lt_of_eq (Fintype.equivFin (Fin d) m).2 (Fintype.card_fin d)
  have h2 : ((Fintype.equivFin (Fin d) m : ℕ) + 1) * Q.n₂ d ≤ d * Q.n₂ d :=
    Nat.mul_le_mul_right _ hm
  unfold T
  calc Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + ℓ
      < Q.T₂ d + Fintype.equivFin (Fin d) m * Q.n₂ d + Q.n₂ d := by omega
    _ = Q.T₂ d + ((Fintype.equivFin (Fin d) m : ℕ) + 1) * Q.n₂ d := by ring
    _ ≤ Q.T₂ d + d * Q.n₂ d := Nat.add_le_add_left h2 _

lemma thetaHat_congr {y y' : ℕ → ℝ} (h : ∀ r < Q.T d, y r = y' r) :
    Q.thetaHat d y = Q.thetaHat d y' := by
  ext m
  simp only [thetaHat, PiLp.toLp_apply]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ ↦ h _ (Q.basis_round_lt m ℓ.2)

lemma recommend_congr {y y' : ℕ → ℝ} (h : ∀ r < Q.T d, y r = y' r) :
    Q.recommend d y = Q.recommend d y' := by
  unfold recommend
  rw [Q.iHat_congr fun m hm ↦
    Q.estN_congr (fun r hr ↦ h r (hr.trans_le (Nat.le_add_right _ _))) hm, Q.thetaHat_congr h]

lemma yOf_seedFinHist (θ : EuclideanSpace ℝ (Fin Q.k × Fin d)) (ω : ℕ → (Fin d → Bool) × ℝ)
    {r : ℕ} (hr : r < Q.T d) :
    NormEstParam.yOf ((Q.alg d).seedFinHist (Q.F θ) (Q.T d) ω) r = Q.yω θ ω r := by
  rw [NormEstParam.yOf, dite_eq_left hr]
  rfl

lemma recommend_yOf_seedFinHist (θ : EuclideanSpace ℝ (Fin Q.k × Fin d))
    (ω : ℕ → (Fin d → Bool) × ℝ) :
    Q.recommend d (NormEstParam.yOf ((Q.alg d).seedFinHist (Q.F θ) (Q.T d) ω))
      = Q.recommend d (Q.yω θ ω) :=
  Q.recommend_congr fun _ hr ↦ Q.yOf_seedFinHist θ ω hr

end BlockParam

end Maiti2026Power
