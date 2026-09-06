/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.NormEstAlg

/-!
# The run of the norm-estimation algorithm on the seed space follows the plan

On the product space of seeds and noises, the actions of the meta-algorithm are the plan actions
`planAction (jsω) t (seeds ω)` (`seedAction_eq_planAction`), and the statistics computed from the
observations are the Rademacher block statistics and the large-norm statistic of the window
projections (`testStat_eq_rbStat`, `addStat_eq_rbStat`, `lnRStat_eq_lnR`).
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning

namespace COLT83

namespace NormEstParam

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : NormEstParam)

/-- The noise function of the linear Gaussian bandit on the unit ball. -/
noncomputable abbrev F (θ : EuclideanSpace ℝ ι) : unitBall ι → ℝ → ℝ :=
  LinearBandit.linearNoise (unitBall ι) θ

/-- The seeds of a seed-noise sequence. -/
def seedsOf (ω : ℕ → (ι → Bool) × ℝ) : ℕ → ι → Bool := fun r ↦ (ω r).1

/-- The observation sequence of the run on the seed space. -/
noncomputable def yω (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) : ℕ → ℝ :=
  fun t ↦ (P.alg ι).seedFeedback (F θ) t ω

/-- The outcome of the multi-scale phase of the run on the seed space. -/
noncomputable def jsω (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) : ℕ :=
  P.jStar ι (P.yω θ ω)

variable {P}

lemma seedFeedback_eq (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) (t : ℕ) :
    (P.alg ι).seedFeedback (F θ) t ω
      = inner ℝ ((P.alg ι).seedAction (F θ) t ω : EuclideanSpace ℝ ι) θ + (ω t).2 := by
  cases t with
  | zero =>
    rw [SeededAlg.seedFeedback, SeededAlg.seedAction, SeededAlg.seedStep_zero]
    rfl
  | succ t =>
    rw [SeededAlg.seedFeedback, SeededAlg.seedAction, SeededAlg.seedStep_succ]
    rfl

omit [DecidableEq ι] in
lemma rbBlock_of_lt {js js' t : ℕ} (ht : t < P.T₁ ι) :
    P.rbBlock (ι := ι) js t = P.rbBlock (ι := ι) js' t := by
  unfold rbBlock
  simp only [ht, ↓reduceIte]

lemma planAction_of_lt {js js' t : ℕ} (ht : t < P.T₁ ι) (u : ℕ → ι → Bool) :
    P.planAction (ι := ι) js t u = P.planAction (ι := ι) js' t u := by
  unfold planAction
  rw [rbBlock_of_lt (js' := js') ht]
  rcases P.rbBlock (ι := ι) js' t with _ | b
  · rw [basisRound_of_lt ht, basisRound_of_lt ht]
  · rfl

lemma planAction_of_block {js b : ℕ} (u : ℕ → ι → Bool) (hb : P.rbBlock (ι := ι) js b = some b) :
    P.planAction (ι := ι) js b u = ⟨radDir (u b), radDir_mem_unitBall _⟩ := by
  unfold planAction
  rw [hb]

lemma nextAction_eq_planAction (hd : 0 < Fintype.card ι) {t : ℕ} (past : ℕ → unitBall ι)
    (js : ℕ) (u : ℕ → ι → Bool)
    (hpast : ∀ b, P.rbBlock (ι := ι) js b = some b → b < t →
      past b = ⟨radDir (u b), radDir_mem_unitBall _⟩) :
    P.nextAction (ι := ι) t past js (u t) = P.planAction (ι := ι) js t u := by
  unfold nextAction planAction
  rcases hb : P.rbBlock (ι := ι) js t with _ | b
  · rfl
  · simp only
    split_ifs with hbt
    · subst hbt
      rfl
    · exact hpast b (rbBlock_self hd hb) (lt_of_le_of_ne (rbBlock_le hb) hbt)

omit [DecidableEq ι] in
lemma T₁_pos (hd : 0 < Fintype.card ι) : 0 < P.T₁ ι := by
  have h1 := P.one_le_J ι hd
  have h2 : P.start ι 1 ≤ P.T₁ ι := P.start_mono h1
  rw [start_succ, start_zero, zero_add] at h2
  exact lt_of_lt_of_le (P.window_pos ι hd 0) h2

/-- At round `0`, `nextAction` does not depend on the past nor on the outcome: it is the first
action of the algorithm. -/
lemma nextAction_zero_eq (hd : 0 < Fintype.card ι) (past : ℕ → unitBall ι) (js : ℕ)
    (u₀ : ι → Bool) : P.nextAction (ι := ι) 0 past js u₀ = (P.alg ι).act0 u₀ := by
  have h1 := nextAction_eq_planAction (P := P) hd past js (fun _ ↦ u₀)
    fun b _ hb ↦ absurd hb (Nat.not_lt_zero b)
  have h2 := nextAction_eq_planAction (P := P) hd (fun _ ↦ unitBallZero) 0 (fun _ ↦ u₀)
    fun b _ hb ↦ absurd hb (Nat.not_lt_zero b)
  change P.nextAction (ι := ι) 0 past js u₀ = P.nextAction (ι := ι) 0 (fun _ ↦ unitBallZero) 0 u₀
  rw [h1, h2, planAction_of_lt (js' := 0) (T₁_pos hd)]

/-- **The run follows the plan**: on the seed space, the action of round `t` is the plan action
for the outcome `jsω` of the multi-scale phase. -/
theorem seedAction_eq_planAction (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι)
    (ω : ℕ → (ι → Bool) × ℝ) (t : ℕ) :
    (P.alg ι).seedAction (F θ) t ω = P.planAction (ι := ι) (P.jsω θ ω) t (seedsOf ω) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero =>
      rw [SeededAlg.seedAction, SeededAlg.seedStep_zero]
      change P.nextAction (ι := ι) 0 (fun _ ↦ unitBallZero) 0 (seedsOf ω 0) = _
      rw [planAction_of_lt (js' := 0) (T₁_pos hd)]
      exact nextAction_eq_planAction hd _ _ _ fun b _ hb ↦ absurd hb (Nat.not_lt_zero b)
    | succ t =>
      rw [SeededAlg.seedAction, SeededAlg.seedStep_succ]
      change P.nextAction (ι := ι) (t + 1) (pastOf fun i : Iic t ↦ (P.alg ι).seedStep (F θ) i ω)
        (P.jStar ι (yOfIic fun i : Iic t ↦ (P.alg ι).seedStep (F θ) i ω)) (seedsOf ω (t + 1)) = _
      have hpast : ∀ b, P.rbBlock (ι := ι) (P.jsω θ ω) b = some b → b < t + 1 →
          pastOf (fun i : Iic t ↦ (P.alg ι).seedStep (F θ) i ω) b
            = ⟨radDir (seedsOf ω b), radDir_mem_unitBall _⟩ := by
        intro b hb hbt
        have hbt' : b ∈ Iic t := mem_Iic.2 (Nat.lt_succ_iff.1 hbt)
        rw [pastOf, dite_eq_left hbt']
        change (P.alg ι).seedAction (F θ) b ω = _
        rw [ih b hbt, planAction_of_block _ hb]
      rcases lt_or_ge (t + 1) (P.T₁ ι) with hlt | hge
      · rw [planAction_of_lt
          (js' := P.jStar ι (yOfIic fun i : Iic t ↦ (P.alg ι).seedStep (F θ) i ω)) hlt]
        refine nextAction_eq_planAction hd _ _ _ fun b hb hbt ↦ ?_
        rw [rbBlock_of_lt (js' := P.jsω θ ω) (hbt.trans hlt)] at hb
        exact hpast b hb hbt
      · have hjs : P.jStar ι (yOfIic fun i : Iic t ↦ (P.alg ι).seedStep (F θ) i ω) = P.jsω θ ω := by
          refine P.jStar_congr fun r hr ↦ ?_
          have hr' : r ∈ Iic t := mem_Iic.2 (by omega)
          rw [yOfIic, dite_eq_left hr']
          rfl
        rw [hjs]
        exact nextAction_eq_planAction hd _ _ _ hpast

/-- The observation of round `t` on the seed space. -/
lemma yω_eq (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) (t : ℕ) :
    P.yω θ ω t = inner ℝ (P.planAction (ι := ι) (P.jsω θ ω) t (seedsOf ω) : EuclideanSpace ℝ ι) θ
      + (ω t).2 := by
  rw [yω, seedFeedback_eq, seedAction_eq_planAction hd]

/-- The test statistic at scale `j < J` is the Rademacher block statistic of window `j`. -/
theorem testStat_eq_rbStat (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι)
    (ω : ℕ → (ι → Bool) × ℝ) {j : ℕ} (hj : j < P.J ι) :
    P.testStat ι j (P.yω θ ω)
      = rbStat (P.s ι j) (P.K j) θ (rbProj (P.start ι j) (P.s ι j) (P.K j) ω) := by
  unfold testStat
  refine winStat_eq_rbStat (P.s_pos ι hd j) θ _ _ fun k ℓ ↦ ?_
  rw [yω_eq hd, planAction, rbBlock_window hd _ hj k.2 ℓ.2]
  rfl

/-- The additive statistic at the outcome `0 < jsω < J` is the Rademacher block statistic of the
second-phase window. -/
theorem addStat_eq_rbStat (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι)
    (ω : ℕ → (ι → Bool) × ℝ) (hjs : 0 < P.jsω θ ω) (hjJ : P.jsω θ ω < P.J ι) :
    P.addStat ι (P.jsω θ ω) (P.yω θ ω)
      = rbStat (P.s' ι (P.jsω θ ω)) (P.K' (P.jsω θ ω)) θ
        (rbProj (P.T₁ ι) (P.s' ι (P.jsω θ ω)) (P.K' (P.jsω θ ω)) ω) := by
  unfold addStat
  refine winStat_eq_rbStat (P.s'_pos ι hd _) θ _ _ fun k ℓ ↦ ?_
  rw [yω_eq hd, planAction, rbBlock_add hd hjs hjJ k.2 ℓ.2]
  rfl

/-- The large-norm statistic at the outcome `jsω = J` is `lnR` of the second-phase window. -/
theorem lnRStat_eq_lnR (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι)
    (ω : ℕ → (ι → Bool) × ℝ) (hJ : P.jsω θ ω = P.J ι) :
    P.lnRStat ι (P.yω θ ω) = lnR θ P.n (lnProj (P.T₁ ι) P.n ω) := by
  refine P.lnRStat_eq θ _ fun i ℓ ↦ ?_
  rw [yω_eq hd, hJ, planAction, rbBlock_of_J (Nat.le_add_right_of_le (Nat.le_add_right _ _)),
    basisRound_basis i ℓ.2]
  simp [lnProj, EuclideanSpace.inner_single_left]

end NormEstParam

end COLT83
