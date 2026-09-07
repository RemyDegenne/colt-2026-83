/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.NormEstStat
public import Maiti2026Power.LeanMachineLearning.Seeded

/-!
# The norm-estimation meta-algorithm as a seeded algorithm

The meta-algorithm (Algorithm 4 of the paper) is a seeded algorithm with seeds the uniform Boolean
vectors: at a round starting a Rademacher block it plays the direction `radDir u` given by the
fresh seed `u`; at the other rounds of a block it repeats the action of the block start (read
from the history); in the large-norm regime it plays the basis vectors; otherwise it idles.

* `planAction js t u`: the action of round `t` given the outcome `js` of the multi-scale phase
  and the seed sequence `u` (only the seeds at block starts are used);
* `nextAction t past js u`: the same action computed from the past actions;
* `alg`: the seeded algorithm; `output`: the deterministic output.
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma single_mem_unitBall (i : ι) : EuclideanSpace.single i (1 : ℝ) ∈ unitBall ι := by
  rw [mem_unitBall_iff]
  simp

/-- The zero action of the unit ball. -/
def unitBallZero : unitBall ι := ⟨0, zero_mem_unitBall⟩

namespace NormEstParam

variable (P : NormEstParam)

/-- The action of the plan at round `t`, given the outcome `js` of the multi-scale phase and the
seed sequence `u`. -/
noncomputable def planAction (js t : ℕ) (u : ℕ → ι → Bool) : unitBall ι :=
  match P.rbBlock (ι := ι) js t with
  | some b => ⟨radDir (u b), radDir_mem_unitBall _⟩
  | none =>
    match P.basisRound (ι := ι) js t with
    | some i => ⟨EuclideanSpace.single i 1, single_mem_unitBall i⟩
    | none => unitBallZero

/-- The action at round `t` computed from the past actions `past`, the outcome `js` and the
fresh seed `u`. -/
noncomputable def nextAction (t : ℕ) (past : ℕ → unitBall ι) (js : ℕ) (u : ι → Bool) :
    unitBall ι :=
  match P.rbBlock (ι := ι) js t with
  | some b => if b = t then ⟨radDir u, radDir_mem_unitBall _⟩ else past b
  | none =>
    match P.basisRound (ι := ι) js t with
    | some i => ⟨EuclideanSpace.single i 1, single_mem_unitBall i⟩
    | none => unitBallZero

/-- The past actions of a history of rounds `0..n`, extended by the zero action. -/
def pastOf {n : ℕ} (h : Iic n → unitBall ι × ℝ) : ℕ → unitBall ι :=
  fun r ↦ if hr : r ∈ Iic n then (h ⟨r, hr⟩).1 else unitBallZero

omit [DecidableEq ι] in
lemma measurable_pastOf_apply {n : ℕ} (r : ℕ) :
    Measurable fun h : Iic n → unitBall ι × ℝ ↦ pastOf h r := by
  unfold pastOf
  split_ifs
  exacts [(measurable_pi_apply _).fst, measurable_const]

lemma measurable_nextAction_of (t js : ℕ) {α : Type*} [MeasurableSpace α]
    {past : α → ℕ → unitBall ι} (hpast : ∀ b, Measurable fun a ↦ past a b) :
    Measurable fun p : α × (ι → Bool) ↦ P.nextAction (ι := ι) t (past p.1) js p.2 := by
  unfold nextAction
  rcases hb : P.rbBlock (ι := ι) js t with _ | b
  · rcases hi : P.basisRound (ι := ι) js t with _ | i
    · exact measurable_const
    · exact measurable_const
  · simp only
    split_ifs
    · exact (measurable_radDir.comp measurable_snd).subtype_mk
    · exact (hpast b).comp measurable_fst

lemma measurable_nextAction (t js : ℕ) {n : ℕ} :
    Measurable fun p : (Iic n → unitBall ι × ℝ) × (ι → Bool) ↦
      P.nextAction (ι := ι) t (pastOf p.1) js p.2 :=
  P.measurable_nextAction_of t js fun b ↦ measurable_pastOf_apply b

/-- The norm-estimation meta-algorithm as a seeded algorithm on the unit ball. -/
noncomputable def alg (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SeededAlg (unitBall ι) ℝ (ι → Bool) where
  seed := uniformBoolVec ι
  act0 u := P.nextAction (ι := ι) 0 (fun _ ↦ unitBallZero) 0 u
  measurable_act0 := by
    unfold nextAction
    rcases hb : P.rbBlock (ι := ι) 0 0 with _ | b
    · rcases hi : P.basisRound (ι := ι) 0 0 with _ | i <;> exact measurable_const
    · simp only
      split_ifs
      · exact measurable_radDir.subtype_mk
      · exact measurable_const
  next n h u := P.nextAction (ι := ι) (n + 1) (pastOf h) (P.jStar ι (yOfIic h)) u
  measurable_next n := by
    have h1 : Measurable fun p : ℕ × ((Iic n → unitBall ι × ℝ) × (ι → Bool)) ↦
        P.nextAction (ι := ι) (n + 1) (pastOf p.2.1) p.1 p.2.2 :=
      measurable_from_prod_countable_right fun js ↦ P.measurable_nextAction (n + 1) js
    have h2 : Measurable fun p : (Iic n → unitBall ι × ℝ) × (ι → Bool) ↦
        (P.jStar ι (yOfIic p.1), p) :=
      ((P.measurable_jStar).comp ((measurable_yOfIic n).comp measurable_fst)).prodMk measurable_id
    exact h1.comp h2

omit [DecidableEq ι] in
/-- The deterministic output of the meta-algorithm: the estimate computed from the observations
of the history of the `T` rounds. -/
noncomputable def output (ι : Type*) [Fintype ι] (h : Fin (P.T ι) → unitBall ι × ℝ) : ℝ :=
  P.estimate ι (yOf h)

omit [DecidableEq ι] in
lemma measurable_output : Measurable (P.output ι) :=
  (P.measurable_estimate).comp (measurable_yOf _)

end NormEstParam

end Maiti2026Power
