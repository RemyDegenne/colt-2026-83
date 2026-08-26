/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.Run
public import COLT83.LeanMachineLearning.FixedBudget

/-!
# Algorithms agreeing on a prefix; transfer of PAC guarantees

Two algorithms `alg`, `alg'` *agree until time `N`* (`Algorithm.AgreeUntil alg alg' N`) if they
have the same initial action distribution and the same policies at times `n < N`, that is they
choose the actions `a_0, …, a_N` in the same way. An algorithm-environment sequence for `alg` is
then an algorithm-environment sequence for `alg'` until time `N` (LML `IsAlgEnvSeqUntil`), and the
law of the history up to time `N` is the one of the canonical trajectory measure of `alg'`
(`IsAlgEnvSeqUntil.map_history_eq`).

For a fixed-budget identification algorithm `A` with budget `n + 1`, an algorithm-environment
sequence for `A.alg` until time `n` together with an output `out` whose conditional law given the
history of the first `n + 1` rounds is `A.output (n + 1)` has the same joint law of
(history, output) as the canonical run of `A` (`IdentAlg.map_finHistory_out_eq`);
in particular every PAC guarantee of `A` applies to `out`
(`IdentAlg.IsPAC.le_measureReal_of_isAlgEnvSeqUntil`). This is how a PAC algorithm is used as
the first phase of a composed algorithm (the test of the adaptive lower bound, blueprint
`lem:test_from_alg`) without a general composition lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w

namespace Learning

variable {𝓐 : Type u} {𝓨 : Type v} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg alg' : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨} {N : ℕ}

/-- Two algorithms agree until time `N` if they have the same initial action distribution and the
same policies at times `n < N` (they choose the actions `a_0, …, a_N` in the same way). -/
structure Algorithm.AgreeUntil (alg alg' : Algorithm 𝓐 𝓨) (N : ℕ) : Prop where
  /-- The initial action distributions coincide. -/
  p0_eq : alg.p0 = alg'.p0
  /-- The policies coincide at times `n < N`. -/
  policy_eq : ∀ n < N, alg.policy n = alg'.policy n

namespace Algorithm.AgreeUntil

lemma refl (alg : Algorithm 𝓐 𝓨) (N : ℕ) : alg.AgreeUntil alg N := ⟨rfl, fun _ _ ↦ rfl⟩

lemma symm (h : alg.AgreeUntil alg' N) : alg'.AgreeUntil alg N :=
  ⟨h.p0_eq.symm, fun n hn ↦ (h.policy_eq n hn).symm⟩

lemma mono (h : alg.AgreeUntil alg' N) {N' : ℕ} (hN : N' ≤ N) : alg.AgreeUntil alg' N' :=
  ⟨h.p0_eq, fun n hn ↦ h.policy_eq n (hn.trans_le hN)⟩

end Algorithm.AgreeUntil

/-- An algorithm-environment sequence until time `N` for `alg` is one for every algorithm agreeing
with `alg` until time `N`. -/
lemma IsAlgEnvSeqUntil.of_agreeUntil (h : IsAlgEnvSeqUntil X Y alg env P N)
    (hagree : alg.AgreeUntil alg' N) : IsAlgEnvSeqUntil X Y alg' env P N where
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasLaw_action_zero := hagree.p0_eq ▸ h.hasLaw_action_zero
  hasCondDistrib_feedback_zero := h.hasCondDistrib_feedback_zero
  hasCondDistrib_action n hn := hagree.policy_eq n hn ▸ h.hasCondDistrib_action n hn
  hasCondDistrib_feedback n hn := h.hasCondDistrib_feedback n hn

/-- An algorithm-environment sequence for `alg` is an algorithm-environment sequence until time
`N` for every algorithm agreeing with `alg` until time `N`. -/
lemma IsAlgEnvSeq.isAlgEnvSeqUntil_of_agreeUntil (h : IsAlgEnvSeq X Y alg env P)
    (hagree : alg.AgreeUntil alg' N) : IsAlgEnvSeqUntil X Y alg' env P N :=
  (h.isAlgEnvSeqUntil N).of_agreeUntil hagree

lemma IsAlgEnvSeqUntil.measurable_history (h : IsAlgEnvSeqUntil X Y alg env P N) (n : ℕ) :
    Measurable (history X Y n) :=
  Learning.measurable_history h.measurable_action h.measurable_feedback n

/-- The law of the history up to time `N` of an algorithm-environment sequence until time `N` is
the law of the history under the canonical trajectory measure. -/
lemma IsAlgEnvSeqUntil.map_history_eq [IsProbabilityMeasure P]
    (h : IsAlgEnvSeqUntil X Y alg env P N) :
    P.map (history X Y N) = (trajMeasure alg env).map (IT.hist N) := by
  rw [IT.hist_eq_frestrictLe]
  exact eq_trajMeasure_map_frestrictLe_of_isAlgEnvSeqUntil h

/-- The history of the first `n + 1` rounds, as a function of the history up to time `n`. -/
def toFinHistory (n : ℕ) (h : Finset.Iic n → 𝓐 × 𝓨) : Fin (n + 1) → 𝓐 × 𝓨 :=
  fun i ↦ h ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩

@[fun_prop]
lemma measurable_toFinHistory (n : ℕ) : Measurable (toFinHistory (𝓐 := 𝓐) (𝓨 := 𝓨) n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

omit m𝓐 m𝓨 in
lemma finHistory_succ_eq_toFinHistory_comp (n : ℕ) :
    finHistory X Y (n + 1) = toFinHistory n ∘ history X Y n := rfl

omit m𝓐 m𝓨 in
lemma IT.finHistory_succ_eq_toFinHistory_comp (n : ℕ) :
    finHistory (IT.action (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.feedback (n + 1) =
      toFinHistory n ∘ IT.hist n := rfl

namespace IdentAlg

variable {𝓞 : Type w} {m𝓞 : MeasurableSpace 𝓞} {A : IdentAlg 𝓐 𝓨 𝓞} {n : ℕ} {out : Ω → 𝓞}

/-- If `(X, Y)` is an algorithm-environment sequence for `A.alg` until time `n` and `out` has
conditional law `A.output (n + 1)` given the history of the first `n + 1` rounds, then
(history, output) has the same law as under the canonical run of `A` with budget `n + 1`
(`fixedBudgetRunMeasure`). -/
lemma map_finHistory_out_eq [IsProbabilityMeasure P] [IsMarkovKernel (A.output (n + 1))]
    (h : IsAlgEnvSeqUntil X Y A.alg env P n)
    (hout : HasCondDistrib out (finHistory X Y (n + 1)) (A.output (n + 1)) P) :
    P.map (fun ω ↦ (finHistory X Y (n + 1) ω, out ω)) =
      (A.fixedBudgetRunMeasure env (n + 1)).map
        (fun ω ↦ (finHistory IT.action IT.feedback (n + 1) ω.1, ω.2)) := by
  have h1 := hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) (A.output (n + 1))
    (measurable_finHistory_traj (n + 1)) (fun _ ↦ inferInstance)
  unfold fixedBudgetRunMeasure
  rw [hout.map_eq, h1.map_eq]
  congr 1
  rw [finHistory_succ_eq_toFinHistory_comp, ← Measure.map_map (measurable_toFinHistory n)
    (h.measurable_history n), h.map_history_eq, Measure.map_map (measurable_toFinHistory n)
    (IT.measurable_hist n), ← IT.finHistory_succ_eq_toFinHistory_comp]
  calc (trajMeasure A.alg env).map (finHistory IT.action IT.feedback (n + 1))
      = ((trajMeasure A.alg env ⊗ₘ (A.output (n + 1)).comap
          (finHistory IT.action IT.feedback (n + 1)) (measurable_finHistory_traj (n + 1))).fst).map
          (finHistory IT.action IT.feedback (n + 1)) := by
        rw [Measure.fst_compProd]
    _ = _ := by
        rw [Measure.fst, Measure.map_map (measurable_finHistory_traj (n + 1)) measurable_fst]
        rfl

/-- **Transfer of a PAC guarantee to a partial run.** If `A` is `δ`-PAC with budget `n + 1`,
`(X, Y)` is an algorithm-environment sequence for `A.alg` until time `n` in `env θ` and `out` has
conditional law `A.output (n + 1)` given the history of the first `n + 1` rounds, then `out` is
`good θ` with probability at least `1 - δ`. -/
lemma IsPAC.le_measureReal_of_isAlgEnvSeqUntil [IsProbabilityMeasure P] {Θ : Type*}
    {env : Θ → Environment 𝓐 𝓨} {good : Θ → 𝓞 → Prop} {δ : ℝ}
    (hpac : A.IsPAC.{max u v w} env good δ) (hA : A.IsFixedBudget (n + 1)) (θ : Θ)
    (h : IsAlgEnvSeqUntil X Y A.alg (env θ) P n)
    (hout : HasCondDistrib out (finHistory X Y (n + 1)) (A.output (n + 1)) P)
    (hgood : MeasurableSet {o | good θ o}) :
    1 - δ ≤ P.real {ω | good θ (out ω)} := by
  have := hA.isMarkovKernel_output
  have hp := hpac θ _ _ _ _ (hA.isRun_fixedBudgetRunMeasure (env := env θ))
  have hmap := map_finHistory_out_eq h hout
  have hg : Measurable fun ω : (ℕ → 𝓐 × 𝓨) × 𝓞 ↦
      (finHistory IT.action IT.feedback (n + 1) ω.1, ω.2) :=
    ((measurable_finHistory_traj (n + 1)).comp measurable_fst).prodMk measurable_snd
  have hf : AEMeasurable (fun ω ↦ (finHistory X Y (n + 1) ω, out ω)) P :=
    hout.aemeasurable
  calc 1 - δ ≤ (A.fixedBudgetRunMeasure (env θ) (n + 1)).real {ω | good θ ω.2} := hp
    _ = ((A.fixedBudgetRunMeasure (env θ) (n + 1)).map
          (fun ω ↦ (finHistory IT.action IT.feedback (n + 1) ω.1, ω.2))).real
          (Prod.snd ⁻¹' {o | good θ o}) := by
        rw [measureReal_def, measureReal_def, Measure.map_apply hg (measurable_snd hgood)]
        rfl
    _ = (P.map (fun ω ↦ (finHistory X Y (n + 1) ω, out ω))).real
          (Prod.snd ⁻¹' {o | good θ o}) := by rw [hmap]
    _ = P.real {ω | good θ (out ω)} := by
        rw [measureReal_def, measureReal_def,
          Measure.map_apply_of_aemeasurable hf (measurable_snd hgood)]
        rfl

end IdentAlg

end Learning
