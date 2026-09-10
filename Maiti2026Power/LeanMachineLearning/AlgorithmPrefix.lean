/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.Run

/-!
# Algorithms agreeing on a prefix; transfer of PAC guarantees

Two algorithms `alg`, `alg'` *agree until time `N`* (`Algorithm.AgreeUntil alg alg' N`) if they
have the same policies at times `n < N`, that is they choose the first `N` actions in the same
way. An algorithm-environment sequence for `alg` is then an algorithm-environment sequence for
`alg'` until time `N` (LML `IsAlgEnvSeqUntil`), and the law of the history of the first `N`
rounds is the one of the canonical trajectory measure of `alg'` (LML
`IsAlgEnvSeqUntil.map_history`).

For a fixed-budget identification algorithm `A` with budget `T`, an algorithm-environment
sequence for `A.alg` until time `T` together with an output `out` whose conditional law given the
history of the first `T` rounds is `A.output T` has the same joint law of
(history, output) as the canonical run of `A` (`IdentAlg.map_history_out_eq`);
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
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg alg' : Algorithm Unit 𝓐 𝓨}
  {env : Environment Unit 𝓐 𝓨} {N : ℕ}

/-- Two algorithms agree until time `N` if they have the same policies at times `n < N` (they
choose the actions `a_0, …, a_{N-1}` in the same way). -/
structure Algorithm.AgreeUntil (alg alg' : Algorithm Unit 𝓐 𝓨) (N : ℕ) : Prop where
  /-- The policies coincide at times `n < N`. -/
  policy_eq : ∀ n < N, alg.policy n = alg'.policy n

namespace Algorithm.AgreeUntil

lemma refl (alg : Algorithm Unit 𝓐 𝓨) (N : ℕ) : alg.AgreeUntil alg N := ⟨fun _ _ ↦ rfl⟩

lemma symm (h : alg.AgreeUntil alg' N) : alg'.AgreeUntil alg N :=
  ⟨fun n hn ↦ (h.policy_eq n hn).symm⟩

lemma mono (h : alg.AgreeUntil alg' N) {N' : ℕ} (hN : N' ≤ N) : alg.AgreeUntil alg' N' :=
  ⟨fun n hn ↦ h.policy_eq n (hn.trans_le hN)⟩

end Algorithm.AgreeUntil

/-- An algorithm-environment sequence until time `N` for `alg` is one for every algorithm agreeing
with `alg` until time `N`. -/
lemma IsAlgEnvSeqUntil.of_agreeUntil (h : IsAlgEnvSeqUntil O X Y alg env P N)
    (hagree : alg.AgreeUntil alg' N) : IsAlgEnvSeqUntil O X Y alg' env P N where
  measurable_obs := h.measurable_obs
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs := h.hasCondDistrib_obs
  hasCondDistrib_action n hn := hagree.policy_eq n hn ▸ h.hasCondDistrib_action n hn
  hasCondDistrib_feedback n hn := h.hasCondDistrib_feedback n hn

/-- An algorithm-environment sequence for `alg` is an algorithm-environment sequence until time
`N` for every algorithm agreeing with `alg` until time `N`. -/
lemma IsAlgEnvSeq.isAlgEnvSeqUntil_of_agreeUntil (h : IsAlgEnvSeq O X Y alg env P)
    (hagree : alg.AgreeUntil alg' N) : IsAlgEnvSeqUntil O X Y alg' env P N :=
  (h.isAlgEnvSeqUntil N).of_agreeUntil hagree

namespace IdentAlg

variable {𝓞 : Type w} {m𝓞 : MeasurableSpace 𝓞} {A : IdentAlg 𝓐 𝓨 𝓞} {T : ℕ} {out : Ω → 𝓞}

/-- If `(O, X, Y)` is an algorithm-environment sequence for `A.alg` until time `T` and `out` has
conditional law `A.output T` given the history of the first `T` rounds, then
(history, output) has the same law as under the canonical run of `A` with budget `T`
(`fixedBudgetRunMeasure`). -/
lemma map_history_out_eq [IsProbabilityMeasure P] [IsMarkovKernel (A.output T)]
    (h : IsAlgEnvSeqUntil O X Y A.alg env P T)
    (hout : HasCondDistrib out (history O X Y T) (A.output T) P) :
    P.map (fun ω ↦ (history O X Y T ω, out ω)) =
      (A.fixedBudgetRunMeasure env T).map
        (fun ω ↦ (history IT.obs IT.action IT.feedback T ω.1, ω.2)) := by
  have h1 := hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) (A.output T)
    (measurable_history_traj T) (fun _ ↦ inferInstance)
  unfold fixedBudgetRunMeasure
  rw [hout.map_eq, h1.map_eq]
  congr 1
  rw [h.map_history]
  calc (trajMeasure A.alg env).map (history IT.obs IT.action IT.feedback T)
      = ((trajMeasure A.alg env ⊗ₘ (A.output T).comap
          (history IT.obs IT.action IT.feedback T) (measurable_history_traj T)).fst).map
          (history IT.obs IT.action IT.feedback T) := by
        rw [Measure.fst_compProd]
    _ = _ := by
        rw [Measure.fst, Measure.map_map (measurable_history_traj T) measurable_fst]
        rfl

/-- **Transfer of a PAC guarantee to a partial run.** If `A` is `δ`-PAC with budget `T`,
`(O, X, Y)` is an algorithm-environment sequence for `A.alg` until time `T` in `env θ` and `out`
has
conditional law `A.output T` given the history of the first `T` rounds, then `out` is
`good θ` with probability at least `1 - δ`. -/
lemma IsPAC.le_measureReal_of_isAlgEnvSeqUntil [IsProbabilityMeasure P] {Θ : Type*}
    {env : Θ → Environment Unit 𝓐 𝓨} {good : Θ → 𝓞 → Prop} {δ : ℝ}
    (hpac : A.IsPAC.{max u v w} env good δ) (hA : A.IsFixedBudget T) (θ : Θ)
    (h : IsAlgEnvSeqUntil O X Y A.alg (env θ) P T)
    (hout : HasCondDistrib out (history O X Y T) (A.output T) P)
    (hgood : MeasurableSet {o | good θ o}) :
    1 - δ ≤ P.real {ω | good θ (out ω)} := by
  have := hA.isMarkovKernel_output
  have hp := hpac θ _ _ _ _ _ (hA.isRun_fixedBudgetRunMeasure (env := env θ))
  have hmap := map_history_out_eq h hout
  have hg : Measurable fun ω : (ℕ → Round Unit 𝓐 𝓨) × 𝓞 ↦
      (history IT.obs IT.action IT.feedback T ω.1, ω.2) :=
    ((measurable_history_traj T).comp measurable_fst).prodMk measurable_snd
  have hf : AEMeasurable (fun ω ↦ (history O X Y T ω, out ω)) P := hout.aemeasurable
  calc 1 - δ ≤ (A.fixedBudgetRunMeasure (env θ) T).real {ω | good θ ω.2} := hp
    _ = ((A.fixedBudgetRunMeasure (env θ) T).map
          (fun ω ↦ (history IT.obs IT.action IT.feedback T ω.1, ω.2))).real
          (Prod.snd ⁻¹' {o | good θ o}) := by
        rw [measureReal_def, measureReal_def, Measure.map_apply hg (measurable_snd hgood)]
        rfl
    _ = (P.map (fun ω ↦ (history O X Y T ω, out ω))).real (Prod.snd ⁻¹' {o | good θ o}) := by
        rw [hmap]
    _ = P.real {ω | good θ (out ω)} := by
        rw [measureReal_def, measureReal_def,
          Measure.map_apply_of_aemeasurable hf (measurable_snd hgood)]
        rfl

end IdentAlg

end Learning
