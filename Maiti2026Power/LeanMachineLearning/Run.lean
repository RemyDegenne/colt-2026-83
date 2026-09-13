/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.IdentAlg
public import Maiti2026Power.Mathlib.Probability.CondDistrib

/-!
# Transport and existence of runs of identification algorithms

* Algorithm-environment sequences and runs can be transported along a map `g : Ω → Ω'` carrying
  `P` to `P'`: if `(O, X, Y, out)` is a run on `(Ω', P')` then `(O ∘ g, X ∘ g, Y ∘ g, out ∘ g)` is a
  run on `(Ω, P)` (`IsAlgEnvSeq.comp_hasLaw`, `IdentAlg.IsRun.comp_hasLaw`).
* Every identification algorithm `A` has a run in every environment, on the space
  `(ℕ → Round 𝓞 𝓐 𝓨) × 𝓓` of (trajectory, output) pairs: the trajectory has the law
  `trajMeasure A.alg env` of the Ionescu-Tulcea construction and the output is drawn from the
  output rule applied to the history at the stopping time (`IdentAlg.runMeasure`,
  `IdentAlg.isRun_runMeasure`); the output rule being a Markov kernel, this is a probability
  measure. Consequently the PAC property `IdentAlg.IsPAC`, a statement about the law
  `IdentAlg.outputMeasure` of the output, follows from a bound on the probability of a bad
  output for every run on a probability space in the universe of this canonical run
  (`IdentAlg.IsPAC.of_forall_isRun`; the converse, for runs in any universe, is LML's
  `IdentAlg.IsPAC.measureReal_bad_of_isRun`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u v w z

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
  [IsProbabilityMeasure P'] {g : Ω → Ω'}

section transport

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {O : ℕ → Ω' → 𝓞} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨}

/-- An algorithm-environment sequence is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IsAlgEnvSeq.comp_hasLaw (h : IsAlgEnvSeq O X Y alg env P') (hg : HasLaw g P' P)
    (hgm : Measurable g) :
    IsAlgEnvSeq (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) alg env P where
  measurable_obs n := (h.measurable_obs n).comp hgm
  measurable_action n := (h.measurable_action n).comp hgm
  measurable_feedback n := (h.measurable_feedback n).comp hgm
  hasCondDistrib_obs n := (h.hasCondDistrib_obs n).comp_hasLaw hg
  hasCondDistrib_action n := (h.hasCondDistrib_action n).comp_hasLaw hg
  hasCondDistrib_feedback n := (h.hasCondDistrib_feedback n).comp_hasLaw hg

/-- A run of an identification algorithm is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IdentAlg.IsRun.comp_hasLaw {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {out : Ω' → 𝓓}
    (h : A.IsRun env O X Y out P') (hg : HasLaw g P' P) (hgm : Measurable g) :
    A.IsRun env (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) (out ∘ g) P where
  isAlgEnvSeq := h.isAlgEnvSeq.comp_hasLaw hg hgm
  hasCondDistrib_output := h.hasCondDistrib_output.comp_hasLaw hg

end transport

/-- The history of the first `T` rounds of a trajectory `ℕ → Round 𝓞 𝓐 𝓨` is measurable. -/
lemma measurable_history_traj (T : ℕ) :
    Measurable (history (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action IT.feedback T) :=
  measurable_history IT.measurable_obs IT.measurable_action IT.measurable_feedback T

namespace IdentAlg

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨)

/-- The history at the stopping time of `A`, as a function of the trajectory
`ℕ → Round 𝓞 𝓐 𝓨`, is measurable. -/
lemma measurable_stoppedHist_traj :
    Measurable (A.stoppedHist (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action IT.feedback) :=
  measurable_stoppedValue_sigmaHistory IT.measurable_obs IT.measurable_action
    IT.measurable_feedback (measurable_hittingAfter_sigmaHistory IT.measurable_obs
      IT.measurable_action IT.measurable_feedback A.measurableSet_stopSet)

/-- The canonical probability space of a run of `A` in the environment `env`: the trajectory
`ℕ → Round 𝓞 𝓐 𝓨` has the law `trajMeasure A.alg env` and, given the trajectory, the output is
drawn from the output rule applied to the history at the stopping time. -/
noncomputable def runMeasure : Measure ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓓) :=
  trajMeasure A.alg env ⊗ₘ
    A.output.comap (A.stoppedHist IT.obs IT.action IT.feedback) A.measurable_stoppedHist_traj
deriving IsProbabilityMeasure

/-- Every identification algorithm has a run in every environment: the canonical run on
`runMeasure`. -/
lemma isRun_runMeasure :
    A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1) (fun n ω ↦ IT.feedback n ω.1)
      Prod.snd (A.runMeasure env) where
  isAlgEnvSeq := (IT.isAlgEnvSeq_trajMeasure A.alg env).comp_hasLaw
    ⟨measurable_fst.aemeasurable, Measure.fst_compProd _ _⟩ measurable_fst
  hasCondDistrib_output :=
    hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) A.output
      A.measurable_stoppedHist_traj fun _ ↦ inferInstance

/-- The law of the output of the canonical run is `A.outputMeasure env`. -/
lemma map_snd_runMeasure : (A.runMeasure env).map Prod.snd = A.outputMeasure env :=
  (A.isRun_runMeasure env).hasLaw_output.map_eq

variable {A env}

/-- **PAC from a bound on every run.** To prove that `A` is PAC at level `δ` it suffices to
bound by `δ` the probability of a bad output for every run of `A` on a probability space in the
universe of the canonical run `runMeasure` (the converse, for runs in any universe, is
`IsPAC.measureReal_bad_of_isRun`). -/
lemma IsPAC.of_forall_isRun {𝓞 : Type u} {𝓐 : Type v} {𝓨 : Type w} {𝓓 : Type z}
    {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
    {m𝓓 : MeasurableSpace 𝓓} {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {Θ : Type*} {env : Θ → Environment 𝓞 𝓐 𝓨}
    {bad : Θ → 𝓓 → Prop} {δ : ℝ} (hbad : ∀ θ, MeasurableSet {d | bad θ d})
    (h : ∀ θ, ∀ {Ω : Type (max u v w z)} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓓),
      A.IsRun (env θ) O X Y out P → P.real {ω | bad θ (out ω)} ≤ δ) :
    A.IsPAC env bad δ := by
  intro θ
  have hrun := A.isRun_runMeasure (env θ)
  rw [← hrun.hasLaw_output.measureReal_eq (hbad θ)]
  exact h θ _ _ _ _ _ hrun

end IdentAlg

end Learning
