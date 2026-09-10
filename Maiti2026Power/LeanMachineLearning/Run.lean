/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.FixedBudget
public import Maiti2026Power.Mathlib.Probability.CondDistrib
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# Transport and existence of runs of identification algorithms

* Algorithm-environment sequences and runs can be transported along a map `g : Ω → Ω'` carrying
  `P` to `P'`: if `(O, X, Y, out)` is a run on `(Ω', P')` then `(O ∘ g, X ∘ g, Y ∘ g, out ∘ g)` is a
  run on `(Ω, P)` (`IsAlgEnvSeq.comp_hasLaw`, `IdentAlg.IsRun.comp_hasLaw`).
* A run of a fixed-budget identification algorithm `A` with budget `T` in any environment exists,
  on the space `(ℕ → Round Unit 𝓐 𝓨) × 𝓞` of (trajectory, output) pairs: the trajectory has the
  law `trajMeasure A.alg env` of the Ionescu-Tulcea construction and the output is drawn from the
  output rule applied to the history of the first `T` rounds
  (`IdentAlg.fixedBudgetRunMeasure`, `IdentAlg.IsFixedBudget.isRun_fixedBudgetRunMeasure`).
  This is the reason why the PAC property `IdentAlg.IsPAC` may be quantified over probability
  spaces in the universe of `(ℕ → Round Unit 𝓐 𝓨) × 𝓞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 𝓞 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {g : Ω → Ω'}

section transport

variable {𝓩 : Type*} {m𝓩 : MeasurableSpace 𝓩} {alg : Algorithm 𝓩 𝓐 𝓨} {env : Environment 𝓩 𝓐 𝓨}
  {O : ℕ → Ω' → 𝓩} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨}

/-- An algorithm-environment sequence (with observations in an arbitrary type `𝓩`) is transported
along a measurable map `g` carrying `P` to `P'`. -/
lemma IsAlgEnvSeq.comp_hasLaw (h : IsAlgEnvSeq O X Y alg env P') (hg : HasLaw g P' P)
    (hgm : Measurable g) :
    IsAlgEnvSeq (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) alg env P where
  measurable_obs n := (h.measurable_obs n).comp hgm
  measurable_action n := (h.measurable_action n).comp hgm
  measurable_feedback n := (h.measurable_feedback n).comp hgm
  hasCondDistrib_obs n := (h.hasCondDistrib_obs n).comp_hasLaw hg
  hasCondDistrib_action n := (h.hasCondDistrib_action n).comp_hasLaw hg
  hasCondDistrib_feedback n := (h.hasCondDistrib_feedback n).comp_hasLaw hg

end transport

/-- A run of an identification algorithm is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IdentAlg.IsRun.comp_hasLaw {A : IdentAlg 𝓐 𝓨 𝓞} {env : Environment Unit 𝓐 𝓨}
    {O : ℕ → Ω' → Unit} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨} {out : Ω' → 𝓞}
    (h : A.IsRun env O X Y out P') (hg : HasLaw g P' P) (hgm : Measurable g) :
    A.IsRun env (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) (out ∘ g) P where
  isAlgEnvSeq := h.isAlgEnvSeq.comp_hasLaw hg hgm
  hasCondDistrib_output := h.hasCondDistrib_output.comp_hasLaw hg

namespace IdentAlg

variable (A : IdentAlg 𝓐 𝓨 𝓞) (env : Environment Unit 𝓐 𝓨) (T : ℕ)

/-- The history of the first `T` rounds of a trajectory `h : ℕ → Round Unit 𝓐 𝓨` is
measurable. -/
lemma measurable_history_traj :
    Measurable (history (IT.obs (𝓞 := Unit) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action IT.feedback T) := by
  unfold history
  fun_prop

/-- The output rule of a fixed-budget algorithm at its budget is a Markov kernel. -/
lemma IsFixedBudget.isMarkovKernel_output {A : IdentAlg 𝓐 𝓨 𝓞} {T : ℕ} (hA : A.IsFixedBudget T) :
    IsMarkovKernel (A.output T) :=
  ⟨fun h ↦ A.isProbabilityMeasure_output T h (by unfold IsFixedBudget at hA; simp [hA])⟩

/-- The canonical probability space of a run of the fixed-budget algorithm `A` (budget `T`) in
the environment `env`: the trajectory `ℕ → Round Unit 𝓐 𝓨` has the law `trajMeasure A.alg env`
and, given the trajectory, the output is drawn from `A.output T` applied to the history of the
first `T` rounds. -/
noncomputable def fixedBudgetRunMeasure : Measure ((ℕ → Round Unit 𝓐 𝓨) × 𝓞) :=
  trajMeasure A.alg env ⊗ₘ (A.output T).comap (history IT.obs IT.action IT.feedback T)
    (measurable_history_traj T)

instance [IsMarkovKernel (A.output T)] : IsProbabilityMeasure (A.fixedBudgetRunMeasure env T) := by
  unfold fixedBudgetRunMeasure
  infer_instance

variable {A T}

/-- A fixed-budget identification algorithm has a run in every environment: the canonical run on
`fixedBudgetRunMeasure` (the instance `IsMarkovKernel (A.output T)` is
`IsFixedBudget.isMarkovKernel_output`). -/
lemma IsFixedBudget.isRun_fixedBudgetRunMeasure (hA : A.IsFixedBudget T)
    [IsMarkovKernel (A.output T)] :
    A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1) (fun n ω ↦ IT.feedback n ω.1)
      Prod.snd (A.fixedBudgetRunMeasure env T) := by
  have hprob : ∀ h : ℕ → Round Unit 𝓐 𝓨,
      IsProbabilityMeasure (A.outputKernel ⟨T, history IT.obs IT.action IT.feedback T h⟩) :=
    fun h ↦ A.isProbabilityMeasure_output T _ (by unfold IsFixedBudget at hA; simp [hA])
  have hfst : HasLaw Prod.fst (trajMeasure A.alg env) (A.fixedBudgetRunMeasure env T) :=
    ⟨measurable_fst.aemeasurable, Measure.fst_compProd _ _⟩
  refine ⟨(IT.isAlgEnvSeq_trajMeasure A.alg env).comp_hasLaw hfst measurable_fst, ?_⟩
  have hsh : A.stoppedHist (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1)
      (fun n ω ↦ IT.feedback n ω.1) =
      fun p : (ℕ → Round Unit 𝓐 𝓨) × 𝓞 ↦
        (⟨T, history IT.obs IT.action IT.feedback T p.1⟩ : Σ n, Hist Unit 𝓐 𝓨 n) :=
    funext fun p ↦ hA.stoppedHist_eq p
  rw [hsh]
  exact hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) A.outputKernel
    ((measurable_sigma_mk T).comp (measurable_history_traj T)) hprob

end IdentAlg

end Learning
