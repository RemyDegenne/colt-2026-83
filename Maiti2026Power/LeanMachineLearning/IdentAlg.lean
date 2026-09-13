/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Sigma
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.IdentificationAlg
public import Maiti2026Power.LeanMachineLearning.StoppedHistory

/-!
# Fixed-budget and fixed-design identification algorithms

An identification algorithm `A : IdentAlg 𝓞 𝓐 𝓨 𝓓` (LML,
`LeanMachineLearning.SequentialLearning.IdentificationAlg`) is a sampling rule `A.alg`, a
stopping rule `A.stopSet` (a measurable set of histories of variable length) and an output rule
`A.output`, a Markov kernel from histories of variable length to `𝓓`. This file specializes it.

* A *fixed-budget* algorithm with budget `T` is one whose stopping rule is "stop after exactly
  `T` rounds" (`IdentAlg.IsFixedBudget A T`); the constructor `IdentAlg.fixedBudget alg T ρ`
  builds one from a sampling rule and an output kernel `ρ` on histories of length `T`, whose
  output rule on histories of length `T` is `ρ` (`output_fixedBudget`; the output rule on other
  lengths, never used, is an arbitrary constant, whence the `[Nonempty 𝓓]` hypothesis).
  In every run of a fixed-budget algorithm the stopping time is `T`
  (`IsFixedBudget.stoppingTime_eq`), the history at the stopping time is the history of the
  first `T` rounds (`IsFixedBudget.stoppedHist_eq`) and the output has conditional law
  `A.output.comap (Sigma.mk T) _`, the output rule on histories of length `T`, given the
  history of the first `T` rounds (`IsRun.hasCondDistrib_output_history`); when that output rule
  is deterministic, the output is that function of the history
  (`IsRun.output_ae_eq_of_output_eq_deterministic`).
* A *fixed-design* (non-adaptive) algorithm is one whose sampling rule plays a fixed sequence of
  actions whatever the observations (`fixedDesignAlg x`, `IdentAlg.IsFixedDesign A`).

The paper's PAC algorithms all have a fixed budget, and its lower bounds are stated for such
budgets; fixed-confidence algorithms, which stop adaptively, are covered by LML's definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

namespace Learning

variable {𝓞 𝓐 𝓨 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The deterministic algorithm that plays the fixed sequence `x : ℕ → 𝓐` regardless of the
observations (a *fixed design*). -/
noncomputable def fixedDesignAlg (x : ℕ → 𝓐) : Algorithm Unit 𝓐 𝓨 :=
  detAlgorithm (fun n _ ↦ x n) fun _ ↦ measurable_const

namespace IdentAlg

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- `A` is a *fixed-budget* algorithm with budget `T` if its stopping rule is "stop after exactly
`T` rounds". -/
def IsFixedBudget (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (T : ℕ) : Prop := A.stopSet = {h | h.1 = T}

/-- An identification algorithm without observations is a *fixed-design* (non-adaptive)
algorithm if its sampling rule plays a fixed sequence of actions; its output rule is
arbitrary. -/
def IsFixedDesign (A : IdentAlg Unit 𝓐 𝓨 𝓓) : Prop := ∃ x : ℕ → 𝓐, A.alg = fixedDesignAlg x

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on histories of length `T` (the output rule on histories of other lengths, never used,
is an arbitrary constant). -/
noncomputable def fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] : IdentAlg 𝓞 𝓐 𝓨 𝓓 where
  alg := alg
  stopSet := {h | h.1 = T}
  measurableSet_stopSet := measurable_sigma_fst (measurableSet_singleton T)
  output := Kernel.sigma fun n ↦
    if h : n = T then ρ.comap (fun (x : Hist 𝓞 𝓐 𝓨 n) i ↦ x (Fin.cast h.symm i)) (by fun_prop)
    else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))
  isMarkovKernel_output := by
    have : ∀ n, IsMarkovKernel (if h : n = T then
        ρ.comap (fun (x : Hist 𝓞 𝓐 𝓨 n) i ↦ x (Fin.cast h.symm i)) (by fun_prop)
        else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))) := fun n ↦ by
      by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance
    infer_instance

lemma isFixedBudget_fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).IsFixedBudget T := rfl

/-- The output rule of `fixedBudget alg T ρ` on histories of length `T` is `ρ`. -/
lemma output_fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).output.comap (Sigma.mk T) (measurable_sigma_mk T) = ρ := by
  rw [show (fixedBudget alg T ρ).output = Kernel.sigma fun n ↦
      if h : n = T then ρ.comap (fun (x : Hist 𝓞 𝓐 𝓨 n) i ↦ x (Fin.cast h.symm i)) (by fun_prop)
      else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓)) from rfl,
    Kernel.comap_sigma_mk]
  simp only [↓reduceDIte, Fin.cast_eq_self]
  ext y u _
  simp

section run

/-- The stopping time of a fixed-budget algorithm with budget `T` is `T`. -/
lemma IsFixedBudget.stoppingTime_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω = T := by
  refine hittingAfter_sigmaHistory_eq_coe_iff.2 ⟨?_, fun j hj hjS ↦ ?_⟩
  · rw [hA]
    rfl
  · rw [hA] at hjS
    exact hj.ne hjS

/-- The history at the stopping time of a fixed-budget algorithm with budget `T` is the history
of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHist_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩ :=
  stoppedValue_sigmaHistory_of_eq (hA.stoppingTime_eq ω)

/-- The stopping time of a fixed-budget algorithm is finite. -/
lemma IsFixedBudget.stoppingTime_ne_top (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω ≠ ⊤ := by
  rw [hA.stoppingTime_eq]
  exact ENat.natCast_ne_top T

variable {P : Measure Ω} [IsProbabilityMeasure P] {out : Ω → 𝓓} {env : Environment 𝓞 𝓐 𝓨}

/-- **The output of a run of a fixed-budget algorithm has conditional law
`A.output.comap (Sigma.mk T) _`, the output rule on histories of length `T`, given the history of
the first `T` rounds.** -/
lemma IsRun.hasCondDistrib_output_history (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) :
    HasCondDistrib out (history O X Y T) (A.output.comap (Sigma.mk T) (measurable_sigma_mk T))
      P := by
  have h1 := h.hasCondDistrib_output
  rw [show A.stoppedHist O X Y = Sigma.mk T ∘ history O X Y T from
    funext hA.stoppedHist_eq] at h1
  exact h1.of_measurableEmbedding_comp_right (measurableEmbedding_sigma_mk T)

/-- For a fixed-budget algorithm whose output rule on histories of length `T` is the
deterministic map `g` of the history, the output of a run is `g` of the history of the first `T`
rounds, almost surely. -/
lemma IsRun.output_ae_eq_of_output_eq_deterministic [MeasurableEq 𝓓] (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) {g : Hist 𝓞 𝓐 𝓨 T → 𝓓} (hg : Measurable g)
    (hout : A.output.comap (Sigma.mk T) (measurable_sigma_mk T) = Kernel.deterministic g hg) :
    out =ᵐ[P] fun ω ↦ g (history O X Y T ω) := by
  have h1 := h.hasCondDistrib_output_history hA
  rw [hout] at h1
  exact ae_eq_of_hasCondDistrib_deterministic hg (h.isAlgEnvSeq.measurable_history T).aemeasurable
    h.hasCondDistrib_output.aemeasurable_snd h1

/-- For a run of a fixed-budget algorithm with budget `0`, the law of the output is the output
rule applied to the empty history. -/
lemma IsRun.map_out_eq_of_isFixedBudget_zero (hA : A.IsFixedBudget 0)
    (h : A.IsRun env O X Y out P) :
    P.map out = A.output ⟨0, Fin.elim0⟩ := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hsh : A.stoppedHist O X Y = fun _ ↦ (⟨0, Fin.elim0⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) := by
    funext ω
    rw [hA.stoppedHist_eq]
    congr
    exact Subsingleton.elim _ _
  have hjoint := h.hasCondDistrib_output.map_eq
  rw [hsh, Measure.map_const, measure_univ, one_smul] at hjoint
  calc P.map out
      = (P.map fun ω ↦ ((⟨0, Fin.elim0⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n), out ω)).map Prod.snd := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
          (aemeasurable_const.prodMk hout)]
        rfl
    _ = (Measure.dirac (⟨0, Fin.elim0⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ⊗ₘ A.output).map Prod.snd := by
        rw [hjoint]
    _ = A.output ⟨0, Fin.elim0⟩ := by
        ext s hs
        rw [Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs),
          lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left (measurable_snd hs))]
        rfl

end run

end IdentAlg

end Learning
