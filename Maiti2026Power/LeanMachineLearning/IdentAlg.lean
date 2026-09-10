/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.StoppedHistory
public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# Identification algorithms: sampling rule, stopping rule, output rule

An *identification algorithm* with outputs in `𝓞` is an LML sampling rule
`alg : Algorithm Unit 𝓐 𝓨` (an algorithm without observations: LML's observation type is `Unit`,
and `𝓞` denotes here the type of *outputs*) together with

* a *stopping rule*: `stop n h` says that the algorithm stops after `n` rounds when the history
  of these rounds is `h : Hist Unit 𝓐 𝓨 n` (each `{h | stop n h}` is measurable);
* an *output rule*: for each `n`, a kernel `output n` from histories of length `n` to `𝓞`, which is
  a probability measure on every history at which the algorithm stops.

A *run* of the algorithm in an environment `env`, on a probability space `(Ω, P)`, consists of
observation, action and feedback processes `O, X, Y` (with `O` trivially `Unit`-valued) forming an
algorithm-environment sequence for `alg` and `env` (LML `IsAlgEnvSeq`) and an output `out : Ω → 𝓞`
whose conditional law given the history at the
stopping time is the output rule (`IdentAlg.IsRun`). The stopping time `IdentAlg.stoppingTime`
is the stopping time `Learning.stoppingTime` of the stopping rule `A.stopSet` (the hitting time,
Mathlib `hittingAfter`, of the stopping rule by the process of histories), a stopping time of
the history filtration, and the history at the stopping time is `Learning.stoppedHist`.

Examples: best-arm identification (`𝓞 = 𝓐`, output = recommended arm), hypothesis tests
(`𝓞 = Bool`), estimation (`𝓞 = ℝ`).

A *fixed-budget* algorithm is the special case where the stopping rule is "stop after exactly
`T` rounds" (`IsFixedBudget A T`; constructor `fixedBudget alg T ρ`); a *fixed-confidence*
algorithm stops adaptively.

## Main definitions

* `IdentAlg 𝓐 𝓨 𝓞`: the structure.
* `IdentAlg.stoppingTime A O X Y : Ω → ℕ∞`: the number of rounds played, a hitting time.
* `IdentAlg.stoppedHist A O X Y : Ω → Σ n, Hist Unit 𝓐 𝓨 n`: the history at the stopping time.
* `IdentAlg.IsRun A env O X Y out P`: `(O, X, Y, out)` is a run of `A` in `env` on `(Ω, P)`.
* `IdentAlg.IsPAC A env good δ`: for every parameter `θ` of the family `env θ` of environments
  and every run of `A` in `env θ`, the output is `good θ` with probability at least `1 - δ`.
* `IdentAlg.IsFixedBudget A T`, `IdentAlg.fixedBudget alg T ρ`: fixed-budget algorithms.
* `fixedDesignAlg x`: the deterministic algorithm playing the sequence `x` whatever the
  observations; `IdentAlg.IsFixedDesign A` says that the sampling rule of `A` is of this form.

Time is `0`-indexed: after `n` rounds the actions `a_0, …, a_{n-1}` have been played.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENat

universe u

namespace Learning

variable {𝓐 𝓨 𝓞 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The deterministic algorithm that plays the fixed sequence `x : ℕ → 𝓐` regardless of the
observations (a *fixed design*). -/
noncomputable def fixedDesignAlg (x : ℕ → 𝓐) : Algorithm Unit 𝓐 𝓨 :=
  detAlgorithm (fun n _ ↦ x n) fun _ ↦ measurable_const

/-- An identification algorithm with outputs in `𝓞`: a sampling rule `alg`, a stopping rule
`stop` (`stop n h`: stop after `n` rounds when their history is `h`) and an output rule `output`
(the distribution of the output given the history of the `n` rounds played), which is a
probability measure on every history at which the algorithm stops. -/
structure IdentAlg (𝓐 𝓨 𝓞 : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    [MeasurableSpace 𝓞] where
  /-- The sampling rule. -/
  alg : Algorithm Unit 𝓐 𝓨
  /-- The stopping rule: `stop n h` means that the algorithm stops after `n` rounds when the
  history of these rounds is `h`. -/
  stop : (n : ℕ) → Hist Unit 𝓐 𝓨 n → Prop
  /-- The stopping rule is measurable. -/
  measurableSet_stop : ∀ n, MeasurableSet {h | stop n h}
  /-- The output rule: distribution of the output given the history of the `n` rounds played. -/
  output : (n : ℕ) → Kernel (Hist Unit 𝓐 𝓨 n) 𝓞
  /-- The output kernels are s-finite (so that the joint law of history and output is a
  composition-product). -/
  [isSFiniteKernel_output : ∀ n, IsSFiniteKernel (output n)]
  /-- The output rule is a probability measure on every history at which the algorithm stops. -/
  [isProbabilityMeasure_output : ∀ n h, stop n h → IsProbabilityMeasure (output n h)]

namespace IdentAlg

variable (A : IdentAlg 𝓐 𝓨 𝓞) (O : ℕ → Ω → Unit) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)

instance (n : ℕ) : IsSFiniteKernel (A.output n) := A.isSFiniteKernel_output n

/-- The stopping rule of `A` as a set of histories of variable length. -/
def stopSet : Set (Σ n : ℕ, Hist Unit 𝓐 𝓨 n) := {h | A.stop h.1 h.2}

/-- The stopping time of `A` on the observation, action and feedback processes `O`, `X`, `Y`: the
number of rounds
played, that is the first `n` such that the stopping rule fires on the history of the first `n`
rounds (`⊤` if it never does). It is the stopping time `Learning.stoppingTime` of the stopping
rule `A.stopSet`. -/
noncomputable def stoppingTime : Ω → ℕ∞ := Learning.stoppingTime O X Y A.stopSet

lemma stoppingTime_def : A.stoppingTime O X Y = Learning.stoppingTime O X Y A.stopSet := rfl

lemma measurableSet_stopSet : MeasurableSet A.stopSet :=
  measurableSet_sigma_iff.2 A.measurableSet_stop

/-- The stopping time of an identification algorithm is a stopping time of the history
filtration of any algorithm-environment sequence `X`, `Y`. -/
lemma isStoppingTime_stoppingTime {alg : Algorithm Unit 𝓐 𝓨} {env : Environment Unit 𝓐 𝓨}
    {P : Measure Ω} [IsFiniteMeasure P] (h : IsAlgEnvSeq O X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime O X Y) :=
  h.isStoppingTime_stoppingTime A.measurableSet_stopSet

/-- The history of the rounds played by `A`, as a history of variable length (of length `0` if
`A` never stops): the history stopped at `A.stoppingTime O X Y`. -/
noncomputable def stoppedHist : Ω → Σ n : ℕ, Hist Unit 𝓐 𝓨 n :=
  Learning.stoppedHist O X Y (A.stoppingTime O X Y)

lemma stoppedHist_def :
    A.stoppedHist O X Y = Learning.stoppedHist O X Y (A.stoppingTime O X Y) := rfl

/-- When the stopping time is finite, the history at the stopping time belongs to the stopping
rule. -/
lemma stoppedHist_mem_stopSet_of_ne_top {ω : Ω} (h : A.stoppingTime O X Y ω ≠ ⊤) :
    A.stoppedHist O X Y ω ∈ A.stopSet :=
  Learning.stoppedHist_mem_of_ne_top h

/-- The output rule of `A` as a single kernel on histories of variable length. -/
noncomputable def outputKernel : Kernel (Σ n : ℕ, Hist Unit 𝓐 𝓨 n) 𝓞 where
  toFun h := A.output h.1 h.2
  measurable' := measurable_sigma_of_measurable_comp_mk fun n ↦ (A.output n).measurable

section extendKernel

variable {A}

/-- A kernel `κ` on histories of length `n`, extended by zero to histories of variable length. -/
noncomputable def extendKernel (n : ℕ) (κ : Kernel (Hist Unit 𝓐 𝓨 n) 𝓞) :
    Kernel (Σ n : ℕ, Hist Unit 𝓐 𝓨 n) 𝓞 where
  toFun h := if hn : h.1 = n then κ (fun i ↦ h.2 (Fin.cast hn.symm i)) else 0
  measurable' := by
    refine measurable_sigma_of_measurable_comp_mk fun m ↦ ?_
    by_cases hm : m = n
    · subst hm
      simpa [Function.comp_def] using κ.measurable
    · simp [Function.comp_def, hm]

lemma extendKernel_apply (n : ℕ) (κ : Kernel (Hist Unit 𝓐 𝓨 n) 𝓞) (h : Σ n : ℕ, Hist Unit 𝓐 𝓨 n) :
    extendKernel n κ h = if hn : h.1 = n then κ (fun i ↦ h.2 (Fin.cast hn.symm i)) else 0 := rfl

instance (n : ℕ) (κ : Kernel (Hist Unit 𝓐 𝓨 n) 𝓞) [IsFiniteKernel κ] :
    IsFiniteKernel (extendKernel n κ) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun h ↦ ?_⟩⟩
  rw [extendKernel_apply]
  split_ifs
  · exact κ.measure_le_bound _ _
  · simp

lemma extendKernel_sum (n : ℕ) {ι : Type*} [Countable ι] (κs : ι → Kernel (Hist Unit 𝓐 𝓨 n) 𝓞) :
    extendKernel n (Kernel.sum κs) = Kernel.sum fun i ↦ extendKernel n (κs i) := by
  ext h s hs
  rw [Kernel.sum_apply' _ _ hs, extendKernel_apply]
  split_ifs with hn
  · rw [Kernel.sum_apply' _ _ hs]
    simp [extendKernel_apply, hn]
  · simp [extendKernel_apply, hn]

instance (n : ℕ) (κ : Kernel (Hist Unit 𝓐 𝓨 n) 𝓞) [IsSFiniteKernel κ] :
    IsSFiniteKernel (extendKernel n κ) := by
  rw [← Kernel.kernel_sum_seq κ, extendKernel_sum]
  infer_instance

end extendKernel

/-- The output kernel is the sum over `n` of the output rules at length `n`, extended by zero. -/
lemma outputKernel_eq_sum : A.outputKernel = Kernel.sum fun n ↦ extendKernel n (A.output n) := by
  ext h s hs
  rw [Kernel.sum_apply' _ _ hs, tsum_eq_single h.1 fun n hn ↦ by simp [extendKernel_apply, hn.symm]]
  simp [outputKernel, extendKernel_apply]

instance : IsSFiniteKernel A.outputKernel := by
  rw [outputKernel_eq_sum]
  infer_instance

/-- `(O, X, Y, out)` is a *run* of the identification algorithm `A` in the environment `env` on
the probability space `(Ω, P)`: the observation, action and feedback processes `O`, `X`, `Y` form
an algorithm-environment sequence for the sampling rule `A.alg` and `env`, and the output `out` has
conditional law `A.output` given the history at the stopping time. -/
structure IsRun (env : Environment Unit 𝓐 𝓨) (O : ℕ → Ω → Unit) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (out : Ω → 𝓞) (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  /-- The actions and feedbacks are generated by the sampling rule in the environment. -/
  isAlgEnvSeq : IsAlgEnvSeq O X Y A.alg env P
  /-- The output is drawn from the output rule applied to the history at the stopping time. -/
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist O X Y) A.outputKernel P

/-- `A` is *PAC at level `δ`* for the family of environments `env : Θ → Environment Unit 𝓐 𝓨` and
the goodness predicate `good : Θ → 𝓞 → Prop` if, for every `θ` and every run of `A` in `env θ` on
a probability space `(Ω, P)`, the output is `good θ` with probability at least `1 - δ`. -/
def IsPAC {Θ : Type*} (env : Θ → Environment Unit 𝓐 𝓨) (good : Θ → 𝓞 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (O : ℕ → Ω → Unit) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓞),
    A.IsRun (env θ) O X Y out P →
    1 - δ ≤ P.real {ω | good θ (out ω)}

/-- `A` is a *fixed-budget* algorithm with budget `T` if its stopping rule is "stop after exactly
`T` rounds". -/
def IsFixedBudget (T : ℕ) : Prop := A.stop = fun n _ ↦ n = T

/-- An identification algorithm is a *fixed-design* (non-adaptive) algorithm if its sampling
rule plays a fixed sequence of actions; its output rule is arbitrary. -/
def IsFixedDesign : Prop := ∃ x : ℕ → 𝓐, A.alg = fixedDesignAlg x

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on histories of length `T`. -/
noncomputable def fixedBudget (alg : Algorithm Unit 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist Unit 𝓐 𝓨 T) 𝓞) [IsMarkovKernel ρ] : IdentAlg 𝓐 𝓨 𝓞 where
  alg := alg
  stop n _ := n = T
  measurableSet_stop n := by by_cases h : n = T <;> simp [h]
  output n := if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop) else 0
  isSFiniteKernel_output n := by
    by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance
  isProbabilityMeasure_output n h hn := by
    simp only [hn, ↓reduceDIte, Kernel.coe_comap, Function.comp_apply]
    infer_instance

lemma isFixedBudget_fixedBudget (alg : Algorithm Unit 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist Unit 𝓐 𝓨 T) 𝓞) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).IsFixedBudget T := rfl

/-- The output rule of `fixedBudget alg T ρ` at the budget `T` is `ρ`. -/
lemma output_fixedBudget (alg : Algorithm Unit 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist Unit 𝓐 𝓨 T) 𝓞) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).output T = ρ := by
  change (if h : T = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop) else 0) = ρ
  simp only [↓reduceDIte, Fin.cast_eq_self]
  ext y u _
  simp

end IdentAlg

end Learning
