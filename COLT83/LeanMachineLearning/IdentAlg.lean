/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.MeasureTheory.MeasurableSpace.Sigma
public import LeanMachineLearning.SequentialLearning.Deterministic
public import Mathlib.Probability.Process.HittingTime

/-!
# Identification algorithms: sampling rule, stopping rule, output rule

An *identification algorithm* with outputs in `𝓞` is an LML sampling rule `alg : Algorithm 𝓐 𝓨`
together with

* a *stopping rule*: `stop n h` says that the algorithm stops after `n` rounds when the history
  of these rounds is `h : Fin n → 𝓐 × 𝓨` (each `{h | stop n h}` is measurable);
* an *output rule*: for each `n`, a kernel `output n` from histories of length `n` to `𝓞`, which is
  a probability measure on every history at which the algorithm stops.

A *run* of the algorithm in an environment `env`, on a probability space `(Ω, P)`, consists of
action and feedback processes `X, Y` forming an algorithm-environment sequence for `alg` and `env`
(LML `IsAlgEnvSeq`) and an output `out : Ω → 𝓞` whose conditional law given the history at the
stopping time is the output rule (`IdentAlg.IsRun`). The stopping time `IdentAlg.stoppingTime`
is the hitting time (Mathlib `hittingAfter`) of the stopping rule by the process of histories,
a stopping time of the history filtration.

Examples: best-arm identification (`𝓞 = 𝓐`, output = recommended arm), hypothesis tests
(`𝓞 = Bool`), estimation (`𝓞 = ℝ`).

A *fixed-budget* algorithm is the special case where the stopping rule is "stop after exactly
`T` rounds" (`IsFixedBudget A T`; constructor `fixedBudget alg T ρ`); a *fixed-confidence*
algorithm stops adaptively.

## Main definitions

* `IdentAlg 𝓐 𝓨 𝓞`: the structure.
* `IdentAlg.stoppingTime A X Y : Ω → ℕ∞`: the number of rounds played, a hitting time.
* `IdentAlg.stoppedHist A X Y : Ω → Σ n, (Fin n → 𝓐 × 𝓨)`: the history at the stopping time.
* `IdentAlg.IsRun A env X Y out P`: `(X, Y, out)` is a run of `A` in `env` on `(Ω, P)`.
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

/-- The history of the first `n` rounds of the action and feedback processes `X`, `Y`. -/
def finHistory (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) : Fin n → 𝓐 × 𝓨 :=
  fun i ↦ (X i ω, Y i ω)

/-- The deterministic algorithm that plays the fixed sequence `x : ℕ → 𝓐` regardless of the
observations (a *fixed design*). -/
noncomputable def fixedDesignAlg (x : ℕ → 𝓐) : Algorithm 𝓐 𝓨 :=
  detAlgorithm (fun n _ ↦ x (n + 1)) (fun _ ↦ measurable_const) (x 0)

/-- An identification algorithm with outputs in `𝓞`: a sampling rule `alg`, a stopping rule
`stop` (`stop n h`: stop after `n` rounds when their history is `h`) and an output rule `output`
(the distribution of the output given the history of the `n` rounds played), which is a
probability measure on every history at which the algorithm stops. -/
structure IdentAlg (𝓐 𝓨 𝓞 : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    [MeasurableSpace 𝓞] where
  /-- The sampling rule. -/
  alg : Algorithm 𝓐 𝓨
  /-- The stopping rule: `stop n h` means that the algorithm stops after `n` rounds when the
  history of these rounds is `h`. -/
  stop : (n : ℕ) → (Fin n → 𝓐 × 𝓨) → Prop
  /-- The stopping rule is measurable. -/
  measurableSet_stop : ∀ n, MeasurableSet {h | stop n h}
  /-- The output rule: distribution of the output given the history of the `n` rounds played. -/
  output : (n : ℕ) → Kernel (Fin n → 𝓐 × 𝓨) 𝓞
  /-- The output kernels are s-finite (so that the joint law of history and output is a
  composition-product). -/
  [isSFiniteKernel_output : ∀ n, IsSFiniteKernel (output n)]
  /-- The output rule is a probability measure on every history at which the algorithm stops. -/
  [isProbabilityMeasure_output : ∀ n h, stop n h → IsProbabilityMeasure (output n h)]

namespace IdentAlg

variable (A : IdentAlg 𝓐 𝓨 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)

instance (n : ℕ) : IsSFiniteKernel (A.output n) := A.isSFiniteKernel_output n

/-- The stopping rule of `A` as a set of histories of variable length. -/
def stopSet : Set (Σ n : ℕ, (Fin n → 𝓐 × 𝓨)) := {h | A.stop h.1 h.2}

/-- The stopping time of `A` on the action and feedback processes `X`, `Y`: the number of rounds
played, that is the first `n` such that the stopping rule fires on the history of the first `n`
rounds (`⊤` if it never does). It is the hitting time of `stopSet` by the process
`n ↦ ⟨n, finHistory X Y n⟩` of histories. -/
noncomputable def stoppingTime : Ω → ℕ∞ :=
  hittingAfter (fun n ω ↦ (⟨n, finHistory X Y n ω⟩ : Σ n : ℕ, (Fin n → 𝓐 × 𝓨))) A.stopSet 0

lemma measurableSet_stopSet : MeasurableSet A.stopSet :=
  measurableSet_sigma_iff.2 A.measurableSet_stop

omit m𝓐 m𝓨 in
/-- The history of the first `n` rounds is a function of the history up to time `n`. -/
lemma finHistory_eq_comp_history (n : ℕ) :
    finHistory X Y n =
      (fun h : Finset.Iic n → 𝓐 × 𝓨 ↦ fun i : Fin n ↦ h ⟨i, Finset.mem_Iic.2 i.2.le⟩) ∘
        history X Y n := rfl

lemma adapted_finHistory {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}
    {P : Measure Ω} [IsFiniteMeasure P] (h : IsAlgEnvSeq X Y alg env P) :
    Adapted h.filtration (fun n ω ↦ (⟨n, finHistory X Y n ω⟩ : Σ n : ℕ, (Fin n → 𝓐 × 𝓨))) := by
  refine fun n ↦ (measurable_sigma_mk n).comp ?_
  rw [finHistory_eq_comp_history]
  exact measurable_comp_comap _ (by fun_prop)

/-- The stopping time of an identification algorithm is a stopping time of the history
filtration of any algorithm-environment sequence `X`, `Y`. -/
lemma isStoppingTime_stoppingTime {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}
    {P : Measure Ω} [IsFiniteMeasure P] (h : IsAlgEnvSeq X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime X Y) :=
  (adapted_finHistory _ _ h).isStoppingTime_hittingAfter A.measurableSet_stopSet

/-- The history of the rounds played by `A`, as a history of variable length (of length `0` if
`A` never stops). -/
noncomputable def stoppedHist (ω : Ω) : Σ n : ℕ, (Fin n → 𝓐 × 𝓨) :=
  ⟨(A.stoppingTime X Y ω).toNat, finHistory X Y _ ω⟩

/-- The output rule of `A` as a single kernel on histories of variable length. -/
noncomputable def outputKernel : Kernel (Σ n : ℕ, (Fin n → 𝓐 × 𝓨)) 𝓞 where
  toFun h := A.output h.1 h.2
  measurable' := measurable_sigma_of_measurable_comp_mk fun n ↦ (A.output n).measurable

section extendKernel

variable {A}

/-- A kernel `κ` on histories of length `n`, extended by zero to histories of variable length. -/
noncomputable def extendKernel (n : ℕ) (κ : Kernel (Fin n → 𝓐 × 𝓨) 𝓞) :
    Kernel (Σ n : ℕ, (Fin n → 𝓐 × 𝓨)) 𝓞 where
  toFun h := if hn : h.1 = n then κ (fun i ↦ h.2 (Fin.cast hn.symm i)) else 0
  measurable' := by
    refine measurable_sigma_of_measurable_comp_mk fun m ↦ ?_
    by_cases hm : m = n
    · subst hm
      simpa [Function.comp_def] using κ.measurable
    · simp [Function.comp_def, hm]

lemma extendKernel_apply (n : ℕ) (κ : Kernel (Fin n → 𝓐 × 𝓨) 𝓞) (h : Σ n : ℕ, (Fin n → 𝓐 × 𝓨)) :
    extendKernel n κ h = if hn : h.1 = n then κ (fun i ↦ h.2 (Fin.cast hn.symm i)) else 0 := rfl

instance (n : ℕ) (κ : Kernel (Fin n → 𝓐 × 𝓨) 𝓞) [IsFiniteKernel κ] :
    IsFiniteKernel (extendKernel n κ) := by
  refine ⟨⟨κ.bound, κ.bound_lt_top, fun h ↦ ?_⟩⟩
  rw [extendKernel_apply]
  split_ifs
  · exact κ.measure_le_bound _ _
  · simp

lemma extendKernel_sum (n : ℕ) {ι : Type*} [Countable ι] (κs : ι → Kernel (Fin n → 𝓐 × 𝓨) 𝓞) :
    extendKernel n (Kernel.sum κs) = Kernel.sum fun i ↦ extendKernel n (κs i) := by
  ext h s hs
  rw [Kernel.sum_apply' _ _ hs, extendKernel_apply]
  split_ifs with hn
  · rw [Kernel.sum_apply' _ _ hs]
    simp [extendKernel_apply, hn]
  · simp [extendKernel_apply, hn]

instance (n : ℕ) (κ : Kernel (Fin n → 𝓐 × 𝓨) 𝓞) [IsSFiniteKernel κ] :
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

/-- `(X, Y, out)` is a *run* of the identification algorithm `A` in the environment `env` on the
probability space `(Ω, P)`: the action and feedback processes `X`, `Y` form an
algorithm-environment sequence for the sampling rule `A.alg` and `env`, and the output `out` has
conditional law `A.output` given the history at the stopping time. -/
structure IsRun (env : Environment 𝓐 𝓨) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓞)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  /-- The actions and feedbacks are generated by the sampling rule in the environment. -/
  isAlgEnvSeq : IsAlgEnvSeq X Y A.alg env P
  /-- The output is drawn from the output rule applied to the history at the stopping time. -/
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist X Y) A.outputKernel P

/-- `A` is *PAC at level `δ`* for the family of environments `env : Θ → Environment 𝓐 𝓨` and the
goodness predicate `good : Θ → 𝓞 → Prop` if, for every `θ` and every run of `A` in `env θ` on a
probability space `(Ω, P)`, the output is `good θ` with probability at least `1 - δ`. -/
def IsPAC {Θ : Type*} (env : Θ → Environment 𝓐 𝓨) (good : Θ → 𝓞 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓞), A.IsRun (env θ) X Y out P →
    1 - δ ≤ P.real {ω | good θ (out ω)}

/-- `A` is a *fixed-budget* algorithm with budget `T` if its stopping rule is "stop after exactly
`T` rounds". -/
def IsFixedBudget (T : ℕ) : Prop := A.stop = fun n _ ↦ n = T

/-- An identification algorithm is a *fixed-design* (non-adaptive) algorithm if its sampling
rule plays a fixed sequence of actions; its output rule is arbitrary. -/
def IsFixedDesign : Prop := ∃ x : ℕ → 𝓐, A.alg = fixedDesignAlg x

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on histories of length `T`. -/
noncomputable def fixedBudget (alg : Algorithm 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Fin T → 𝓐 × 𝓨) 𝓞) [IsMarkovKernel ρ] : IdentAlg 𝓐 𝓨 𝓞 where
  alg := alg
  stop n _ := n = T
  measurableSet_stop n := by by_cases h : n = T <;> simp [h]
  output n := if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop) else 0
  isSFiniteKernel_output n := by
    by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance
  isProbabilityMeasure_output n h hn := by
    simp only [hn, ↓reduceDIte, Kernel.coe_comap, Function.comp_apply]
    infer_instance

lemma isFixedBudget_fixedBudget (alg : Algorithm 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Fin T → 𝓐 × 𝓨) 𝓞) [IsMarkovKernel ρ] :
    (fixedBudget alg T ρ).IsFixedBudget T := rfl

end IdentAlg

end Learning
