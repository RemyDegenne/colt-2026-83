# Stopping rules, stopping times and identification algorithms: one design for LML

Written on 2026-09-11 after comparing this project's `IdentAlg` (`Maiti2026Power/LeanMachineLearning/IdentAlg.lean`, `StoppedHistory.lean`, `Run.lean`, `FixedBudget.lean`, `RunDivergence.lean`) with the fork in `../LMLPapers/LMLPapers/LeanMachineLearning/IdentAlg.lean` and the six fixed-confidence papers stated on top of it (Garivier2016Optimal, Degenne2019Pure, Degenne2019Non, Essakine2026Tight, Chase2026Tight, MaynardZhang2026Complexity). The two files share the same core text; they differ on four axes, and each repository has something the other lacks. This note records the comparison and fixes the target design, with the shape of every definition, so that the merge can be done in LML once and both projects switch to it.

**Status.** Step 4 below (Markov output kernels in this project) was done on 2026-09-11. Everything else is a proposal.

## 1. What the two forks have

| Axis | colt-2026-83 (this project) | LMLPapers |
|---|---|---|
| Observations | hard-coded `Unit`: `IdentAlg 𝓐 𝓨 𝓞`, where `𝓞` is the *output* type (clashes with LML's observation type name) | general: `IdentAlg 𝓞 𝓐 𝓨 𝓩`; needed by Chase2026Tight, where the expert advice is the observation |
| Output rule | (before 2026-09-11) s-finite kernels, probability measures only on the stop set; `fixedBudget` put the zero kernel off the budget; `extendKernel` plumbing | Markov kernels at every length; `fixedBudget` needs `[Nonempty 𝓩]` |
| Stopping time | general layer `StoppedHistory.lean`: hitting time of any measurable set of variable-length histories, stopped history for any `τ : Ω → ℕ∞`, about forty lemmas (characterizations, measurability, truncation, laws at `min τ M`, conditional laws on `{M < τ}`); `IdentAlg` delegates to it | inlined in `IdentAlg.stoppingTime` and `IdentAlg.stoppedHist`; three lemmas |
| Downstream theory | data processing for runs, change of measure at an a.s. finite stopping time (KL form), existence of the canonical run for fixed budget, transport of runs, `AgreeUntil` | `StopsAS`, `IsDeltaPAC`, `IsDeltaCorrect` with monotonicity lemmas, `outputLaw` through the trajectory measure, `IdentAlg.comap` / `comapPartialFeedback`, threshold stopping rules (`chernoffStop`, `glrtStopOf`) and the specification predicate `IsGLRTRuleOf` |
| Consumers | fixed budget only (the paper's algorithms all have a deterministic budget) | six papers state `E[τ]` as `∫⁻ ω, (τ ω : ℝ≥0∞) ∂P`; all lower bounds on `E[τ]` are `sorry` |

Three further ad-hoc styles live in LMLPapers papers: a raw Mathlib `IsStoppingTime` on the trajectory filtration with `∀ ω, σ ω ≠ ⊤` (MaynardZhang Lemma 6), a plain Mathlib stopping time with `toNat` sums (Chen Lemma 3), and a bounded within-episode index defined by `sInf` (Lee2026Unified `etaAt`). The first two are exactly what the general layer covers; the third is a different object and stays as it is.

LMLPapers pins LML `3ff93c0` ("MeasurableSpace on kernels, algorithms, environments"), this project `565f652`; the former is newer.

## 2. Assessment

* **The s-finite output design had a trap.** A run requires the joint law of (stopped history, output) to be the composition product `P.map stoppedHist ⊗ₘ outputKernel`, a probability measure. If the algorithm fails to stop with positive probability, the stopped history is the empty history and the output kernel there is `output 0 ∅`, which was `0` for `fixedBudget` and for any adaptive algorithm built the same way. No run existed, so `IsPAC` held vacuously. Harmless here (fixed budgets), fatal for fixed-confidence statements. Markov kernels remove the trap: every algorithm has runs, and non-termination is handled explicitly by `StopsAS` and `IsDeltaCorrect`. The only gain of the s-finite variant was avoiding `[Nonempty 𝓩]` in `fixedBudget`, and every use site has a witness anyway (a design `x 0`, an initial state, `ℝ`).
* **The general stopping layer is what LMLPapers is missing.** Garivier Theorem 1 and Remark 2, Essakine Theorem 3 and MaynardZhang Lemma 6 are all "change of measure at a stopping time", which `RunDivergence.lean` proves (`IsRun.klDiv_map_out_le_lintegral`). The layer is already general in the observation type.
* **Both keep the same wart:** the stopped history at `τ = ⊤` is the empty history. So law lemmas carry `∀ᵐ ω ∂P, τ ω ≠ ⊤`, and `IsPAC` alone is not the right property for adaptive algorithms; `IsDeltaCorrect` (stop *and* be correct with probability `1 - δ`) is. An option-valued stopped history would remove the hypotheses but complicate every `HasCondDistrib`; not worth it.
* **Existence of runs is partial on both sides:** fixed budget only here, none in LMLPapers (which has `outputLaw` by `bind`). With Markov kernels and the measurability lemmas of the layer, a canonical run for every algorithm is a two-liner (Section 3.5), and it justifies the universe quantification of `IsPAC` for adaptive algorithms.
* **Expected stopping time.** The run form `∫⁻ ω, (τ ω : ℝ≥0∞) ∂P` is right for theorems; a functional through the trajectory measure with a bridge lemma is needed for statements that quantify over `δ` (Garivier Remark 2 currently existentially quantifies a function `τE`).
* **Combinators.** Five stopping rules in LMLPapers have the shape "a statistic of the folded history exceeds a threshold"; one constructor covers them.

## 3. Target design

Everything below is meant for LML (`SequentialLearning/StoppedHistory.lean`, `SequentialLearning/IdentAlg.lean`, ...), with general observations `𝓞`, actions `𝓐`, feedbacks `𝓨`, outputs `𝓩`. Snippets marked *existing* are the current code (of this project unless said otherwise); the others are the proposed shape.

### 3.1 Stopping rules and stopping times, independent of `IdentAlg` (existing, `StoppedHistory.lean`)

A stopping rule is a measurable set of histories of variable length; its stopping time is a hitting time; the stopped history is defined for any random time.

```lean
/-- The stopping time of the stopping rule `S`: the first `n` such that the history of the
first `n` rounds belongs to `S` (`⊤` if there is none). -/
noncomputable def stoppingTime (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) : Ω → ℕ∞ :=
  hittingAfter (fun n ω ↦ (⟨n, history O X Y n ω⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) S 0

/-- The history of the first `τ ω` rounds (of length `0` if `τ ω = ⊤`). -/
noncomputable def stoppedHist (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (τ : Ω → ℕ∞)
    (ω : Ω) : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  ⟨(τ ω).toNat, history O X Y _ ω⟩
```

The API that the rest of the design consumes:

```lean
lemma stoppingTime_le_iff : stoppingTime O X Y S ω ≤ n ↔ ∃ j ≤ n, ⟨j, history O X Y j ω⟩ ∈ S
lemma stoppingTime_eq_coe_iff : stoppingTime O X Y S ω = n ↔
    ⟨n, history O X Y n ω⟩ ∈ S ∧ ∀ j < n, ⟨j, history O X Y j ω⟩ ∉ S
lemma stoppingTime_eq_top_iff : stoppingTime O X Y S ω = ⊤ ↔ ∀ n, ⟨n, history O X Y n ω⟩ ∉ S
lemma stoppedHist_mem_of_ne_top (h : stoppingTime O X Y S ω ≠ ⊤) :
    stoppedHist O X Y (stoppingTime O X Y S) ω ∈ S
lemma measurable_stoppingTime (hO …) (hX …) (hY …) (hS : MeasurableSet S) :
    Measurable (stoppingTime O X Y S)
lemma measurable_stoppedHist (hO …) (hX …) (hY …) (hτ : Measurable τ) :
    Measurable (stoppedHist O X Y τ)
lemma IsAlgEnvSeq.isStoppingTime_stoppingTime (h : IsAlgEnvSeq O X Y alg env P)
    (hS : MeasurableSet S) : IsStoppingTime h.filtration (stoppingTime O X Y S)
/-- `{n < τ}` is determined by the first `n` rounds. -/
lemma exists_measurableSet_preimage_lt_stoppingTime (hS : MeasurableSet S) (n : ℕ) :
    ∃ B, MeasurableSet B ∧ {ω | (n : ℕ∞) < stoppingTime O X Y S ω} = history O X Y n ⁻¹' B
/-- Truncation to `M` rounds, and the laws of the histories stopped at `min τ M`. -/
def truncHist (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n
lemma map_stoppedHist_min_succ_eq_add (M : ℕ) :
    P.map (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) (M + 1 : ℕ)) =
      (P.restrict {ω | stoppingTime O X Y S ω ≤ M}).map
          (stoppedHist O X Y fun ω ↦ min (stoppingTime O X Y S ω) M) +
        ((P.restrict {ω | (M : ℕ∞) < stoppingTime O X Y S ω}).map (history O X Y M)).map
          (Sigma.mk M)
```

On top of it, `DivergenceDecomposition.lean` gives the chain rule and the divergence decomposition for histories stopped at `min τ M` and at an a.s. finite `τ` (`IsAlgEnvSeq.klDiv_map_stoppedHist_min_stepKernel`, `klDiv_map_stoppedHist_stepKernel`, `klDiv_map_stoppedHist_min_compProd`, `klDiv_map_stoppedHist_compProd`, `klDiv_map_stoppedHist`). These move to LML next to the fixed-horizon versions already upstreamed.

### 3.2 The structure (merged: LMLPapers' shape, general observations, Markov outputs)

```lean
structure IdentAlg (𝓞 𝓐 𝓨 𝓩 : Type*) [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]
    [MeasurableSpace 𝓨] [MeasurableSpace 𝓩] where
  /-- The sampling rule. -/
  alg : Algorithm 𝓞 𝓐 𝓨
  /-- The stopping rule: `stop n h` means that the algorithm stops after `n` rounds when the
  history of these rounds is `h`. -/
  stop : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Prop
  /-- The stopping rule is measurable. -/
  measurableSet_stop : ∀ n, MeasurableSet {h | stop n h}
  /-- The output rule: distribution of the output given the history of the `n` rounds played. -/
  output : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓩
  /-- The output rules are Markov kernels. -/
  [isMarkovKernel_output : ∀ n, IsMarkovKernel (output n)]
```

Bandit problems use `IdentAlg Unit 𝓐 𝓨 𝓩`; this project's `IdentAlg 𝒳 ℝ 𝒳` becomes `IdentAlg Unit 𝒳 ℝ 𝒳`. Keep the fields as they are: a `Prop`-valued `stop` with a separate measurability field is what every concrete algorithm (Chernoff, GLRT, successive elimination, Entropic-BPI) instantiates, and a `Set`-valued or `Bool`-valued variant buys nothing.

### 3.3 Derived objects: delegate to the layer (existing shape of this project)

```lean
namespace IdentAlg

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓩) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)

instance (n : ℕ) : IsMarkovKernel (A.output n) := A.isMarkovKernel_output n

/-- The stopping rule of `A` as a set of histories of variable length. -/
def stopSet : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) := {h | A.stop h.1 h.2}

lemma measurableSet_stopSet : MeasurableSet A.stopSet :=
  measurableSet_sigma_iff.2 A.measurableSet_stop

/-- The number of rounds played: the stopping time of the stopping rule `A.stopSet`. -/
noncomputable def stoppingTime : Ω → ℕ∞ := Learning.stoppingTime O X Y A.stopSet

/-- The history of the rounds played (of length `0` if `A` never stops). -/
noncomputable def stoppedHist : Ω → Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  Learning.stoppedHist O X Y (A.stoppingTime O X Y)

/-- The output rule as a single kernel on histories of variable length. -/
noncomputable def outputKernel : Kernel (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) 𝓩 where
  toFun h := A.output h.1 h.2
  measurable' := measurable_sigma_of_measurable_comp_mk fun n ↦ (A.output n).measurable

instance : IsMarkovKernel A.outputKernel :=
  ⟨fun h ↦ (A.isMarkovKernel_output h.1).isProbabilityMeasure h.2⟩

lemma isStoppingTime_stoppingTime (h : IsAlgEnvSeq O X Y alg env P) :
    IsStoppingTime h.filtration (A.stoppingTime O X Y) :=
  h.isStoppingTime_stoppingTime A.measurableSet_stopSet
```

Every fact about `A.stoppingTime` is then a one-line specialization of the layer (`stoppingTime_eq_coe_iff`, `stoppedHist_mem_of_ne_top`, `measurable_stoppingTime`, ...), instead of the three hand-proved lemmas of LMLPapers.

### 3.4 Runs and the correctness properties

```lean
/-- `(O, X, Y, out)` is a run of `A` in `env` on `(Ω, P)`. -/
structure IsRun (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨)
    (out : Ω → 𝓩) (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  isAlgEnvSeq : IsAlgEnvSeq O X Y A.alg env P
  hasCondDistrib_output : HasCondDistrib out (A.stoppedHist O X Y) A.outputKernel P
```

Because `outputKernel` is Markov, `IsRun` is satisfiable for every algorithm (Section 3.5), and the data-processing identity holds without any finiteness hypothesis:

```lean
lemma IsRun.klDiv_map_stoppedHist_out (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) := by
  rw [h.hasCondDistrib_output.map_eq, h'.hasCondDistrib_output.map_eq]
  exact klDiv_compProd_left _ _ _
```

The correctness vocabulary is LMLPapers', with the universe parameter of this project (justified by the canonical run of Section 3.5):

```lean
/-- PAC at level `δ`: the output is `good θ` with probability at least `1 - δ`. Meaningful on
its own only when `A` stops almost surely (the output of a non-stopping run is drawn from
`output 0` on the empty history). -/
def IsPAC {Θ : Type*} (env : Θ → Environment 𝓞 𝓐 𝓨) (good : Θ → 𝓩 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓩),
    A.IsRun (env θ) O X Y out P → 1 - δ ≤ P.real {ω | good θ (out ω)}

/-- `A` stops almost surely in every run in every `env θ`. -/
def StopsAS {Θ : Type*} (env : Θ → Environment 𝓞 𝓐 𝓨) : Prop :=
  ∀ θ, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (O : ℕ → Ω → 𝓞) (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (out : Ω → 𝓩),
    A.IsRun (env θ) O X Y out P → P.real {ω | A.stoppingTime O X Y ω = ⊤} = 0

/-- `δ`-PAC (Garivier–Kaufmann): PAC at level `δ` and stops almost surely. -/
def IsDeltaPAC … : Prop := A.IsPAC.{u} env good δ ∧ A.StopsAS.{u} env

/-- `δ`-correct (Degenne–Koolen): with probability at least `1 - δ`, `A` stops and its output
is `good θ`. The primary fixed-confidence property: robust to `τ = ⊤`. -/
def IsDeltaCorrect … : Prop :=
  ∀ θ, ∀ {Ω : Type u} … , A.IsRun (env θ) O X Y out P →
    1 - δ ≤ P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ good θ (out ω)}

lemma IsDeltaPAC.isDeltaCorrect : A.IsDeltaPAC.{u} env good δ → A.IsDeltaCorrect.{u} env good δ
lemma IsDeltaCorrect.isPAC : A.IsDeltaCorrect.{u} env good δ → A.IsPAC.{u} env good δ
```

Fixed-budget algorithms (existing, both forks; `[Nonempty 𝓩]` is the price of Markov kernels):

```lean
def IsFixedBudget (T : ℕ) : Prop := A.stop = fun n _ ↦ n = T

noncomputable def fixedBudget [Nonempty 𝓩] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓩) [IsMarkovKernel ρ] : IdentAlg 𝓞 𝓐 𝓨 𝓩 where
  alg := alg
  stop n _ := n = T
  measurableSet_stop n := by by_cases h : n = T <;> simp [h]
  output n := if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
    else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓩))
  isMarkovKernel_output n := by
    by_cases h : n = T <;> simp only [h, ↓reduceDIte] <;> infer_instance

lemma IsFixedBudget.stoppingTime_eq (hA : A.IsFixedBudget T) (ω : Ω) : A.stoppingTime O X Y ω = T
lemma IsFixedBudget.stoppedHist_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩
```

### 3.5 The canonical run, the output law and the expected stopping time (proposed)

The measurability lemmas of the layer make the canonical run available for every algorithm, not only for fixed budgets; `fixedBudgetRunMeasure` becomes the special case `T = τ`.

```lean
/-- The canonical probability space of a run of `A` in `env`: the trajectory has the law
`trajMeasure A.alg env` and, given the trajectory, the output is drawn from the output rule at
the history stopped at the stopping time. -/
noncomputable def runMeasure (A : IdentAlg 𝓞 𝓐 𝓨 𝓩) (env : Environment 𝓞 𝓐 𝓨) :
    Measure ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓩) :=
  trajMeasure A.alg env ⊗ₘ
    A.outputKernel.comap (A.stoppedHist IT.obs IT.action IT.feedback)
      (measurable_stoppedHist (by fun_prop) (by fun_prop) (by fun_prop)
        (measurable_stoppingTime (by fun_prop) (by fun_prop) (by fun_prop)
          A.measurableSet_stopSet))

instance : IsProbabilityMeasure (A.runMeasure env)   -- Markov kernel, hence a probability

lemma isRun_runMeasure (A : IdentAlg 𝓞 𝓐 𝓨 𝓩) (env : Environment 𝓞 𝓐 𝓨) :
    A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1)
      (fun n ω ↦ IT.feedback n ω.1) Prod.snd (A.runMeasure env)

/-- The law of the output (LMLPapers' `outputLaw`, now a projection of the canonical run). -/
noncomputable def outputLaw (env : Environment 𝓞 𝓐 𝓨) : Measure 𝓩 := (A.runMeasure env).map Prod.snd

/-- The expected number of rounds, as a term. -/
noncomputable def expectedStoppingTime (env : Environment 𝓞 𝓐 𝓨) : ℝ≥0∞ :=
  ∫⁻ ω, (A.stoppingTime IT.obs IT.action IT.feedback ω : ℝ≥0∞) ∂trajMeasure A.alg env

/-- Bridge: on every run the expected stopping time is the functional (the law of the
trajectory is `trajMeasure`, LML `IsAlgEnvSeq.hasLaw_trajectory`). -/
lemma IsRun.lintegral_stoppingTime_eq (h : A.IsRun env O X Y out P) :
    ∫⁻ ω, (A.stoppingTime O X Y ω : ℝ≥0∞) ∂P = A.expectedStoppingTime env

lemma IsRun.map_out_eq (h : A.IsRun env O X Y out P) : P.map out = A.outputLaw env
```

Theorems stay in run form (`∀ run, E[τ] ≥ …`, as in Garivier Theorem 1 or Essakine Theorem 3); the functionals are for statements that need a term (Garivier Remark 2's `liminf_{δ → 0} E[τ_δ] / log(1/δ)`, Degenne2023's error probability `errProb`, which already uses `outputLaw`).

### 3.6 Constructors and transport

Threshold stopping rules, which cover `chernoffStop`, `chernoffStopZ`, `glrtStopOf`, `PEGame.gameAlg` and `optimisticTaS` of LMLPapers (all of the form `stop n h := β n < stat (foldHist upd init n h)`):

```lean
/-- Run `alg`; stop after `n` rounds as soon as the statistic `stat n h` of the history exceeds
the threshold `β n`; output from `out n`. -/
noncomputable def thresholdStop (alg : Algorithm 𝓞 𝓐 𝓨) (stat : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → ℝ)
    (hstat : ∀ n, Measurable (stat n)) (β : ℕ → ℝ)
    (out : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓩) [∀ n, IsMarkovKernel (out n)] :
    IdentAlg 𝓞 𝓐 𝓨 𝓩 where
  alg := alg
  stop n h := β n < stat n h
  measurableSet_stop n := measurableSet_lt measurable_const (hstat n)
  output := out

@[simp] lemma stop_thresholdStop_iff : (thresholdStop alg stat hstat β out).stop n h ↔ β n < stat n h
lemma stoppingTime_thresholdStop_le_iff :
    (thresholdStop alg stat hstat β out).stoppingTime O X Y ω ≤ n ↔
      ∃ j ≤ n, β j < stat j (history O X Y j ω)
```

The stateful variant takes `stat n h := f n (foldHist upd init n h)` with `f` measurable in the state, which is how every concrete algorithm is written. Specification predicates such as LMLPapers' `IsGLRTRuleOf alt d β A` ("`A` stops only when a test succeeds and then recommends a passing answer") stay as they are: they are properties of `stop` and `output`, not constructors.

Transport (existing in LMLPapers): the sampling rule, stopping rule and output rule all see the history through history maps.

```lean
noncomputable def comap (A : IdentAlg 𝓞 𝓐 𝓦 𝓩)
    (F : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n × 𝓞 → Hist 𝓞 𝓐 𝓦 n × 𝓞) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Hist 𝓞 𝓐 𝓦 n) (hG : ∀ n, Measurable (G n)) :
    IdentAlg 𝓞 𝓐 𝓨 𝓩 where
  alg := A.alg.comap F hF
  stop n h := A.stop n (G n h)
  measurableSet_stop n := (hG n) (A.measurableSet_stop n)
  output n := (A.output n).comap (G n) (hG n)
```

Transport of runs along a measurable map of the sample space (existing here, `IsRun.comp_hasLaw`) and `Algorithm.AgreeUntil` (existing here, `AlgorithmPrefix.lean`) are unchanged.

### 3.7 Change of measure at a stopping time (existing here, `RunDivergence.lean`)

With the layer and Markov outputs, the standard fixed-confidence lower-bound toolkit is:

```lean
/-- Data processing: outputs are no more distinguishable than stopped histories. -/
lemma IsRun.klDiv_map_out_le_stoppedHist (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y'))

/-- Change of measure at an a.s. finite stopping time, stationary environments `κ`, `κ'`. -/
lemma IsRun.klDiv_map_out_le_lintegral [MeasurableSpace.CountablyGenerated 𝓨]
    (h : A.IsRun (stationaryEnv κ) O X Y out P) (h' : A.IsRun (stationaryEnv κ') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hτ' : ∀ᵐ ω ∂P', A.stoppingTime O' X' Y' ω ≠ ⊤) :
    klDiv (P.map out) (P'.map out') ≤
      ∫⁻ ω, ∑ t ∈ range (A.stoppingTime O X Y ω).toNat, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P
```

Garivier Theorem 1 (`E[τ] ≥ T*(μ) kl(δ, 1 - δ)`) follows from the second lemma, `IsDeltaCorrect` on both environments, and the binary data-processing inequality `kl(P(E), P'(E)) ≤ KL(P ‖ P')`; Remark 2's non-asymptotic form from Bretagnolle–Huber (`Mathlib/InformationTheory/BretagnolleHuber.lean` here). MaynardZhang Lemma 6 (likelihood-ratio form) is the same statement through `EnvDensity.lean`.

## 4. Migration

1. **LML, library layer** (from this project, already general in `𝓞`): `HistoryLaw.lean`, `StoppedHistory.lean` → `SequentialLearning/StoppedHistory.lean`; the stopped `DivergenceDecomposition.lean` next to the fixed-horizon decomposition upstreamed on 2026-09-10. Rebase on LMLPapers' LML commit first (it is the newer one).
2. **LML, `IdentAlg`**: the structure of Section 3.2 with the derived objects of 3.3 (delegation), the properties of 3.4, the canonical run and functionals of 3.5, `thresholdStop` and `comap` of 3.6. Then `Run.lean` (transport), `FixedBudget.lean` (fixed-budget data processing) and `RunDivergence.lean` of this project, generalized to `𝓞`.
3. **LMLPapers**: bump LML, delete the local `IdentAlg.lean` and `PartialFeedback.lean`'s `IdentAlg.comap`, rewrite the five threshold rules with `thresholdStop`, state MaynardZhang Lemma 6 through `stoppingTime`/`stoppedHist`, replace Garivier Remark 2's `τE` by `expectedStoppingTime`.
4. **This project** (done 2026-09-11): Markov output kernels. `IdentAlg` lost the two s-finite/probability fields and the `extendKernel` plumbing; `fixedBudget` takes `[Nonempty 𝓞]` (provided at each use by a design point `⟨x 0⟩`, an initial state `⟨out A.init⟩`, `Nonempty ℝ`, or the nonemptiness lemma of the action set); the `have := hA.isMarkovKernel_output` lines and the `[IsMarkovKernel (A.output T)]` hypotheses that carried the instance through the proofs went away; `IsRun.klDiv_map_stoppedHist_out` and `klDiv_map_out_le_stoppedHist` lost their a.s.-finiteness hypotheses (Mathlib's `klDiv_compProd_left` applies directly), which made `ae_stoppedHist_mem_stopSet` and `klDiv_map_stoppedHist_out_of_isFixedBudget` redundant. The comparator challenges, which inline the structure, were regenerated and compile; `scripts/comparator-verify.sh` has not been rerun since. Still to do here: rename to `IdentAlg Unit 𝒳 ℝ 𝒳` with output type `𝓩` when switching to the LML version.

## 5. Left open

* Whether `IsPAC` keeps its explicit universe parameter once `runMeasure` exists for every algorithm (the canonical run lives in the universe of `(ℕ → Round 𝓞 𝓐 𝓨) × 𝓩`; `IsPAC.{u}` with `u` that universe is what the transport lemma needs).
* Within-episode stopping steps (Lee2026Unified's `etaAt : ℕ`, bounded by the horizon) are a different object and are not covered by the layer; if a second paper needs them, a `Fin`-indexed variant of `stoppingTime` on the steps of an episode would be the analogue.
