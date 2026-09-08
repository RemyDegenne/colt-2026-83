/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Maiti2026Power.Mathlib.Probability.CondDistrib
public import Maiti2026Power.Mathlib.Probability.CondDistribConst

/-!
# The law of the history of an algorithm-environment sequence

The history `history X Y n` of the first `n` rounds of an algorithm-environment sequence is
obtained from the history of the first `n - 1` rounds by appending the step at round `n - 1`.
At the level of laws this says that the law of the first `n + 1` rounds is the
composition-product of the law of the first `n` rounds with the step kernel.

* `map_history_succ_of_hasCondDistrib`, `IsAlgEnvSeq.map_history_succ`.
* `stepKernel_stationaryEnv`: in a stationary environment with reward kernel `κ`, the step
  kernel at round `n` is `alg.policy n ⊗ₖ κ.prodMkLeft _`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓐 𝓨}
  {env : Environment 𝓐 𝓨}

/-- In a stationary environment with reward kernel `κ`, the step kernel at round `n` is the
composition-product of the policy with `κ`. -/
lemma stepKernel_stationaryEnv (alg : Algorithm 𝓐 𝓨) (κ : Kernel 𝓐 𝓨) [IsMarkovKernel κ]
    (n : ℕ) :
    stepKernel alg (stationaryEnv κ) n = alg.policy n ⊗ₖ κ.prodMkLeft _ := by
  rw [stepKernel, feedback_stationaryEnv]

/-- If the step at round `n` has conditional law `stepKernel alg env n` given the first `n`
rounds under a measure `Q`, then the law of the first `n + 1` rounds under `Q` is the
composition-product of the law of the first `n` rounds with the step kernel. -/
lemma map_history_succ_of_hasCondDistrib {Q : Measure Ω} {n : ℕ}
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (h : HasCondDistrib (step X Y n) (history X Y n) (stepKernel alg env n) Q) :
    Q.map (history X Y (n + 1)) =
      (Q.map (history X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (𝓐 × 𝓨) n).symm := by
  rw [history_succ, ← h.map_eq,
    Measure.map_map (MeasurableEquiv.finSuccProd (𝓐 × 𝓨) n).symm.measurable (by fun_prop)]

/-- The law of the first `n + 1` rounds is the composition-product of the law of the first `n`
rounds with the step kernel. -/
lemma IsAlgEnvSeq.map_history_succ {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq X Y alg env P) (n : ℕ) :
    P.map (history X Y (n + 1)) =
      (P.map (history X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (𝓐 × 𝓨) n).symm :=
  map_history_succ_of_hasCondDistrib h.measurable_action h.measurable_feedback
    (h.hasCondDistrib_step n)

end Learning
