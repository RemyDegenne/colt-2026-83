/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import Maiti2026Power.Mathlib.Probability.CondDistrib
public import Maiti2026Power.Mathlib.Probability.CondDistribConst

/-!
# The law of the history of an algorithm-environment sequence

The history `history O X Y n` of the first `n` rounds of an algorithm-environment sequence is
obtained from the history of the first `n - 1` rounds by appending the step at round `n - 1`.
At the level of laws this says that the law of the first `n + 1` rounds is the
composition-product of the law of the first `n` rounds with the step kernel.

* `map_history_succ_of_hasCondDistrib`, `IsAlgEnvSeq.map_history_succ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}

/-- If the step at round `n` has conditional law `stepKernel alg env n` given the first `n`
rounds under a measure `Q`, then the law of the first `n + 1` rounds under `Q` is the
composition-product of the law of the first `n` rounds with the step kernel. -/
lemma map_history_succ_of_hasCondDistrib {Q : Measure Ω} {n : ℕ}
    (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (h : HasCondDistrib (step O X Y n) (history O X Y n) (stepKernel alg env n) Q) :
    Q.map (history O X Y (n + 1)) =
      (Q.map (history O X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm := by
  rw [history_succ, ← h.map_eq,
    Measure.map_map (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm.measurable
      (by fun_prop)]

/-- The law of the first `n + 1` rounds is the composition-product of the law of the first `n`
rounds with the step kernel. -/
lemma IsAlgEnvSeq.map_history_succ {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O X Y alg env P) (n : ℕ) :
    P.map (history O X Y (n + 1)) =
      (P.map (history O X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.finSuccProd (Round 𝓞 𝓐 𝓨) n).symm :=
  map_history_succ_of_hasCondDistrib h.measurable_obs h.measurable_action h.measurable_feedback
    (h.hasCondDistrib_step n)

end Learning
