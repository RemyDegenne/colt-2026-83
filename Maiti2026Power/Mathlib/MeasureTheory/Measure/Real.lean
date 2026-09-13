/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Complements of events under a probability measure

If an event has probability at least `1 - δ`, its complement has probability at most `δ`.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If an event has probability at least `1 - δ`, its complement has probability at most `δ`. -/
lemma measureReal_compl_le_of_one_sub_le {s : Set Ω} (hs : MeasurableSet s) {δ : ℝ}
    (h : 1 - δ ≤ μ.real s) : μ.real sᶜ ≤ δ := by
  rw [measureReal_compl hs, probReal_univ]
  linarith

/-- If `f ≤ c` with probability at least `1 - δ`, then `c < f` with probability at most `δ`. -/
lemma measureReal_lt_le_of_one_sub_le_measureReal_le {f : Ω → ℝ} (hf : Measurable f) {c δ : ℝ}
    (h : 1 - δ ≤ μ.real {ω | f ω ≤ c}) : μ.real {ω | c < f ω} ≤ δ := by
  rw [show {ω | c < f ω} = {ω | f ω ≤ c}ᶜ by ext; simp]
  exact measureReal_compl_le_of_one_sub_le (measurableSet_le hf measurable_const) h

end MeasureTheory
