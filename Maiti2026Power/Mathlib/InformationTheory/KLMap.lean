/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# The Kullback–Leibler divergence of the images of two measures

* `klDiv_map_of_leftInverse`: the divergence is invariant under a measurable map with a
  measurable left inverse.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The Kullback–Leibler divergence is invariant under a measurable map with a measurable left
inverse. -/
lemma klDiv_map_of_leftInverse {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hf) ?_
  have h := klDiv_map_le (μ.map f) (ν.map f) hg
  rwa [Measure.map_map hg hf, Measure.map_map hg hf, hgf.comp_eq_id, Measure.map_id,
    Measure.map_id] at h

end InformationTheory
