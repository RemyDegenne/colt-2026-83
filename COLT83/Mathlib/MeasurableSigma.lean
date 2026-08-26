/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of functions on a sigma type

A function on `Σ a, β a` is measurable as soon as each of its restrictions `f ∘ Sigma.mk a` is.
-/

@[expose] public section

open MeasurableSpace

variable {α γ : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] [MeasurableSpace γ]

@[fun_prop]
lemma measurable_sigma_mk (a : α) : Measurable (Sigma.mk a : β a → Σ a, β a) :=
  fun _ hs ↦ measurableSet_iInf.1 hs a

/-- A function on a sigma type is measurable if all its restrictions to the fibers are. -/
lemma measurable_sigma_of_measurable_comp_mk {f : (Σ a, β a) → γ}
    (h : ∀ a, Measurable (f ∘ Sigma.mk a)) : Measurable f :=
  fun _ hs ↦ measurableSet_iInf.2 fun a ↦ (h a) hs

/-- A set in a sigma type is measurable iff its trace on every fiber is. -/
lemma measurableSet_sigma_iff {s : Set (Σ a, β a)} :
    MeasurableSet s ↔ ∀ a, MeasurableSet (Sigma.mk a ⁻¹' s) :=
  measurableSet_iInf

lemma measurable_sigma_iff {f : (Σ a, β a) → γ} :
    Measurable f ↔ ∀ a, Measurable (f ∘ Sigma.mk a) :=
  ⟨fun hf a ↦ hf.comp (measurable_sigma_mk a), measurable_sigma_of_measurable_comp_mk⟩
