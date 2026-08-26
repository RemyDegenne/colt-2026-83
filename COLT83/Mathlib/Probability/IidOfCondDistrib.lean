/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Sequences with a constant conditional law are i.i.d.

If `W 0` has law `ν` and, for every `n`, the conditional law of `W (n + 1)` given
`(W 0, …, W n)` is the constant `ν`, then `(W 0, …, W (n - 1))` has the product law `ν^n` for every
`n` (`hasLaw_pi_of_hasCondDistrib_const`), hence the `W i` are independent with law `ν`
(`iIndepFun_of_hasCondDistrib_const`). The conditioning variable can be replaced by any variable
of which `(W 0, …, W n)` is a measurable function (`HasCondDistrib.const_comp_right`).

This is the abstract form of "the noise of a sequential experiment is i.i.d.", used for the
noise of a linear Gaussian bandit run.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω β 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {ν : Measure β} {Y : Ω → β}

lemma Kernel.const_comap_eq (ν : Measure β) {f : 𝓧 → 𝓩} (hf : Measurable f) :
    (Kernel.const 𝓩 ν).comap f hf = Kernel.const 𝓧 ν := by
  ext a s _
  simp [Kernel.comap_apply]

/-- A constant conditional law given `Z` is a constant conditional law given any measurable
function of `Z`. -/
lemma HasCondDistrib.const_comp_right [SFinite P] [SFinite ν] {Z : Ω → 𝓩}
    (h : HasCondDistrib Y Z (Kernel.const 𝓩 ν) P)
    {f : 𝓩 → 𝓧} (hf : Measurable f) : HasCondDistrib Y (f ∘ Z) (Kernel.const 𝓧 ν) P := by
  refine HasCondDistrib.comp_right (hf := hf) ?_
  rwa [Kernel.const_comap_eq]

variable [IsProbabilityMeasure P] [IsProbabilityMeasure ν] {W : ℕ → Ω → β}

/-- The law of `W i` when the conditional law of `W (n + 1)` given `(W 0, …, W n)` is the
constant `ν`. -/
lemma hasLaw_of_hasCondDistrib_const (h0 : HasLaw (W 0) ν P)
    (h : ∀ n, HasCondDistrib (W (n + 1)) (fun ω (i : Fin (n + 1)) ↦ W i ω) (Kernel.const _ ν) P)
    (i : ℕ) : HasLaw (W i) ν P := by
  cases i with
  | zero => exact h0
  | succ n => exact (h n).hasLaw_of_const

omit [IsProbabilityMeasure P] in
/-- The law of `(W 0, …, W n)` when the conditional law of `W (n + 1)` given `(W 0, …, W n)` is
the constant `ν`: the product law `ν^(n + 1)`. -/
theorem hasLaw_pi_succ_of_hasCondDistrib_const (h0 : HasLaw (W 0) ν P)
    (h : ∀ n, HasCondDistrib (W (n + 1)) (fun ω (i : Fin (n + 1)) ↦ W i ω) (Kernel.const _ ν) P)
    (n : ℕ) : HasLaw (fun ω (i : Fin (n + 1)) ↦ W i ω) (Measure.pi fun _ ↦ ν) P := by
  induction n with
  | zero =>
    have h4 := (measurePreserving_piUnique fun _ : Fin 1 ↦ ν).symm.comp_hasLaw h0
    refine h4.congr ?_
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    funext i
    simp [MeasurableEquiv.piUnique]
  | succ n ih =>
    -- the law of `(W (n + 1), (W 0, …, W n))`
    have h1 : HasLaw (fun ω ↦ (W (n + 1) ω, fun i : Fin (n + 1) ↦ W i ω))
        (ν.prod (Measure.pi fun _ : Fin (n + 1) ↦ ν)) P := by
      have h2 := ih.prodMk_of_hasCondDistrib (h n)
      rw [Measure.compProd_const] at h2
      exact Measure.measurePreserving_swap.comp_hasLaw h2
    -- transport through the measurable equivalence `piFinSuccAbove`
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) ↦ ν) (Fin.last (n + 1))
    have hcomp : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ β) (Fin.last (n + 1))) ∘
        (fun ω (i : Fin (n + 2)) ↦ W i ω) =
        fun ω ↦ (W (n + 1) ω, fun i : Fin (n + 1) ↦ W i ω) := by
      funext ω
      rw [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
      exact Prod.ext (by simp) (funext fun i ↦ by simp [Fin.init])
    have h3 : HasLaw ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ β) (Fin.last (n + 1)))
        ∘ fun ω (i : Fin (n + 2)) ↦ W i ω) (ν.prod (Measure.pi fun _ : Fin (n + 1) ↦ ν)) P := by
      rw [hcomp]
      exact h1
    exact (hpres.symm.comp_hasLaw h3).congr
      (Filter.Eventually.of_forall fun ω ↦ (MeasurableEquiv.symm_apply_apply _ _).symm)

/-- **A sequence with a constant conditional law is i.i.d.**: if `W 0` has law `ν` and the
conditional law of `W (n + 1)` given `(W 0, …, W n)` is the constant `ν` for every `n`, then
`(W 0, …, W (n - 1))` has the product law `ν^n`. -/
theorem hasLaw_pi_of_hasCondDistrib_const (h0 : HasLaw (W 0) ν P)
    (h : ∀ n, HasCondDistrib (W (n + 1)) (fun ω (i : Fin (n + 1)) ↦ W i ω) (Kernel.const _ ν) P)
    (n : ℕ) : HasLaw (fun ω (i : Fin n) ↦ W i ω) (Measure.pi fun _ ↦ ν) P := by
  cases n with
  | zero =>
    have hconst : (fun ω (i : Fin 0) ↦ W i ω) = fun _ ↦ (isEmptyElim : Fin 0 → β) := by
      funext ω i
      exact i.elim0
    rw [hconst]
    refine ⟨aemeasurable_const, ?_⟩
    rw [Measure.map_const, measure_univ, one_smul, Measure.pi_of_empty]
  | succ n => exact hasLaw_pi_succ_of_hasCondDistrib_const h0 h n

/-- **A sequence with a constant conditional law is i.i.d.**: independence of
`W 0, …, W (n - 1)`. -/
theorem iIndepFun_of_hasCondDistrib_const (h0 : HasLaw (W 0) ν P)
    (h : ∀ n, HasCondDistrib (W (n + 1)) (fun ω (i : Fin (n + 1)) ↦ W i ω) (Kernel.const _ ν) P)
    (n : ℕ) : iIndepFun (fun i : Fin n ↦ W i) P :=
  (iIndepFun_iff_hasLaw_pi_pi (X := fun i : Fin n ↦ W i)
    fun i ↦ hasLaw_of_hasCondDistrib_const h0 h i).2 (hasLaw_pi_of_hasCondDistrib_const h0 h n)

end ProbabilityTheory
