/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Order
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Suprema of finitely many real numbers

Elementary facts about `⨆ i, f i` for `f : ι → ℝ` with `ι` finite and nonempty:
`|⨆ i, f i| ≤ ∑ i, |f i|`, `exp (t * ⨆ i, f i) ≤ ∑ i, exp (t * f i)` and
`⨆ i, (b + c * f i) = b + c * ⨆ i, f i` for `c ≥ 0`.

## TODO

These are stated for `ℝ` only: `abs_le_sum_abs_iSup` and `ciSup_const_add_const_mul` hold in
any conditionally complete linear ordered field, and `exp_mul_iSup_le_sum` (which is what forces
the import of the exponential into this `Order` file) is an instance of the general fact that a
nonnegative monotone function of a finite maximum is at most the sum of its values.
-/

@[expose] public section

open Real

variable {ι : Type*}

lemma abs_le_sum_abs_iSup [Fintype ι] [Nonempty ι] (f : ι → ℝ) : |⨆ i, f i| ≤ ∑ i, |f i| := by
  refine abs_le.2 ⟨?_, ciSup_le fun i ↦ (le_abs_self _).trans (Finset.single_le_sum
    (f := fun i ↦ |f i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i))⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine (neg_le.2 ?_).trans (le_ciSup (Finite.bddAbove_range f) i)
  exact (neg_le_abs _).trans (Finset.single_le_sum (f := fun i ↦ |f i|)
    (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i))

lemma exp_mul_iSup_le_sum [Fintype ι] [Nonempty ι] (t : ℝ) (f : ι → ℝ) :
    exp (t * ⨆ i, f i) ≤ ∑ i, exp (t * f i) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ⨆ i, f i = f i₀ := by
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨i₀, le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range f) i₀)⟩
  rw [hi₀]
  exact Finset.single_le_sum (f := fun i ↦ exp (t * f i)) (fun i _ ↦ (exp_pos _).le)
    (Finset.mem_univ i₀)

/-- `⨆ i, (b + c * f i) = b + c * ⨆ i, f i` for `c ≥ 0` over a finite nonempty index set. -/
lemma ciSup_const_add_const_mul [Finite ι] [Nonempty ι] (b : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (f : ι → ℝ) :
    ⨆ i, (b + c * f i) = b + c * ⨆ i, f i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
  have hsup : ⨆ i, f i = f i₀ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range f) i₀)
  rw [hsup]
  refine le_antisymm (ciSup_le fun i ↦ by gcongr; exact hi₀ i) ?_
  exact le_ciSup (Finite.bddAbove_range fun i ↦ b + c * f i) i₀
