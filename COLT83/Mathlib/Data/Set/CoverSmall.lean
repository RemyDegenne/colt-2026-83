/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Covering a finite set by a few small subsets

A finite set of `m ≥ d ≥ 1` elements is covered by `d` nonempty subsets of at most `m / d + 1`
elements each: enumerate the set by `Fin m` and group the elements by the residue of their index
modulo `d`. This is the combinatorial splitting of the action set into `d` regions used by the
logarithmic gain of adaptivity (blueprint `thm:log_gains` (ii)).
-/

@[expose] public section

namespace Set

/-- A finite set of `m ≥ d ≥ 1` elements is covered by `d` nonempty subsets of at most `m / d + 1`
elements each. -/
lemma exists_cover_ncard_le {α : Type*} {s : Set α} (hs : s.Finite) {d : ℕ} (hd : 0 < d)
    (hds : d ≤ s.ncard) :
    ∃ R : Fin d → Set α, (∀ i, R i ⊆ s) ∧ (∀ i, (R i).Nonempty) ∧
      (∀ i, (R i).ncard ≤ s.ncard / d + 1) ∧ s ⊆ ⋃ i, R i := by
  obtain ⟨m, f, hf, rfl⟩ := hs.fin_param
  have hm : (range f).ncard = m := by
    rw [ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hm] at hds ⊢
  refine ⟨fun i ↦ f '' {k | (k : ℕ) % d = i}, fun i ↦ image_subset_range _ _, fun i ↦ ?_,
    fun i ↦ ?_, fun y hy ↦ ?_⟩
  · exact ⟨f ⟨i, i.2.trans_le hds⟩, ⟨i, i.2.trans_le hds⟩, Nat.mod_eq_of_lt i.2, rfl⟩
  · rw [ncard_image_of_injective _ hf]
    calc ({k : Fin m | (k : ℕ) % d = i}).ncard
        ≤ (Finset.Iic (m / d) : Set ℕ).ncard :=
          ncard_le_ncard_of_injOn (fun k : Fin m ↦ (k : ℕ) / d) ?_ ?_
      _ = m / d + 1 := by rw [ncard_coe_finset, Nat.card_Iic]
    · intro k _
      simp only [Finset.coe_Iic, mem_Iic]
      exact Nat.div_le_div_right k.2.le
    · intro k hk k' hk' hkk'
      simp only [mem_ofPred_eq] at hk hk' hkk'
      exact Fin.ext (by
        rw [← Nat.div_add_mod (k : ℕ) d, ← Nat.div_add_mod (k' : ℕ) d, hkk', hk, hk'])
  · obtain ⟨k, rfl⟩ := hy
    exact mem_iUnion.2 ⟨⟨(k : ℕ) % d, Nat.mod_lt _ hd⟩, k, rfl, rfl⟩

end Set
