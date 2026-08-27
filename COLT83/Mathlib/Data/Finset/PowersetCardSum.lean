/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Powerset

/-!
# Double sums over a set of a given size and one of its elements

The pairs `(S, i)` with `|S| = k + 1` and `i ∈ S` are in bijection with the pairs `(B, i)` with
`|B| = k` and `i ∉ B`, through `(S, i) ↦ (S \ {i}, i)`. This is the reindexing used by the lower
bound for the `m`-sets (blueprint `lem:msets_equivalent_sampling`).
-/

@[expose] public section

open Finset

/-- Reindexing a double sum over a set of size `k + 1` and one of its elements along the
bijection `(S, i) ↦ (S \ {i}, i)` onto the pairs `(B, i)` with `|B| = k` and `i ∉ B`. -/
lemma Finset.sum_powersetCard_succ_sum_mem {ι M : Type*} [DecidableEq ι] [Fintype ι]
    [AddCommMonoid M] (k : ℕ) (F : Finset ι → ι → M) :
    ∑ S ∈ powersetCard (k + 1) univ, ∑ i ∈ S, F (S.erase i) i =
      ∑ B ∈ powersetCard k univ, ∑ i ∈ Bᶜ, F B i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p ↦ ⟨p.1.erase p.2, p.2⟩) (fun p ↦ ⟨insert p.2 p.1, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨S, i⟩ hp
    simp only [mem_sigma, mem_powersetCard, mem_compl] at hp ⊢
    exact ⟨⟨subset_univ _, by rw [card_erase_of_mem hp.2]; omega⟩, notMem_erase _ _⟩
  · rintro ⟨B, i⟩ hp
    simp only [mem_sigma, mem_powersetCard, mem_compl] at hp ⊢
    exact ⟨⟨subset_univ _, by rw [card_insert_of_notMem hp.2, hp.1.2]⟩, mem_insert_self _ _⟩
  · rintro ⟨S, i⟩ hp
    simp only [mem_sigma, mem_powersetCard] at hp
    simp [insert_erase hp.2]
  · rintro ⟨B, i⟩ hp
    simp only [mem_sigma, mem_compl] at hp
    simp [erase_insert hp.2]
  · rintro ⟨S, i⟩ _
    rfl
