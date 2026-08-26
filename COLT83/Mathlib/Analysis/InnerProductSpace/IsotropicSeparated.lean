/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Well-separated points of a family in isotropic position

Let `E` be a finite-dimensional real inner product space of dimension `d`, and let `u : ι → E` be
a finite family of vectors with nonnegative weights `w : ι → ℝ` summing to `1`, in *isotropic
position*: `∑ i, w i * ⟪u i, v⟫ ^ 2 = ‖v‖ ^ 2` for every `v : E`.

## Main results

* `exists_pos_weight_sq_dist_ge_of_isotropic`: for every subspace `V` of `E`, there is an index `i`
  with positive weight such that the squared distance from `u i` to `V` is at least `d - dim V`.
* `exists_separated_of_isotropic`: for every `m`, there are `m` indices with positive weights whose
  points are pairwise at squared distance at least `d + 1 - m`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Finset Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `f` is an orthonormal basis of the orthogonal complement `Vᗮ` of a subspace `V`, then for
every `v ∈ V` and every `x`, the sum of the squared inner products of `x` against `f` is at most
`‖x - v‖ ^ 2`. -/
lemma sum_inner_sq_orthogonal_le_norm_sub_sq {V : Submodule ℝ E} {κ : Type*} [Fintype κ]
    (f : OrthonormalBasis κ ℝ Vᗮ) (x : E) {v : E} (hv : v ∈ V) :
    ∑ j, ⟪x, (f j : E)⟫ ^ 2 ≤ ‖x - v‖ ^ 2 := by
  have horth : Orthonormal ℝ (fun j ↦ (f j : E)) := f.orthonormal.comp_linearIsometry Vᗮ.subtypeₗᵢ
  have h := horth.sum_inner_products_le (x - v) (s := univ)
  simp only [Real.norm_eq_abs, sq_abs, inner_sub_right,
    Submodule.inner_left_of_mem_orthogonal hv (f _).2, sub_zero, real_inner_comm x] at h
  exact h

variable [FiniteDimensional ℝ E]

/-- Let `u` be a weighted family in isotropic position. Then for every subspace `V` there is an
index `i` with positive weight such that `u i` is at squared distance at least
`finrank ℝ E - finrank ℝ V` from `V`. -/
lemma exists_pos_weight_sq_dist_ge_of_isotropic {ι : Type*} [Fintype ι] {u : ι → E} {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hiso : ∀ v, ∑ i, w i * ⟪u i, v⟫ ^ 2 = ‖v‖ ^ 2)
    (V : Submodule ℝ E) :
    ∃ i, 0 < w i ∧ ∀ v ∈ V, (finrank ℝ E : ℝ) - finrank ℝ V ≤ ‖u i - v‖ ^ 2 := by
  set f := stdOrthonormalBasis ℝ Vᗮ
  set D : ℝ := (finrank ℝ E : ℝ) - finrank ℝ V with hD
  set S : ι → ℝ := fun i ↦ ∑ j, ⟪u i, (f j : E)⟫ ^ 2 with hS
  have hD' : D = finrank ℝ Vᗮ := by
    rw [hD, sub_eq_iff_eq_add, ← Nat.cast_add, add_comm, Submodule.finrank_add_finrank_orthogonal]
  have hsum : ∑ i, w i * S i = D := by
    simp only [hS, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hiso, Submodule.norm_coe, f.orthonormal.1, one_pow, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hD']
  have hex : ∃ i, 0 < w i ∧ D ≤ S i := by
    by_contra! h
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < w i := by
      by_contra! h0
      have : ∑ i, w i = 0 := sum_eq_zero fun i _ ↦ le_antisymm (h0 i) (hw i)
      linarith
    have hlt : ∑ i, w i * S i < ∑ i, w i * D := by
      refine sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, mem_univ _, mul_lt_mul_of_pos_left (h i₀ hi₀) hi₀⟩
      rcases (hw i).eq_or_lt with h0 | h0
      · simp [← h0]
      · exact (mul_lt_mul_of_pos_left (h i h0) h0).le
    rw [hsum, ← sum_mul, hw1, one_mul] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨i, hi, hiS⟩ := hex
  exact ⟨i, hi, fun v hv ↦ hiS.trans (sum_inner_sq_orthogonal_le_norm_sub_sq f (u i) hv)⟩

/-- Let `u` be a weighted family in isotropic position in a space of dimension `d`. Then for every
`m`, there are `m` indices with positive weights whose points are pairwise at squared distance at
least `d + 1 - m`. -/
lemma exists_separated_of_isotropic {ι : Type*} [Fintype ι] {u : ι → E} {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hiso : ∀ v, ∑ i, w i * ⟪u i, v⟫ ^ 2 = ‖v‖ ^ 2)
    (m : ℕ) :
    ∃ t : Fin m → ι, (∀ k, 0 < w (t k)) ∧
      ∀ k l, k ≠ l → (finrank ℝ E : ℝ) + 1 - m ≤ ‖u (t k) - u (t l)‖ ^ 2 := by
  induction m with
  | zero => exact ⟨finZeroElim, fun k ↦ k.elim0, fun k ↦ k.elim0⟩
  | succ m ih =>
    obtain ⟨t, ht, htsep⟩ := ih
    set V := Submodule.span ℝ (Set.range (u ∘ t))
    have hVdim : (finrank ℝ V : ℝ) ≤ m := by
      have h := finrank_range_le_card (R := ℝ) (u ∘ t)
      simp only [Set.finrank, Fintype.card_fin] at h
      exact_mod_cast h
    obtain ⟨i, hi, hdist⟩ := exists_pos_weight_sq_dist_ge_of_isotropic hw hw1 hiso V
    have hnew : ∀ k, (finrank ℝ E : ℝ) + 1 - (m + 1 : ℕ) ≤ ‖u i - u (t k)‖ ^ 2 := fun k ↦ by
      refine le_trans ?_ (hdist _ (Submodule.subset_span ⟨k, rfl⟩))
      push_cast
      linarith
    refine ⟨Fin.snoc t i, ?_, ?_⟩
    · intro k
      induction k using Fin.lastCases with
      | last => simpa using hi
      | cast k => simpa using ht k
    · intro k l hkl
      induction k using Fin.lastCases with
      | last =>
        induction l using Fin.lastCases with
        | last => exact absurd rfl hkl
        | cast l => simpa using hnew l
      | cast k =>
        induction l using Fin.lastCases with
        | last => simpa [norm_sub_rev] using hnew k
        | cast l =>
          simp only [Fin.snoc_castSucc]
          refine le_trans ?_ (htsep k l fun h ↦ hkl (by rw [h]))
          push_cast
          linarith

end
