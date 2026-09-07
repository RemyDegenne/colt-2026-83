/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The barrier sum inequality

The elementary inequality behind the lower-barrier step of the Batson–Spielman–Srivastava
argument. Given reals `a i ≥ 1` with `∑ 1 / a i ≤ 1`, set `b i = a i - 1 / 2`,
`P = ∑ 1 / b i ^ 2` and `Δ = ∑ (1 / b i - 1 / a i)`. Then `Δ > 0` and
`P / Δ - ∑ 1 / b i ≥ 2 - ∑ 1 / a i`.

The proof goes through `Q = ∑ 1 / (a i * b i)`: one has `Δ = Q / 2`,
`P - Q = (1 / 2) ∑ 1 / (a i * b i ^ 2)` and, by Cauchy–Schwarz,
`Q ^ 2 ≤ (∑ 1 / (a i * b i ^ 2)) * ∑ 1 / a i ≤ 2 * (P - Q)`.
-/

@[expose] public section

open Finset

/-- With `b i = a i - 1/2`: `∑ (1/b i - 1/a i) > 0`. -/
lemma sum_inv_sub_half_sub_inv_pos {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha : ∀ i, 1 ≤ a i) :
    0 < ∑ i, ((a i - 1 / 2)⁻¹ - (a i)⁻¹) := by
  refine sum_pos (fun i _ ↦ sub_pos.2 (inv_strictAnti₀ ?_ ?_)) univ_nonempty
  · linarith [ha i]
  · linarith

/-- The averaged barrier inequality: for `a i ≥ 1` with `∑ 1/a i ≤ 1`, writing `b i = a i - 1/2`,
`P = ∑ 1/b i ^ 2`, `Δ = ∑ (1/b i - 1/a i)`, one has `P / Δ - ∑ 1/b i ≥ 2 - ∑ 1/a i`. -/
lemma barrier_sum_ineq {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i)
    (hΦ : ∑ i, (a i)⁻¹ ≤ 1) :
    2 - ∑ i, (a i)⁻¹ ≤
      (∑ i, ((a i - 1 / 2)⁻¹) ^ 2) / (∑ i, ((a i - 1 / 2)⁻¹ - (a i)⁻¹)) - ∑ i, (a i - 1 / 2)⁻¹ := by
  set b : ι → ℝ := fun i ↦ a i - 1 / 2 with hb
  have ha_pos : ∀ i, 0 < a i := fun i ↦ by linarith [ha i]
  have hb_pos : ∀ i, 0 < b i := fun i ↦ by simp only [hb]; linarith [ha i]
  -- pointwise identities
  have h1 : ∀ i, (b i)⁻¹ - (a i)⁻¹ = (a i * b i)⁻¹ / 2 := fun i ↦ by
    have hab : a i - b i = 1 / 2 := by simp only [hb]; ring
    rw [inv_sub_inv (hb_pos i).ne' (ha_pos i).ne', hab]
    ring
  have h2 : ∀ i, (b i)⁻¹ ^ 2 - (a i * b i)⁻¹ = (a i * b i ^ 2)⁻¹ / 2 := fun i ↦ by
    have ha' : a i ≠ 0 := (ha_pos i).ne'
    have hb' : a i - 1 / 2 ≠ 0 := (hb_pos i).ne'
    simp only [hb]
    field_simp
    ring
  -- the auxiliary sums
  set Q := ∑ i, (a i * b i)⁻¹ with hQ
  set R := ∑ i, (a i * b i ^ 2)⁻¹ with hR
  have hQ_pos : 0 < Q :=
    sum_pos (fun i _ ↦ by have := ha_pos i; have := hb_pos i; positivity) univ_nonempty
  have hR_pos : 0 < R :=
    sum_pos (fun i _ ↦ by have := ha_pos i; have := hb_pos i; positivity) univ_nonempty
  have hΔ : ∑ i, ((b i)⁻¹ - (a i)⁻¹) = Q / 2 := by
    rw [hQ, eq_div_iff two_ne_zero, sum_mul]
    exact sum_congr rfl fun i _ ↦ by rw [h1 i, div_mul_cancel₀ _ two_ne_zero]
  have hPQ : ∑ i, (b i)⁻¹ ^ 2 - Q = R / 2 := by
    rw [hQ, hR, ← sum_sub_distrib, eq_div_iff two_ne_zero, sum_mul]
    exact sum_congr rfl fun i _ ↦ by rw [h2 i, div_mul_cancel₀ _ two_ne_zero]
  have hΦ' : ∑ i, (b i)⁻¹ = ∑ i, (a i)⁻¹ + Q / 2 := by
    rw [← hΔ, ← sum_add_distrib]
    simp
  -- Cauchy–Schwarz: `Q ^ 2 ≤ R * ∑ 1 / a i ≤ R`
  have hCS : Q ^ 2 ≤ R * ∑ i, (a i)⁻¹ := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ ↦ ?_) (fun i _ ↦ ?_) (fun i _ ↦ ?_)
    · have := ha_pos i; have := hb_pos i; positivity
    · have := (ha_pos i).le; positivity
    · have := ha_pos i
      have := hb_pos i
      refine le_of_eq ?_
      field_simp
  have hQ2 : Q ^ 2 ≤ R := hCS.trans (mul_le_of_le_one_right hR_pos.le hΦ)
  -- conclusion
  rw [hΔ, hΦ', le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  nlinarith [hPQ, hQ2, hQ_pos]
