/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.Multitask

/-!
# The hard instances of the multi-task lower bound

For block sizes `d : Fin m → ℕ` and an accuracy `ε > 0`, the hard instances of the lower bound
for multi-task bandits (blueprint `def:multitask_instances`) are indexed by the elements
`κ : ∀ j, Fin (d j)` of the multi-task set: `mtParam d ε κ` has the value `10 εⱼ` at the position
`⟨j, κ j⟩` of every block `j` and `0` elsewhere, where `εⱼ = ε √dⱼ / S_d` and
`S_d = ∑ⱼ √dⱼ` (`mtSum`), so that `∑ⱼ εⱼ = ε`. The alternative used for the block `j` is
`mtParam0 d ε κ j`, the same vector with the block `j` set to `0`; it does not depend on
`κ j` (`mtParam0_update`), which is what makes the two instances `κ` and `Function.update κ j i`
indistinguishable.

The value of a recommendation is `⟪y, mtParam d ε κ⟫ = ∑ⱼ 10 εⱼ y ⟨j, κ j⟩`
(`inner_mtParam`), the maximal value on the multi-task set is `10 ε` (`supportFn_mtParam`), and
the difference of an instance and its alternative is supported on a single coordinate
(`inner_mtParam0_sub_mtParam`).
-/

@[expose] public section

open MeasureTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {m : ℕ} {d : Fin m → ℕ} {ε : ℝ}

/-- `S_d = ∑ⱼ √dⱼ`, the quantity appearing in the multi-task lower bound. -/
noncomputable def mtSum (d : Fin m → ℕ) : ℝ := ∑ j, √(d j)

lemma mtSum_nonneg : 0 ≤ mtSum d := sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

lemma mtSum_pos (hm : 0 < m) (hd : ∀ j, 0 < d j) : 0 < mtSum d := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine sum_pos (fun j _ ↦ Real.sqrt_pos.2 ?_) univ_nonempty
  exact_mod_cast hd j

/-- The accuracy `εⱼ = ε √dⱼ / S_d` allocated to the block `j`. -/
noncomputable def mtEps (d : Fin m → ℕ) (ε : ℝ) (j : Fin m) : ℝ := ε * √(d j) / mtSum d

lemma mtEps_nonneg (hε : 0 ≤ ε) (j : Fin m) : 0 ≤ mtEps d ε j :=
  div_nonneg (mul_nonneg hε (Real.sqrt_nonneg _)) mtSum_nonneg

/-- The accuracies of the blocks sum to `ε`. -/
lemma sum_mtEps (hm : 0 < m) (hd : ∀ j, 0 < d j) (ε : ℝ) : ∑ j, mtEps d ε j = ε := by
  have hS : mtSum d ≠ 0 := (mtSum_pos hm hd).ne'
  simp only [mtEps, ← sum_div, ← mul_sum]
  rw [← mtSum]
  field_simp

/-- The reward vector of the hard instance indexed by `κ`: `10 εⱼ` at the position `⟨j, κ j⟩` of
every block. -/
noncomputable def mtParam (d : Fin m → ℕ) (ε : ℝ) (κ : ∀ j, Fin (d j)) :
    EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ if i.2 = κ i.1 then 10 * mtEps d ε i.1 else 0

/-- The alternative of the block `j`: `mtParam d ε κ` with the block `j` set to `0`. -/
noncomputable def mtParam0 (d : Fin m → ℕ) (ε : ℝ) (κ : ∀ j, Fin (d j)) (j : Fin m) :
    EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ if i.1 = j then 0 else if i.2 = κ i.1 then 10 * mtEps d ε i.1 else 0

@[simp] lemma mtParam_apply (κ : ∀ j, Fin (d j)) (i : Σ j, Fin (d j)) :
    mtParam d ε κ i = if i.2 = κ i.1 then 10 * mtEps d ε i.1 else 0 := rfl

@[simp] lemma mtParam0_apply (κ : ∀ j, Fin (d j)) (j : Fin m) (i : Σ j, Fin (d j)) :
    mtParam0 d ε κ j i =
      if i.1 = j then 0 else if i.2 = κ i.1 then 10 * mtEps d ε i.1 else 0 := rfl

/-- The alternative of the block `j` does not depend on the coordinate `j` of `κ`. -/
lemma mtParam0_update (κ : ∀ j, Fin (d j)) (j : Fin m) (i : Fin (d j)) :
    mtParam0 d ε (Function.update κ j i) j = mtParam0 d ε κ j := by
  ext i'
  rw [mtParam0_apply, mtParam0_apply]
  by_cases h : i'.1 = j
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, Function.update_of_ne h]

/-- The value of a recommendation under the instance `κ`. -/
lemma inner_mtParam (κ : ∀ j, Fin (d j)) (y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪y, mtParam d ε κ⟫ = ∑ j, 10 * mtEps d ε j * y ⟨j, κ j⟩ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ ↦ ?_
  change ∑ l : Fin (d j), (if l = κ j then 10 * mtEps d ε j else 0) * y ⟨j, l⟩ = _
  simp_rw [ite_mul, zero_mul]
  simp

/-- The difference of the alternative of the block `j` and the instance `κ` is supported on the
single coordinate `⟨j, κ j⟩`. -/
lemma inner_mtParam0_sub_mtParam (κ : ∀ j, Fin (d j)) (j : Fin m)
    (y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪y, mtParam0 d ε κ j - mtParam d ε κ⟫ = -(10 * mtEps d ε j * y ⟨j, κ j⟩) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma]
  rw [← Finset.sum_erase_add _ _ (mem_univ j)]
  have hzero : ∀ j' ∈ univ.erase j,
      ∑ l : Fin (d j'), (mtParam0 d ε κ j - mtParam d ε κ) ⟨j', l⟩ * y ⟨j', l⟩ = 0 := by
    intro j' hj'
    refine sum_eq_zero fun l _ ↦ ?_
    have h : (mtParam0 d ε κ j - mtParam d ε κ) ⟨j', l⟩ = 0 := by
      change mtParam0 d ε κ j ⟨j', l⟩ - mtParam d ε κ ⟨j', l⟩ = 0
      rw [mtParam0_apply, mtParam_apply, ite_eq_right (mem_erase.1 hj').1]
      ring
    rw [h, zero_mul]
  rw [sum_eq_zero hzero, zero_add]
  have hterm : ∀ l : Fin (d j), (mtParam0 d ε κ j - mtParam d ε κ) ⟨j, l⟩ =
      if l = κ j then -(10 * mtEps d ε j) else 0 := by
    intro l
    change mtParam0 d ε κ j ⟨j, l⟩ - mtParam d ε κ ⟨j, l⟩ = _
    rw [mtParam0_apply, mtParam_apply, ite_eq_left rfl]
    split_ifs <;> ring
  simp_rw [hterm, ite_mul, zero_mul]
  simp

/-- The maximal value of an instance on the multi-task set is `10 ε`. -/
lemma supportFn_mtParam (hm : 0 < m) (hd : ∀ j, 0 < d j) (hε : 0 ≤ ε) (κ : ∀ j, Fin (d j)) :
    supportFn (multitaskSet d) (mtParam d ε κ) = 10 * ε := by
  rw [supportFn_multitaskSet hd]
  have hj : ∀ j, (⨆ l, mtParam d ε κ ⟨j, l⟩) = 10 * mtEps d ε j := by
    intro j
    have : Nonempty (Fin (d j)) := ⟨⟨0, hd j⟩⟩
    refine le_antisymm (ciSup_le fun l ↦ ?_) ?_
    · rw [mtParam_apply]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by norm_num) (mtEps_nonneg hε j)
    · refine le_trans (le_of_eq ?_) (le_ciSup (Finite.bddAbove_range _) (κ j))
      rw [mtParam_apply]
      simp
  simp_rw [hj]
  rw [← mul_sum, sum_mtEps hm hd]

/-- The value of a recommendation of the multi-task set is nonnegative. -/
lemma inner_mtParam_nonneg (hε : 0 ≤ ε) (κ : ∀ j, Fin (d j))
    {y : EuclideanSpace ℝ (Σ j, Fin (d j))} (hy : y ∈ multitaskSet d) :
    0 ≤ ⟪y, mtParam d ε κ⟫ := by
  rw [inner_mtParam]
  refine sum_nonneg fun j _ ↦ ?_
  have h1 : 0 ≤ y ⟨j, κ j⟩ := by
    rcases hy.1 ⟨j, κ j⟩ with h | h
    · rw [h]
    · rw [h]; norm_num
  have h2 : 0 ≤ mtEps d ε j := mtEps_nonneg hε j
  positivity

end COLT83
