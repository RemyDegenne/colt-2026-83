/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.Mathlib.GaussianWidth
public import COLT83.MXJ2026.StructuredSets

/-!
# The `m`-sets and the hard instances of their lower bound

The `m`-set action set `mSet ι m` consists of the vectors of `{0, 1}^ι` with exactly `m`
coordinates equal to `1`; `msVec S` is the indicator vector of a subset `S` of size `m`
(`msVec_mem_mSet`). The hard instances of the lower bound (blueprint `def:msets`) are the
vectors `msParam Δ S = Δ ⬝ 1_S` for `S` of size `m`, with `Δ = 10 ε / m`: the value of a
recommendation is `Δ` times the size of its overlap with `S` (`inner_msParam`), the maximal
value on `mSet ι m` is `Δ m` (`supportFn_msParam`), and two instances `θ^(B)` and
`θ^(B ∪ {i})` differ only in the coordinate `i` (`inner_msParam_sub_insert`).
-/

@[expose] public section

open MeasureTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} {Δ : ℝ} {S B : Finset ι}

/-- The vector `Δ ⬝ 1_S` of `ℝ^ι`. -/
noncomputable def msParam (Δ : ℝ) (S : Finset ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if i ∈ S then Δ else 0

omit [Fintype ι] in
@[simp] lemma msParam_apply (Δ : ℝ) (S : Finset ι) (i : ι) :
    msParam Δ S i = if i ∈ S then Δ else 0 := rfl

/-- The indicator vector of `S`, an element of `mSet ι S.card`. -/
noncomputable def msVec (S : Finset ι) : EuclideanSpace ℝ ι := msParam 1 S

lemma msVec_mem_mSet (hS : S.card = m) : msVec S ∈ mSet ι m := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [msVec, msParam_apply]
    split_ifs <;> simp
  · change ∑ i, (if i ∈ S then (1 : ℝ) else 0) = m
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hS, nsmul_eq_mul, mul_one]

omit [DecidableEq ι] in
lemma mSet_nonempty (hm : m ≤ Fintype.card ι) : (mSet ι m).Nonempty := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset ι)) (by simpa using hm)
  exact ⟨msVec S, msVec_mem_mSet hS⟩

omit [DecidableEq ι] in
lemma norm_le_of_mem_mSet {x : EuclideanSpace ℝ ι} (hx : x ∈ mSet ι m) :
    ‖x‖ ≤ √(Fintype.card ι) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rcases hx.1 i with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num
    _ = Fintype.card ι := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The value of a recommendation under the instance `S`. -/
lemma inner_msParam (Δ : ℝ) (S : Finset ι) (y : EuclideanSpace ℝ ι) :
    ⟪y, msParam Δ S⟫ = Δ * ∑ i ∈ S, y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change ∑ i, (if i ∈ S then Δ else 0) * y i = _
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Two instances differing by one element of the support differ only in that coordinate. -/
lemma inner_msParam_sub_insert (Δ : ℝ) {i : ι} (hi : i ∉ B) (y : EuclideanSpace ℝ ι) :
    ⟪y, msParam Δ B - msParam Δ (insert i B)⟫ = -(Δ * y i) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change ∑ i', ((if i' ∈ B then Δ else 0) - if i' ∈ insert i B then Δ else 0) * y i' = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hzero : ∀ i' ∈ univ.erase i,
      ((if i' ∈ B then Δ else 0) - if i' ∈ insert i B then Δ else 0) * y i' = 0 := by
    intro i' hi'
    have hne : i' ≠ i := (Finset.mem_erase.1 hi').1
    simp [Finset.mem_insert, hne]
  rw [Finset.sum_eq_zero hzero, zero_add, ite_eq_right hi,
    ite_eq_left (Finset.mem_insert_self i B)]
  ring

/-- The value of a recommendation of `mSet ι m` is nonnegative. -/
lemma inner_msParam_nonneg (hΔ : 0 ≤ Δ) (S : Finset ι) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ mSet ι m) : 0 ≤ ⟪y, msParam Δ S⟫ := by
  rw [inner_msParam]
  refine mul_nonneg hΔ (Finset.sum_nonneg fun i _ ↦ ?_)
  rcases hy.1 i with h | h <;> simp [h]

/-- The maximal value of an instance of size `m` on `mSet ι m` is `Δ m`. -/
lemma supportFn_msParam (hΔ : 0 ≤ Δ) (hS : S.card = m) (hm : m ≤ Fintype.card ι) :
    supportFn (mSet ι m) (msParam Δ S) = Δ * m := by
  refine le_antisymm (supportFn_le (mSet_nonempty hm) fun y hy ↦ ?_) ?_
  · rw [inner_msParam]
    have h1 : ∑ i ∈ S, y i ≤ ∑ i, y i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ by
        rcases hy.1 i with h | h <;> simp [h]
    rw [hy.2] at h1
    exact mul_le_mul_of_nonneg_left h1 hΔ
  · refine le_trans (le_of_eq ?_)
      (inner_le_supportFn (fun x hx ↦ norm_le_of_mem_mSet hx) (msVec_mem_mSet hS) (msParam Δ S))
    rw [inner_msParam]
    have : ∀ i ∈ S, (msVec S) i = 1 := fun i hi ↦ by
      rw [msVec, msParam_apply, ite_eq_left hi]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hS, nsmul_eq_mul, mul_one]

end COLT83
