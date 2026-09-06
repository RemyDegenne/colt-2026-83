/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.RademacherTest
public import COLT83.MXJ2026.LargeNormStat

/-!
# Parameters and budget of the norm-estimation meta-algorithm

Scales `t_j = 2^j ε`, confidences `δ_j = δ / 2^(j+2)`, block lengths `s_j = ⌈4d/t_j²⌉` and block
numbers `K_j = ⌈5120 log(1/δ_j)⌉` of the multi-scale phase; the number of scales
`J = min {j : 2√d ≤ t_j}`; the starting rounds `start j = ∑ i < j, s_i K_i` of the tests; the
length `N₂` of the second phase; the total budget `T = start J + N₂`, and its bound
`T ≤ 10⁵ d log(4/δ) / ε²`.

Blueprint: `def:multiscale_algorithm`, `lem:multiscale_samples`, `def:meta_algorithm`,
`thm:norm_estimation` (budget clause).
-/

@[expose] public section

open Real Finset

namespace COLT83

section Scales

variable (d : ℕ) (ε δ : ℝ)

/-- The scale `t_j = 2^j ε`. -/
noncomputable def nsScale (j : ℕ) : ℝ := 2 ^ j * ε

/-- The confidence `δ_j = δ / 2^(j+2)` of the test at scale `j`. -/
noncomputable def nsDelta (j : ℕ) : ℝ := δ / 2 ^ (j + 2)

/-- The block length `s_j = ⌈4 d / t_j²⌉` of the test at scale `j`. -/
noncomputable def nsS (j : ℕ) : ℕ := testS d (nsScale ε j)

/-- The number of blocks `K_j = ⌈5120 log(1/δ_j)⌉` of the test at scale `j`. -/
noncomputable def nsK (j : ℕ) : ℕ := testK (nsDelta δ j)

lemma exists_two_mul_sqrt_le_nsScale (hε : 0 < ε) : ∃ j : ℕ, 2 * √d ≤ nsScale ε j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * √d / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_⟩
  rw [nsScale, ← div_le_iff₀ hε]
  exact hj.le

/-- The number of scales `J = min {j : 2 √d ≤ t_j}`. -/
noncomputable def nsJ (hε : 0 < ε) : ℕ := Nat.find (exists_two_mul_sqrt_le_nsScale d ε hε)

variable {d ε δ}

lemma nsScale_succ (j : ℕ) : nsScale ε (j + 1) = 2 * nsScale ε j := by
  rw [nsScale, nsScale, pow_succ]
  ring

lemma nsScale_pos (hε : 0 < ε) (j : ℕ) : 0 < nsScale ε j := by
  unfold nsScale
  positivity

lemma le_nsScale (hε : 0 < ε) (j : ℕ) : ε ≤ nsScale ε j := by
  rw [nsScale]
  have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

lemma nsScale_mono (hε : 0 < ε) {i j : ℕ} (hij : i ≤ j) : nsScale ε i ≤ nsScale ε j := by
  unfold nsScale
  gcongr
  norm_num

lemma two_mul_sqrt_le_nsScale_nsJ (hε : 0 < ε) : 2 * √d ≤ nsScale ε (nsJ d ε hε) :=
  Nat.find_spec (exists_two_mul_sqrt_le_nsScale d ε hε)

lemma nsScale_lt_of_lt_nsJ (hε : 0 < ε) {j : ℕ} (hj : j < nsJ d ε hε) :
    nsScale ε j < 2 * √d := by
  have := Nat.find_min (exists_two_mul_sqrt_le_nsScale d ε hε) hj
  exact not_le.1 this

lemma one_le_nsJ (hd : 0 < d) (hε : ε ∈ Set.Ioc 0 1) : 1 ≤ nsJ d ε hε.1 := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have := two_mul_sqrt_le_nsScale_nsJ (d := d) hε.1
  rw [h0, nsScale, pow_zero, one_mul] at this
  have hd1 : (1 : ℝ) ≤ √d := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hd
  linarith [hε.2]

lemma nsScale_nsJ_lt (hd : 0 < d) (hε : ε ∈ Set.Ioc 0 1) : nsScale ε (nsJ d ε hε.1) < 4 * √d := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 (one_le_nsJ hd hε))
  have := nsScale_lt_of_lt_nsJ (d := d) hε.1 (j := j) (by omega)
  rw [hj, nsScale_succ]
  linarith

lemma nsDelta_pos (hδ : 0 < δ) (j : ℕ) : 0 < nsDelta δ j := by
  unfold nsDelta
  positivity

lemma nsDelta_le (hδ : 0 < δ) (j : ℕ) : nsDelta δ j ≤ δ / 4 := by
  rw [nsDelta, div_le_div_iff_of_pos_left hδ (by positivity) (by norm_num)]
  calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)

lemma nsDelta_mem (hδ : δ ∈ Set.Ioo 0 1) (j : ℕ) : nsDelta δ j ∈ Set.Ioc 0 (1 / 4) :=
  ⟨nsDelta_pos hδ.1 j, (nsDelta_le hδ.1 j).trans (by linarith [hδ.2])⟩

/-- `∑ j < J, 3 δ_j / 4 ≤ 3 δ / 8`. -/
lemma sum_nsDelta_le (hδ : 0 ≤ δ) (J : ℕ) : ∑ j ∈ range J, 3 * nsDelta δ j / 4 ≤ 3 * δ / 8 := by
  have h : ∀ j, 3 * nsDelta δ j / 4 = 3 * δ / 16 * (1 / 2) ^ j := by
    intro j
    rw [nsDelta, pow_add, div_pow, one_pow]
    field_simp
    ring
  simp_rw [h, ← Finset.mul_sum]
  rw [geom_sum_eq (by norm_num) J]
  have h1 : ((1 : ℝ) / 2) ^ J ≥ 0 := by positivity
  have h2 : ((1 / 2 : ℝ) ^ J - 1) / (1 / 2 - 1) ≤ 2 := by
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  calc 3 * δ / 16 * (((1 / 2 : ℝ) ^ J - 1) / (1 / 2 - 1)) ≤ 3 * δ / 16 * 2 := by gcongr
    _ = 3 * δ / 8 := by ring

end Scales

section Budget

variable (d : ℕ) (ε δ : ℝ)

/-- The starting round `start j = ∑ i < j, s_i K_i` of the test at scale `j`. -/
noncomputable def nsStart (j : ℕ) : ℕ := ∑ i ∈ range j, nsS d ε i * nsK δ i

/-- The length of the second phase: `max (d n) (max_{j < J} s(t_j) K(t_j))`. -/
noncomputable def nsN2 (hε : 0 < ε) : ℕ :=
  max (d * lnN ε δ) ((range (nsJ d ε hε)).sup fun j ↦ addS d (nsScale ε j) * addK (nsScale ε j) ε δ)

/-- The total budget of the norm-estimation meta-algorithm. -/
noncomputable def nsBudget (hε : 0 < ε) : ℕ := nsStart d ε δ (nsJ d ε hε) + nsN2 d ε δ hε

variable {d ε δ}

lemma nsStart_succ (j : ℕ) : nsStart d ε δ (j + 1) = nsStart d ε δ j + nsS d ε j * nsK δ j := by
  rw [nsStart, nsStart, Finset.sum_range_succ]

lemma nsStart_mono {i j : ℕ} (hij : i ≤ j) : nsStart d ε δ i ≤ nsStart d ε δ j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hij)

/-- `∑ j < J, x^j ≤ 1 / (1 - x)` for `0 ≤ x < 1`. -/
lemma sum_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (J : ℕ) :
    ∑ j ∈ range J, x ^ j ≤ 1 / (1 - x) := by
  rw [geom_sum_eq hx1.ne J]
  have h1 : 0 ≤ x ^ J := pow_nonneg hx0 J
  have h2 : 0 < 1 - x := by linarith
  have e : (x ^ J - 1) / (x - 1) = (1 - x ^ J) / (1 - x) := by
    rw [div_eq_div_iff (sub_ne_zero.2 hx1.ne) (sub_ne_zero.2 hx1.ne')]
    ring
  rw [e]
  gcongr
  linarith

/-- `∑ j < J, j x^j = (x - J x^J + (J - 1) x^(J+1)) / (1 - x)²`. -/
lemma sum_mul_pow_eq {x : ℝ} (hx1 : x ≠ 1) (J : ℕ) :
    ∑ j ∈ range J, (j : ℝ) * x ^ j = (x - J * x ^ J + (J - 1) * x ^ (J + 1)) / (1 - x) ^ 2 := by
  have hne : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx1.symm)
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, div_add' _ _ _ hne, div_left_inj' hne]
    push_cast
    ring

/-- `∑ j < J, j x^j ≤ x / (1 - x)²` for `0 ≤ x ≤ 1`. -/
lemma sum_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (J : ℕ) :
    ∑ j ∈ range J, (j : ℝ) * x ^ j ≤ x / (1 - x) ^ 2 := by
  rw [sum_mul_pow_eq hx1.ne J]
  gcongr
  -- x - J x^J + (J - 1) x^(J+1) ≤ x  ⟸  (J - 1) x^(J+1) ≤ J x^J
  have h1 : 0 ≤ x ^ J := pow_nonneg hx0 J
  have h2 : (J - 1 : ℝ) * x ^ (J + 1) ≤ J * x ^ J := by
    rw [pow_succ]
    have : (J - 1 : ℝ) * x ≤ J := by nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    nlinarith
  linarith

end Budget

end COLT83
