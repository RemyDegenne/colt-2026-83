/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The schedule of Median Elimination

Median Elimination runs in rounds `ℓ = 0, 1, …, L - 1`. In round `ℓ` it pulls each of the
`s_ℓ` surviving arms `n_ℓ` times, then discards the worse half of them (rounded down), so that
`s_{ℓ+1} = ⌈s_ℓ / 2⌉`. The round accuracies and confidences are
`ε_ℓ = (ε / 4) (3/4)^ℓ` and `δ_ℓ = δ / 2^(ℓ+1)`, with `∑ ε_ℓ ≤ ε` and `∑ δ_ℓ ≤ δ`, and the
number of pulls is `n_ℓ = ⌈8 log(3/δ_ℓ) / ε_ℓ²⌉₊`. The algorithm stops at the first round `L`
with `s_L ≤ 1`.

This file defines the schedule and proves the budget bound
`N_ME(K, ε, δ) = ∑_{ℓ < L} s_ℓ n_ℓ ≤ (256 K / ε²) (9 log(3/δ) + 81 log 2) + 4 K`, hence
`N_ME(K, ε, δ) ≤ 16000 K log(3/δ) / ε²` for `ε ≤ 1`.

Blueprint: `def:me_schedule`, `lem:me_schedule_sums`, `def:pm_halving`, `lem:me_budget`.
-/

@[expose] public section

open Finset

namespace Learning.MedianElim

variable {ε δ : ℝ} {K ℓ : ℕ}

/-! ### Accuracy and confidence schedules -/

/-- Accuracy of round `ℓ`: `ε_ℓ = (ε / 4) (3/4)^ℓ`. -/
noncomputable def epsSched (ε : ℝ) (ℓ : ℕ) : ℝ := ε / 4 * (3 / 4) ^ ℓ

/-- Confidence of round `ℓ`: `δ_ℓ = δ / 2^(ℓ+1)`. -/
noncomputable def deltaSched (δ : ℝ) (ℓ : ℕ) : ℝ := δ / 2 ^ (ℓ + 1)

lemma epsSched_pos (hε : 0 < ε) (ℓ : ℕ) : 0 < epsSched ε ℓ := by
  unfold epsSched; positivity

lemma deltaSched_pos (hδ : 0 < δ) (ℓ : ℕ) : 0 < deltaSched δ ℓ := by
  unfold deltaSched; positivity

lemma deltaSched_lt_one (hδ : δ < 1) (ℓ : ℕ) : deltaSched δ ℓ < 1 := by
  rw [deltaSched, div_lt_one (by positivity)]
  exact hδ.trans_le (one_le_pow₀ (by norm_num))

/-- Partial sums of a geometric series with ratio in `[0, 1)`. -/
lemma sum_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    ∑ ℓ ∈ range L, r ^ ℓ ≤ 1 / (1 - r) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hr0 hr1
  rwa [← range_eq_Ico, pow_zero] at h

/-- The sum of the round accuracies is at most `ε`. -/
lemma sum_epsSched_le (hε : 0 ≤ ε) (L : ℕ) : ∑ ℓ ∈ range L, epsSched ε ℓ ≤ ε := by
  simp_rw [epsSched, ← mul_sum]
  calc ε / 4 * ∑ ℓ ∈ range L, (3 / 4 : ℝ) ^ ℓ ≤ ε / 4 * (1 / (1 - 3 / 4)) :=
    mul_le_mul_of_nonneg_left (sum_geom_le (by norm_num) (by norm_num) L) (by positivity)
  _ = ε := by ring

/-- The sum of the round confidences is at most `δ`. -/
lemma sum_deltaSched_le (hδ : 0 ≤ δ) (L : ℕ) : ∑ ℓ ∈ range L, deltaSched δ ℓ ≤ δ := by
  have h : ∀ ℓ, deltaSched δ ℓ = δ / 2 * (1 / 2) ^ ℓ := fun ℓ ↦ by
    rw [deltaSched, pow_succ, one_div_pow]; ring
  simp_rw [h, ← mul_sum]
  calc δ / 2 * ∑ ℓ ∈ range L, (1 / 2 : ℝ) ^ ℓ ≤ δ / 2 * (1 / (1 - 1 / 2)) :=
    mul_le_mul_of_nonneg_left (sum_geom_le (by norm_num) (by norm_num) L) (by positivity)
  _ = δ := by ring

lemma log_deltaSched (hδ : 0 < δ) (ℓ : ℕ) :
    Real.log (3 / deltaSched δ ℓ) = Real.log (3 / δ) + (ℓ + 1) * Real.log 2 := by
  rw [deltaSched, div_div_eq_mul_div, mul_div_right_comm,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

lemma log_deltaSched_pos (hδ : δ ∈ Set.Ioo 0 1) (ℓ : ℕ) :
    0 < Real.log (3 / deltaSched δ ℓ) := by
  refine Real.log_pos ?_
  rw [one_lt_div (deltaSched_pos hδ.1 ℓ)]
  linarith [deltaSched_lt_one hδ.2 ℓ]

/-! ### Number of pulls per round -/

/-- Number of pulls of each surviving arm in round `ℓ`: `n_ℓ = ⌈8 log(3/δ_ℓ) / ε_ℓ²⌉₊`. -/
noncomputable def numPulls (ε δ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌈8 * Real.log (3 / deltaSched δ ℓ) / epsSched ε ℓ ^ 2⌉₊

lemma le_numPulls (ε δ : ℝ) (ℓ : ℕ) :
    8 * Real.log (3 / deltaSched δ ℓ) / epsSched ε ℓ ^ 2 ≤ numPulls ε δ ℓ :=
  Nat.le_ceil _

lemma numPulls_pos (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (ℓ : ℕ) : 0 < numPulls ε δ ℓ := by
  refine Nat.ceil_pos.2 ?_
  have := log_deltaSched_pos hδ ℓ
  have := epsSched_pos hε ℓ
  positivity

/-- `n_ℓ < 8 log(3/δ_ℓ) / ε_ℓ² + 1`. -/
lemma numPulls_lt (hδ : δ ∈ Set.Ioo 0 1) (ℓ : ℕ) :
    (numPulls ε δ ℓ : ℝ) < 8 * Real.log (3 / deltaSched δ ℓ) / epsSched ε ℓ ^ 2 + 1 := by
  refine Nat.ceil_lt_add_one ?_
  have := log_deltaSched_pos hδ ℓ
  positivity

/-! ### Surviving arms and number of rounds -/

/-- Number of surviving arms at the start of round `ℓ`: `s_0 = K`, `s_{ℓ+1} = ⌈s_ℓ / 2⌉`. -/
def survivors (K : ℕ) : ℕ → ℕ
  | 0 => K
  | ℓ + 1 => (survivors K ℓ + 1) / 2

@[simp] lemma survivors_zero (K : ℕ) : survivors K 0 = K := rfl

lemma survivors_succ (K ℓ : ℕ) : survivors K (ℓ + 1) = (survivors K ℓ + 1) / 2 := rfl

lemma survivors_succ_le (K ℓ : ℕ) : survivors K (ℓ + 1) ≤ survivors K ℓ := by
  rw [survivors_succ]; omega

lemma survivors_le (K ℓ : ℕ) : survivors K ℓ ≤ K := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => exact (survivors_succ_le K ℓ).trans ih

lemma survivors_pos (hK : 0 < K) (ℓ : ℕ) : 0 < survivors K ℓ := by
  induction ℓ with
  | zero => simpa
  | succ ℓ ih => rw [survivors_succ]; omega

/-- `s_ℓ ≤ ⌊K / 2^ℓ⌋ + 1`. -/
lemma survivors_le_div_add_one (K ℓ : ℕ) : survivors K ℓ ≤ K / 2 ^ ℓ + 1 := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [survivors_succ, pow_succ, ← Nat.div_div_eq_div_mul]
    generalize K / 2 ^ ℓ = m at ih ⊢
    omega

lemma exists_survivors_le_one (K : ℕ) : ∃ ℓ, survivors K ℓ ≤ 1 :=
  ⟨K, by simpa [Nat.div_eq_of_lt K.lt_two_pow_self] using survivors_le_div_add_one K K⟩

/-- Number of rounds: the first `ℓ` with `s_ℓ ≤ 1`. -/
noncomputable def numRounds (K : ℕ) : ℕ := Nat.find (exists_survivors_le_one K)

lemma survivors_numRounds_le_one (K : ℕ) : survivors K (numRounds K) ≤ 1 :=
  Nat.find_spec (exists_survivors_le_one K)

lemma survivors_numRounds (hK : 0 < K) : survivors K (numRounds K) = 1 :=
  le_antisymm (survivors_numRounds_le_one K) (survivors_pos hK _)

lemma two_le_survivors_of_lt (hℓ : ℓ < numRounds K) : 2 ≤ survivors K ℓ := by
  have := Nat.find_min (exists_survivors_le_one K) hℓ
  omega

@[simp] lemma numRounds_zero : numRounds 0 = 0 := by simp [numRounds]

@[simp] lemma numRounds_one : numRounds 1 = 0 := by simp [numRounds]

/-- `s_ℓ ≤ K / 2^ℓ + 1`, as real numbers. -/
lemma survivors_le_add_one (K ℓ : ℕ) : (survivors K ℓ : ℝ) ≤ K / 2 ^ ℓ + 1 :=
  calc (survivors K ℓ : ℝ) ≤ ((K / 2 ^ ℓ + 1 : ℕ) : ℝ) := by
        exact_mod_cast survivors_le_div_add_one K ℓ
  _ ≤ K / 2 ^ ℓ + 1 := by
        have h : ((K / 2 ^ ℓ : ℕ) : ℝ) ≤ (K : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := Nat.cast_div_le
        push_cast at h ⊢
        linarith

/-- For `ℓ < L`, `s_ℓ ≤ 2 K / 2^ℓ`. -/
lemma survivors_le_two_mul (hℓ : ℓ < numRounds K) : (survivors K ℓ : ℝ) ≤ 2 * K / 2 ^ ℓ := by
  have h1 := survivors_le_add_one K ℓ
  have h2 : (2 : ℝ) ≤ survivors K ℓ := by exact_mod_cast two_le_survivors_of_lt hℓ
  rw [mul_div_assoc]
  linarith

/-! ### Total budget -/

/-- Total budget `N_ME(K, ε, δ) = ∑_{ℓ < L} s_ℓ n_ℓ`. -/
noncomputable def budget (K : ℕ) (ε δ : ℝ) : ℕ :=
  ∑ ℓ ∈ range (numRounds K), survivors K ℓ * numPulls ε δ ℓ

/-- Partial sums of `(ℓ + 1) r^ℓ` for `r ∈ [0, 1)`. -/
lemma sum_succ_mul_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    ∑ ℓ ∈ range L, (ℓ + 1 : ℝ) * r ^ ℓ ≤ 1 / (1 - r) ^ 2 := by
  have h : ∀ L : ℕ, (∑ ℓ ∈ range L, (ℓ + 1 : ℝ) * r ^ ℓ) * (1 - r) ^ 2 =
      1 - (L + 1) * r ^ L + L * r ^ (L + 1) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring
  rw [le_div_iff₀ (pow_pos (sub_pos.2 hr1) 2), h]
  have h1 : (L : ℝ) * r ^ (L + 1) ≤ L * r ^ L := by
    rw [pow_succ, ← mul_assoc]
    exact mul_le_of_le_one_right (by positivity) hr1.le
  have h2 : (L : ℝ) * r ^ L ≤ (L + 1) * r ^ L := by gcongr; linarith
  linarith

/-- Per-round bound: for `ℓ < L`,
`s_ℓ n_ℓ ≤ (256 K / ε²) (8/9)^ℓ (log(3/δ) + (ℓ+1) log 2) + 2 K (1/2)^ℓ`. -/
lemma survivors_mul_numPulls_le (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (hℓ : ℓ < numRounds K) :
    (survivors K ℓ * numPulls ε δ ℓ : ℝ) ≤
      256 * K / ε ^ 2 * ((8 / 9) ^ ℓ * (Real.log (3 / δ) + (ℓ + 1) * Real.log 2))
        + 2 * K * (1 / 2) ^ ℓ := by
  have hs := survivors_le_two_mul hℓ
  have hn := (numPulls_lt (ε := ε) hδ ℓ).le
  rw [log_deltaSched hδ.1] at hn
  have hkey : 8 * (Real.log (3 / δ) + (ℓ + 1) * Real.log 2) / epsSched ε ℓ ^ 2 =
      128 / ε ^ 2 * (16 / 9) ^ ℓ * (Real.log (3 / δ) + (ℓ + 1) * Real.log 2) := by
    have h : (16 / 9 : ℝ) ^ ℓ = (((3 / 4) ^ ℓ)⁻¹) ^ 2 := by
      rw [← inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h]
    unfold epsSched
    field_simp
    ring
  rw [hkey] at hn
  have hA : 0 ≤ Real.log (3 / δ) := Real.log_nonneg ((one_le_div hδ.1).2 (by linarith [hδ.2]))
  have hB : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc (survivors K ℓ * numPulls ε δ ℓ : ℝ)
      ≤ 2 * K / 2 ^ ℓ *
        (128 / ε ^ 2 * (16 / 9) ^ ℓ * (Real.log (3 / δ) + (ℓ + 1) * Real.log 2) + 1) :=
        mul_le_mul hs hn (by positivity) (by positivity)
  _ = 256 * K / ε ^ 2 * ((8 / 9) ^ ℓ * (Real.log (3 / δ) + (ℓ + 1) * Real.log 2))
        + 2 * K * (1 / 2) ^ ℓ := by
      have h1 : (8 / 9 : ℝ) ^ ℓ = (16 / 9) ^ ℓ / 2 ^ ℓ := by rw [← div_pow]; norm_num
      rw [h1, one_div_pow]
      field_simp
      ring

/-- Budget bound (blueprint `lem:me_budget`, first form):
`N_ME(K, ε, δ) ≤ (256 K / ε²) (9 log(3/δ) + 81 log 2) + 4 K`. -/
lemma budget_le (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (K : ℕ) :
    (budget K ε δ : ℝ) ≤ 256 * K / ε ^ 2 * (9 * Real.log (3 / δ) + 81 * Real.log 2) + 4 * K := by
  set A := Real.log (3 / δ) with hA_def
  set B := Real.log 2 with hB_def
  have hA : 0 ≤ A := Real.log_nonneg ((one_le_div hδ.1).2 (by linarith [hδ.2]))
  have hB : 0 ≤ B := Real.log_nonneg (by norm_num)
  have h89 := sum_geom_le (r := 8 / 9) (by norm_num) (by norm_num) (numRounds K)
  have h89' := sum_succ_mul_geom_le (r := 8 / 9) (by norm_num) (by norm_num) (numRounds K)
  have h12 := sum_geom_le (r := 1 / 2) (by norm_num) (by norm_num) (numRounds K)
  norm_num at h89 h89' h12
  calc (budget K ε δ : ℝ)
      = ∑ ℓ ∈ range (numRounds K), (survivors K ℓ * numPulls ε δ ℓ : ℝ) := by
        rw [budget]; push_cast; rfl
  _ ≤ ∑ ℓ ∈ range (numRounds K),
        (256 * K / ε ^ 2 * ((8 / 9) ^ ℓ * (A + (ℓ + 1) * B)) + 2 * K * (1 / 2) ^ ℓ) :=
      sum_le_sum fun ℓ hℓ ↦ survivors_mul_numPulls_le hε hδ (mem_range.1 hℓ)
  _ = 256 * K / ε ^ 2 * A * ∑ ℓ ∈ range (numRounds K), (8 / 9 : ℝ) ^ ℓ
        + 256 * K / ε ^ 2 * B * ∑ ℓ ∈ range (numRounds K), (ℓ + 1 : ℝ) * (8 / 9) ^ ℓ
        + 2 * K * ∑ ℓ ∈ range (numRounds K), (1 / 2 : ℝ) ^ ℓ := by
      rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun ℓ _ ↦ by ring
  _ ≤ 256 * K / ε ^ 2 * A * 9 + 256 * K / ε ^ 2 * B * 81 + 2 * K * 2 := by
      gcongr
  _ = 256 * K / ε ^ 2 * (9 * A + 81 * B) + 4 * K := by ring

/-- Budget bound, second form: for `ε ≤ 1`, `N_ME(K, ε, δ) ≤ 16000 K log(3/δ) / ε²`. -/
lemma budget_le_of_le_one (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) (K : ℕ) :
    (budget K ε δ : ℝ) ≤ 16000 * K * Real.log (3 / δ) / ε ^ 2 := by
  have h := budget_le hε.1 hδ K
  have hA : 1.0986122885 < Real.log (3 / δ) :=
    Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) (le_div_self (by norm_num) hδ.1 hδ.2.le))
  have hB := Real.log_two_lt_d9
  set A := Real.log (3 / δ) with hA_def
  set B := Real.log 2 with hB_def
  set c := (K : ℝ) / ε ^ 2 with hc_def
  have hc : 0 ≤ c := by positivity
  have hKc : (K : ℝ) ≤ c := by
    rw [hc_def, le_div_iff₀ (pow_pos hε.1 2)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg K) (pow_le_one₀ hε.1.le hε.2)
  have h1 := mul_le_mul_of_nonneg_left hB.le hc
  have h2 := mul_le_mul_of_nonneg_left hA.le hc
  calc (budget K ε δ : ℝ) ≤ 256 * K / ε ^ 2 * (9 * A + 81 * B) + 4 * K := h
  _ = 256 * c * (9 * A + 81 * B) + 4 * K := by rw [hc_def]; ring
  _ ≤ 16000 * c * A := by nlinarith
  _ = 16000 * K * A / ε ^ 2 := by rw [hc_def]; ring

end Learning.MedianElim
