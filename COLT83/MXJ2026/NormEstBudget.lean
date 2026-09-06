/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.NormEstSchedule

/-!
# Budget of the norm-estimation meta-algorithm

The total number of rounds `T = T₁ + N₂` of the meta-algorithm is at most
`10⁵ d log(4/δ) / ε²` (`NormEstParam.T_le`, blueprint `lem:multiscale_samples` and
`thm:norm_estimation`).

The multi-scale phase uses `T₁ = ∑_{j < J} s_j K_j` rounds with `s_j ≤ 8 d / t_j²` (since
`t_j < 2 √d` for `j < J`) and `K_j ≤ 3549 j + 5121 L` where `L = log (4/δ)`, so that
`T₁ ≤ (8d/ε²) ∑_j 4⁻ʲ (3549 j + 5121 L) ≤ 63736 d L / ε²`. The second phase uses at most
`max (d n, max_j s'_j K'_j) ≤ 32776 d L / ε²` rounds.
-/

@[expose] public section

open Real Finset

namespace COLT83

namespace NormEstParam

variable {ι : Type*} [Fintype ι] (P : NormEstParam)

lemma log_four_lt_L : log 4 < log (4 / P.δ) := by
  have hδ := P.hδ
  refine Real.log_lt_log (by norm_num) ?_
  rw [lt_div_iff₀ hδ.1]
  nlinarith [hδ.2]

lemma one_lt_L : 1 < log (4 / P.δ) := lt_trans ProbabilityTheory.one_lt_log_four P.log_four_lt_L

lemma d1386_lt_L : 1.3862943606 < log (4 / P.δ) := by
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith [P.log_four_lt_L]

lemma nsScale_sq (j : ℕ) : nsScale P.ε j ^ 2 = 4 ^ j * P.ε ^ 2 := by
  rw [nsScale, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
  norm_num

/-- For `j < J`, `s_j ≤ 8 d / t_j² = (8 d / ε²) 4⁻ʲ`. -/
lemma s_le (hd : 0 < Fintype.card ι) {j : ℕ} (hj : j < P.J ι) :
    (P.s ι j : ℝ) ≤ 8 * Fintype.card ι / P.ε ^ 2 * (1 / 4) ^ j := by
  have hε := P.hε.1
  have ht : 0 < nsScale P.ε j := nsScale_pos hε j
  have htd : nsScale P.ε j < 2 * √(Fintype.card ι) := nsScale_lt_of_lt_nsJ hε hj
  have hd' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hd
  have ht2 : nsScale P.ε j ^ 2 < 4 * Fintype.card ι := by
    have := Real.sq_sqrt hd'.le
    nlinarith [Real.sqrt_nonneg (Fintype.card ι : ℝ)]
  have h1 : (1 : ℝ) < 4 * Fintype.card ι / nsScale P.ε j ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hceil : (P.s ι j : ℝ) < 4 * Fintype.card ι / nsScale P.ε j ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsq := P.nsScale_sq j
  calc (P.s ι j : ℝ) ≤ 4 * Fintype.card ι / nsScale P.ε j ^ 2 + 1 := hceil.le
    _ ≤ 4 * Fintype.card ι / nsScale P.ε j ^ 2 + 4 * Fintype.card ι / nsScale P.ε j ^ 2 := by
        linarith
    _ = 8 * Fintype.card ι / P.ε ^ 2 * (1 / 4) ^ j := by
        rw [hsq, one_div_pow]
        field_simp
        ring

lemma log_one_div_nsDelta (j : ℕ) :
    log (1 / nsDelta P.δ j) = j * log 2 + log (4 / P.δ) := by
  have hδ := P.hδ.1
  rw [nsDelta, one_div_div, Real.log_div (by positivity) hδ.ne', Real.log_div (by norm_num) hδ.ne',
    Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- `K_j ≤ 5120 (j log 2 + L) + 1 ≤ 3549 j + 5121 L`. -/
lemma K_le (j : ℕ) : (P.K j : ℝ) ≤ 3549 * j + 5121 * log (4 / P.δ) := by
  have hL := P.one_lt_L
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hc : (P.K j : ℝ) < 5120 * log (1 / nsDelta P.δ j) + 1 :=
    Nat.ceil_lt_add_one (by rw [P.log_one_div_nsDelta]; nlinarith)
  rw [P.log_one_div_nsDelta] at hc
  nlinarith

lemma T₁_eq : (P.T₁ ι : ℝ) = ∑ j ∈ range (P.J ι), (P.s ι j : ℝ) * P.K j := by
  simp only [T₁, nsStart, Nat.cast_sum, Nat.cast_mul]
  rfl

/-- The multi-scale phase uses at most `63736 d L / ε²` rounds. -/
lemma T₁_le (hd : 0 < Fintype.card ι) :
    (P.T₁ ι : ℝ) ≤ 63736 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by
  have hε := P.hε.1
  have hL := P.d1386_lt_L
  have hd' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hd
  have hA := sum_pow_le (x := 1 / 4) (by norm_num) (by norm_num) (P.J ι)
  have hB := sum_mul_pow_le (x := 1 / 4) (by norm_num) (by norm_num) (P.J ι)
  have hA0 : 0 ≤ ∑ j ∈ range (P.J ι), (1 / 4 : ℝ) ^ j :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hB0 : 0 ≤ ∑ j ∈ range (P.J ι), (j : ℝ) * (1 / 4) ^ j :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  norm_num at hA hB
  have hc0 : 0 ≤ 8 * (Fintype.card ι : ℝ) / P.ε ^ 2 := by positivity
  calc (P.T₁ ι : ℝ) = ∑ j ∈ range (P.J ι), (P.s ι j : ℝ) * P.K j := P.T₁_eq
    _ ≤ ∑ j ∈ range (P.J ι), (8 * Fintype.card ι / P.ε ^ 2 * (1 / 4) ^ j)
          * (3549 * j + 5121 * log (4 / P.δ)) :=
        Finset.sum_le_sum fun j hj ↦ mul_le_mul (P.s_le hd (mem_range.1 hj)) (P.K_le j)
          (Nat.cast_nonneg _) (by positivity)
    _ = 8 * Fintype.card ι / P.ε ^ 2 * (3549 * ∑ j ∈ range (P.J ι), (j : ℝ) * (1 / 4) ^ j
          + 5121 * log (4 / P.δ) * ∑ j ∈ range (P.J ι), (1 / 4 : ℝ) ^ j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
    _ ≤ 8 * Fintype.card ι / P.ε ^ 2 * (3549 * (4 / 9) + 5121 * log (4 / P.δ) * (4 / 3)) := by
        gcongr
    _ ≤ 8 * Fintype.card ι / P.ε ^ 2 * (7967 * log (4 / P.δ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
    _ = 63736 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by ring

/-- `n ≤ 48 L / ε² + 1 ≤ 49 L / ε²`. -/
lemma n_le : (P.n : ℝ) ≤ 49 * log (4 / P.δ) / P.ε ^ 2 := by
  have hε := P.hε
  have hε0 := P.hε.1
  have hL := P.one_lt_L
  have hc : (P.n : ℝ) < 48 * log (4 / P.δ) / P.ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : 1 ≤ log (4 / P.δ) / P.ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hε.2, hε.1]
  calc (P.n : ℝ) ≤ 48 * log (4 / P.δ) / P.ε ^ 2 + 1 := hc.le
    _ ≤ 48 * log (4 / P.δ) / P.ε ^ 2 + log (4 / P.δ) / P.ε ^ 2 := by linarith
    _ = 49 * log (4 / P.δ) / P.ε ^ 2 := by ring

/-- For `j < J`, the additive estimator at scale `j` uses at most `32776 d L / ε²` rounds. -/
lemma s'_mul_K'_le (hd : 0 < Fintype.card ι) {j : ℕ} (hj : j < P.J ι) :
    (P.s' ι j * P.K' j : ℝ) ≤ 32776 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by
  have hε := P.hε.1
  have hL := P.one_lt_L
  have hd' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hd
  have hs : (P.s' ι j : ℝ) ≤ 8 * Fintype.card ι / P.ε ^ 2 * (1 / 4) ^ j := P.s_le hd hj
  have heq : 4096 * nsScale P.ε j ^ 2 * log (4 / P.δ) / P.ε ^ 2
      = 4096 * 4 ^ j * log (4 / P.δ) := by
    rw [P.nsScale_sq]
    field_simp
  have hK : (P.K' j : ℝ) < 4096 * 4 ^ j * log (4 / P.δ) + 1 := by
    have : (P.K' j : ℝ) < 4096 * nsScale P.ε j ^ 2 * log (4 / P.δ) / P.ε ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    rwa [heq] at this
  have h4 : (1 / 4 : ℝ) ^ j * 4 ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have h14 : (1 / 4 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (P.s' ι j * P.K' j : ℝ)
      ≤ (8 * Fintype.card ι / P.ε ^ 2 * (1 / 4) ^ j) * (4096 * 4 ^ j * log (4 / P.δ) + 1) :=
        mul_le_mul hs hK.le (Nat.cast_nonneg _) (by positivity)
    _ = 8 * Fintype.card ι / P.ε ^ 2
          * (4096 * log (4 / P.δ) * ((1 / 4) ^ j * 4 ^ j) + (1 / 4) ^ j) := by ring
    _ ≤ 8 * Fintype.card ι / P.ε ^ 2 * (4096 * log (4 / P.δ) * 1 + 1) := by
        rw [h4]
        gcongr
    _ ≤ 8 * Fintype.card ι / P.ε ^ 2 * (4097 * log (4 / P.δ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 32776 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by ring

/-- The second phase uses at most `32776 d L / ε²` rounds. -/
lemma N₂_le (hd : 0 < Fintype.card ι) :
    (P.N₂ ι : ℝ) ≤ 32776 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by
  have hε := P.hε.1
  have hL := P.one_lt_L
  have hd' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hd
  unfold N₂ nsN2
  rw [Nat.cast_max, max_le_iff]
  constructor
  · push_cast
    calc (Fintype.card ι : ℝ) * lnN P.ε P.δ ≤ Fintype.card ι * (49 * log (4 / P.δ) / P.ε ^ 2) :=
          mul_le_mul_of_nonneg_left P.n_le hd'.le
      _ = 49 * (Fintype.card ι * log (4 / P.δ) / P.ε ^ 2) := by ring
      _ ≤ 32776 * (Fintype.card ι * log (4 / P.δ) / P.ε ^ 2) := by gcongr; norm_num
      _ = 32776 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by ring
  · change (((range (P.J ι)).sup fun j ↦
      addS (Fintype.card ι) (nsScale P.ε j) * addK (nsScale P.ε j) P.ε P.δ : ℕ) : ℝ) ≤ _
    rcases (range (P.J ι)).eq_empty_or_nonempty with h | h
    · rw [h, Finset.sup_empty]
      simp only [bot_eq_zero', Nat.cast_zero]
      positivity
    · obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup _ h
        (fun j ↦ addS (Fintype.card ι) (nsScale P.ε j) * addK (nsScale P.ε j) P.ε P.δ)
      rw [hsup]
      push_cast
      exact P.s'_mul_K'_le hd (mem_range.1 hj)

/-- **Budget of the norm-estimation meta-algorithm**: `T ≤ 10⁵ d log(4/δ) / ε²`. -/
theorem T_le (hd : 0 < Fintype.card ι) :
    (P.T ι : ℝ) ≤ 100000 * Fintype.card ι * log (4 / P.δ) / P.ε ^ 2 := by
  have hL := P.one_lt_L
  have h0 : 0 ≤ (Fintype.card ι : ℝ) * log (4 / P.δ) / P.ε ^ 2 := by positivity
  have h1 := P.T₁_le hd
  have h2 := P.N₂_le hd
  rw [T_eq, Nat.cast_add]
  have e1 : 63736 * (Fintype.card ι : ℝ) * log (4 / P.δ) / P.ε ^ 2
      = 63736 * (Fintype.card ι * log (4 / P.δ) / P.ε ^ 2) := by ring
  have e2 : 32776 * (Fintype.card ι : ℝ) * log (4 / P.δ) / P.ε ^ 2
      = 32776 * (Fintype.card ι * log (4 / P.δ) / P.ε ^ 2) := by ring
  have e3 : 100000 * (Fintype.card ι : ℝ) * log (4 / P.δ) / P.ε ^ 2
      = 100000 * (Fintype.card ι * log (4 / P.δ) / P.ε ^ 2) := by ring
  rw [e3]
  rw [e1] at h1
  rw [e2] at h2
  linarith

end NormEstParam

end COLT83
