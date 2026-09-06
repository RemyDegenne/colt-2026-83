/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.NormEstParams

/-!
# The round schedule of the norm-estimation meta-algorithm

The meta-algorithm has two phases. Phase 1 (rounds `< T₁ = start J`) runs the scale tests
`j = 0, …, J - 1` in windows of `K_j` blocks of `s_j` rounds; each block plays one Rademacher
direction. Phase 2 (rounds `T₁ ≤ t < T₁ + N₂`) depends on the outcome `js` of the multi-scale
phase: if `js = 0` it idles, if `js = J` it plays the basis design (each basis vector `n` times),
otherwise it runs the additive estimator at scale `t_js` (`K(t_js)` blocks of `s(t_js)` rounds).

`rbBlock P js t = some b` means that round `t` belongs to a Rademacher block starting at round
`b`; `basisRound P js t = some i` means that round `t` plays the basis vector `e_i`.
-/

@[expose] public section

open Real Finset

namespace COLT83

/-- The parameters `ε ∈ (0, 1]`, `δ ∈ (0, 1)` of the norm-estimation algorithm. -/
structure NormEstParam where
  /-- The accuracy. -/
  ε : ℝ
  /-- The confidence. -/
  δ : ℝ
  hε : ε ∈ Set.Ioc 0 1
  hδ : δ ∈ Set.Ioo 0 1

namespace NormEstParam

variable {ι : Type*} [Fintype ι] (P : NormEstParam)

/-- The number of scales. -/
noncomputable def J (ι : Type*) [Fintype ι] : ℕ := nsJ (Fintype.card ι) P.ε P.hε.1

/-- The length of the first phase. -/
noncomputable def T₁ (ι : Type*) [Fintype ι] : ℕ := nsStart (Fintype.card ι) P.ε P.δ (P.J ι)

/-- The length of the second phase. -/
noncomputable def N₂ (ι : Type*) [Fintype ι] : ℕ := nsN2 (Fintype.card ι) P.ε P.δ P.hε.1

/-- The total budget. -/
noncomputable def T (ι : Type*) [Fintype ι] : ℕ := P.T₁ ι + P.N₂ ι

/-- The number of repetitions of each basis vector in the large-norm regime. -/
noncomputable def n : ℕ := lnN P.ε P.δ

/-- The block length of the test at scale `j`. -/
noncomputable def s (ι : Type*) [Fintype ι] (j : ℕ) : ℕ := nsS (Fintype.card ι) P.ε j

/-- The number of blocks of the test at scale `j`. -/
noncomputable def K (j : ℕ) : ℕ := nsK P.δ j

/-- The starting round of the test at scale `j`. -/
noncomputable def start (ι : Type*) [Fintype ι] (j : ℕ) : ℕ := nsStart (Fintype.card ι) P.ε P.δ j

/-- The block length of the additive estimator at scale `j`. -/
noncomputable def s' (ι : Type*) [Fintype ι] (j : ℕ) : ℕ := addS (Fintype.card ι) (nsScale P.ε j)

/-- The number of blocks of the additive estimator at scale `j`. -/
noncomputable def K' (j : ℕ) : ℕ := addK (nsScale P.ε j) P.ε P.δ

lemma T_eq : P.T ι = P.T₁ ι + P.N₂ ι := rfl

lemma start_succ (j : ℕ) : P.start ι (j + 1) = P.start ι j + P.s ι j * P.K j := nsStart_succ j

lemma start_mono {i j : ℕ} (hij : i ≤ j) : P.start ι i ≤ P.start ι j := nsStart_mono hij

lemma start_zero : P.start ι 0 = 0 := by simp [start, nsStart]

/-- The scale index of a round of the first phase: the `j` with `start j ≤ t < start (j+1)`
(a total function; only meaningful for `t < T₁`). -/
noncomputable def phaseOf (ι : Type*) [Fintype ι] (t : ℕ) : ℕ :=
  Nat.find (p := fun j ↦ t < P.start ι (j + 1) ∨ t < j + 1) ⟨t, Or.inr (Nat.lt_succ_self t)⟩

lemma phaseOf_spec (t : ℕ) : t < P.start ι (P.phaseOf ι t + 1) ∨ t < P.phaseOf ι t + 1 :=
  Nat.find_spec (p := fun j ↦ t < P.start ι (j + 1) ∨ t < j + 1) ⟨t, Or.inr (Nat.lt_succ_self t)⟩

lemma phaseOf_min (t : ℕ) {j : ℕ} (hj : j < P.phaseOf ι t) :
    P.start ι (j + 1) ≤ t ∧ j + 1 ≤ t := by
  have := Nat.find_min (p := fun j ↦ t < P.start ι (j + 1) ∨ t < j + 1)
    ⟨t, Or.inr (Nat.lt_succ_self t)⟩ hj
  push Not at this
  exact this

lemma start_phaseOf_le (t : ℕ) : P.start ι (P.phaseOf ι t) ≤ t := by
  rcases Nat.eq_zero_or_pos (P.phaseOf ι t) with h | h
  · rw [h, start_zero]
    exact Nat.zero_le t
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [hj]
    exact (P.phaseOf_min t (j := j) (by omega)).1

/-- If every window has positive length, `t < start (phaseOf t + 1)`. -/
lemma lt_start_phaseOf_succ (hpos : ∀ j, 0 < P.s ι j * P.K j) (t : ℕ) :
    t < P.start ι (P.phaseOf ι t + 1) := by
  have hge : ∀ j, j ≤ P.start ι j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      rw [start_succ]
      have := hpos j
      omega
  rcases P.phaseOf_spec (ι := ι) t with h | h
  · exact h
  · exact lt_of_lt_of_le h (hge _)

lemma phaseOf_eq_of_mem (hpos : ∀ j, 0 < P.s ι j * P.K j) {t j : ℕ} (h1 : P.start ι j ≤ t)
    (h2 : t < P.start ι (j + 1)) : P.phaseOf ι t = j := by
  rcases lt_trichotomy (P.phaseOf ι t) j with hlt | heq | hgt
  · have h3 := P.lt_start_phaseOf_succ hpos t
    have h4 : P.start ι (P.phaseOf ι t + 1) ≤ P.start ι j := P.start_mono hlt
    omega
  · exact heq
  · have := (P.phaseOf_min t hgt).1
    omega

section Positivity

variable (ι)

lemma L_pos : 0 < log (4 / P.δ) :=
  Real.log_pos (by rw [lt_div_iff₀ P.hδ.1]; linarith [P.hδ.2])

lemma n_pos : 0 < P.n :=
  Nat.ceil_pos.2 (div_pos (mul_pos (by norm_num) P.L_pos) (pow_pos P.hε.1 2))

lemma s_pos (hd : 0 < Fintype.card ι) (j : ℕ) : 0 < P.s ι j := by
  unfold s nsS testS
  exact Nat.ceil_pos.2 (div_pos (mul_pos (by norm_num) (by exact_mod_cast hd))
    (pow_pos (nsScale_pos P.hε.1 j) 2))

lemma K_pos (j : ℕ) : 0 < P.K j := by
  unfold K nsK testK
  refine Nat.ceil_pos.2 (mul_pos (by norm_num) (Real.log_pos ?_))
  have := nsDelta_mem P.hδ j
  rw [lt_one_div one_pos this.1]
  linarith [this.2]

lemma s'_pos (hd : 0 < Fintype.card ι) (j : ℕ) : 0 < P.s' ι j := by
  unfold s' addS
  exact Nat.ceil_pos.2 (div_pos (mul_pos (by norm_num) (by exact_mod_cast hd))
    (pow_pos (nsScale_pos P.hε.1 j) 2))

lemma K'_pos (j : ℕ) : 0 < P.K' j := by
  unfold K' addK
  exact Nat.ceil_pos.2 (div_pos (mul_pos (mul_pos (by norm_num) (pow_pos (nsScale_pos P.hε.1 j) 2))
    P.L_pos) (pow_pos P.hε.1 2))

lemma window_pos (hd : 0 < Fintype.card ι) (j : ℕ) : 0 < P.s ι j * P.K j :=
  Nat.mul_pos (P.s_pos ι hd j) (P.K_pos j)

lemma one_le_J (hd : 0 < Fintype.card ι) : 1 ≤ P.J ι := one_le_nsJ hd P.hε

lemma start_lt_T₁ {j : ℕ} (hj : j < P.J ι) : P.start ι (j + 1) ≤ P.T₁ ι :=
  P.start_mono hj

end Positivity

section Blocks

/-- The start of the Rademacher block containing round `t`, if any, given the outcome `js` of
the multi-scale phase. -/
noncomputable def rbBlock (js t : ℕ) : Option ℕ :=
  if t < P.T₁ ι then
    some (P.start ι (P.phaseOf ι t)
      + (t - P.start ι (P.phaseOf ι t)) / P.s ι (P.phaseOf ι t) * P.s ι (P.phaseOf ι t))
  else if 0 < js ∧ js < P.J ι ∧ t - P.T₁ ι < P.s' ι js * P.K' js then
    some (P.T₁ ι + (t - P.T₁ ι) / P.s' ι js * P.s' ι js)
  else none

/-- The basis vector played at round `t`, if any. -/
noncomputable def basisRound (js t : ℕ) : Option ι :=
  if h : js = P.J ι ∧ P.T₁ ι ≤ t ∧ t - P.T₁ ι < Fintype.card ι * P.n then
    some ((Fintype.equivFin ι).symm
      ⟨(t - P.T₁ ι) / P.n, (Nat.div_lt_iff_lt_mul P.n_pos).2 h.2.2⟩)
  else none

variable {P}

lemma rbBlock_le {js t b : ℕ} (h : P.rbBlock (ι := ι) js t = some b) : b ≤ t := by
  unfold rbBlock at h
  split_ifs at h with h1 h2
  · have := Option.some_injective _ h
    rw [← this]
    have := P.start_phaseOf_le (ι := ι) t
    have := Nat.div_mul_le_self (t - P.start ι (P.phaseOf ι t)) (P.s ι (P.phaseOf ι t))
    omega
  · have := Option.some_injective _ h
    rw [← this]
    have := Nat.div_mul_le_self (t - P.T₁ ι) (P.s' ι js)
    omega

lemma rbBlock_self (hd : 0 < Fintype.card ι) {js t b : ℕ} (h : P.rbBlock (ι := ι) js t = some b) :
    P.rbBlock (ι := ι) js b = some b := by
  have hpos := P.window_pos ι hd
  have hb := rbBlock_le h
  unfold rbBlock at h ⊢
  split_ifs at h with h1 h2
  · have hbt := Option.some_injective _ h
    set j := P.phaseOf ι t with hj
    have hs := P.s_pos ι hd j
    have h3 := P.lt_start_phaseOf_succ hpos t
    have h4 := P.start_phaseOf_le (ι := ι) t
    have h5 : P.start ι j ≤ b := by
      rw [← hbt]
      exact Nat.le_add_right _ _
    have h6 : P.phaseOf ι b = j :=
      P.phaseOf_eq_of_mem hpos h5 (lt_of_le_of_lt hb h3)
    rw [ite_eq_left (lt_of_le_of_lt hb h1), h6]
    congr 2
    rw [← hbt, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hs]
  · have hbt := Option.some_injective _ h
    have hs := P.s'_pos ι hd js
    have h5 : P.T₁ ι ≤ b := by
      rw [← hbt]
      exact Nat.le_add_right _ _
    have hcond : b - P.T₁ ι < P.s' ι js * P.K' js := by
      rw [← hbt, Nat.add_sub_cancel_left]
      exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) h2.2.2
    rw [ite_eq_right (not_lt.2 h5), ite_eq_left ⟨h2.1, h2.2.1, hcond⟩]
    congr 2
    rw [← hbt, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hs]

/-- Rounds of window `j` of the first phase: round `start j + k s_j + ℓ` belongs to the block
starting at `start j + k s_j`. -/
lemma rbBlock_window (hd : 0 < Fintype.card ι) (js : ℕ) {j : ℕ} (hj : j < P.J ι) {k ℓ : ℕ}
    (hk : k < P.K j) (hℓ : ℓ < P.s ι j) :
    P.rbBlock (ι := ι) js (P.start ι j + k * P.s ι j + ℓ) = some (P.start ι j + k * P.s ι j) := by
  have hpos := P.window_pos ι hd
  have hs := P.s_pos ι hd j
  have hlt : P.start ι j + k * P.s ι j + ℓ < P.start ι (j + 1) := by
    rw [start_succ]
    have : (k + 1) * P.s ι j ≤ P.K j * P.s ι j := Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at this
    rw [mul_comm (P.s ι j)]
    omega
  have hT : P.start ι j + k * P.s ι j + ℓ < P.T₁ ι := lt_of_lt_of_le hlt (P.start_lt_T₁ ι hj)
  have hph : P.phaseOf ι (P.start ι j + k * P.s ι j + ℓ) = j :=
    P.phaseOf_eq_of_mem hpos (by omega) hlt
  unfold rbBlock
  rw [ite_eq_left hT, hph]
  congr 2
  rw [Nat.add_assoc, Nat.add_sub_cancel_left, mul_comm k, Nat.mul_add_div hs,
    Nat.div_eq_of_lt hℓ, add_zero, mul_comm]

lemma basisRound_of_lt {js t : ℕ} (ht : t < P.T₁ ι) : P.basisRound (ι := ι) js t = none := by
  unfold basisRound
  rw [dite_eq_right]
  omega

/-- Rounds of the additive estimator at scale `js` (`0 < js < J`): round `T₁ + k s' + ℓ` belongs
to the block starting at `T₁ + k s'`. -/
lemma rbBlock_add (hd : 0 < Fintype.card ι) {js : ℕ} (hjs : 0 < js) (hjJ : js < P.J ι) {k ℓ : ℕ}
    (hk : k < P.K' js) (hℓ : ℓ < P.s' ι js) :
    P.rbBlock (ι := ι) js (P.T₁ ι + k * P.s' ι js + ℓ) = some (P.T₁ ι + k * P.s' ι js) := by
  have hs := P.s'_pos ι hd js
  have hlt : k * P.s' ι js + ℓ < P.s' ι js * P.K' js := by
    have : (k + 1) * P.s' ι js ≤ P.K' js * P.s' ι js := Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at this
    rw [mul_comm (P.s' ι js)]
    omega
  unfold rbBlock
  rw [ite_eq_right (by omega),
    ite_eq_left ⟨hjs, hjJ, by rw [Nat.add_assoc, Nat.add_sub_cancel_left]; exact hlt⟩]
  congr 2
  rw [Nat.add_assoc, Nat.add_sub_cancel_left, mul_comm k, Nat.mul_add_div hs,
    Nat.div_eq_of_lt hℓ, add_zero, mul_comm]

lemma basisRound_of_ne {js t : ℕ} (hjs : js ≠ P.J ι) : P.basisRound (ι := ι) js t = none := by
  unfold basisRound
  rw [dite_eq_right]
  exact fun h ↦ hjs h.1

/-- Rounds of the basis design (`js = J`): round `T₁ + (equivFin i) n + ℓ` plays `e_i`. -/
lemma basisRound_basis (i : ι) {ℓ : ℕ} (hℓ : ℓ < P.n) :
    P.basisRound (ι := ι) (P.J ι) (P.T₁ ι + (Fintype.equivFin ι i) * P.n + ℓ) = some i := by
  have hn := P.n_pos
  have hlt : (Fintype.equivFin ι i) * P.n + ℓ < Fintype.card ι * P.n := by
    have : ((Fintype.equivFin ι i : ℕ) + 1) * P.n ≤ Fintype.card ι * P.n :=
      Nat.mul_le_mul_right _ (Fintype.equivFin ι i).2
    rw [Nat.succ_mul] at this
    omega
  unfold basisRound
  rw [dite_eq_left ⟨rfl, Nat.le_add_right_of_le (Nat.le_add_right _ _),
    by rw [Nat.add_assoc, Nat.add_sub_cancel_left]; exact hlt⟩]
  congr 1
  apply (Fintype.equivFin ι).symm_apply_eq.2
  ext
  simp only
  rw [Nat.add_assoc, Nat.add_sub_cancel_left, mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hℓ,
    add_zero]

lemma rbBlock_of_J {t : ℕ} (hT : P.T₁ ι ≤ t) : P.rbBlock (ι := ι) (P.J ι) t = none := by
  unfold rbBlock
  rw [ite_eq_right (not_lt.2 hT), ite_eq_right]
  omega

end Blocks

end NormEstParam

end COLT83
