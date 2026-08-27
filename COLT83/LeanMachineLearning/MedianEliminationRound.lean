/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Data.Finset.TopBy
public import COLT83.Mathlib.Probability.GaussianMGF
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# One round of Median Elimination

A round of Median Elimination with surviving set `S` of size `s` pulls every arm of `S` `n` times,
round-robin: the offset `j : Fin (s * n)` of the round is decoded as `(i, r) : Fin s × Fin n` and
the arm pulled is the `i`-th element of `S` in increasing order. At the end of the round, the
empirical mean of each arm is the average of its `n` observations, and the `⌈s / 2⌉` arms with
the largest empirical means survive.

This file defines the arm pulled at each offset (`roundArm`), the empirical means (`empMean`,
`roundScore`) and the surviving set (`roundNext`), proves the Gaussian tail bound for the
empirical means (`measureReal_le_empMean_le`, `measureReal_empMean_le_le`) and the main lemma
`one_sub_le_measureReal_round`: if every surviving arm is pulled `n ≥ 8 log(3/δ) / ε²` times, then
with probability at least `1 - δ` the best surviving arm after the round is within `ε` of the best
arm before the round.

Blueprint: `def:pm_top`, `def:median_elimination`, `lem:pm_empmean_tail`, `lem:me_round`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Learning.MedianElim

variable {K : ℕ} {S : Finset (Fin K)} {s n m : ℕ} {y : Fin (s * n) → ℝ}

/-! ### Definitions -/

/-- The arm pulled at offset `j` of a round with surviving set `S` of size `s` in which every arm is
pulled `n` times: the `i`-th element of `S` at the offsets `(i, r)`, `r < n`. If `S.card ≠ s` (never
the case along a run), the default arm `a₀`. -/
def roundArm (S : Finset (Fin K)) (s n : ℕ) (a₀ : Fin K) (j : Fin (s * n)) : Fin K :=
  if h : S.card = s then S.orderEmbOfFin h (finProdFinEquiv.symm j).1 else a₀

/-- The empirical mean of the `n` observations of the `i`-th arm of the round. -/
noncomputable def empMean (s n : ℕ) (y : Fin (s * n) → ℝ) (i : Fin s) : ℝ :=
  (∑ r : Fin n, y (finProdFinEquiv (i, r))) / n

/-- The score of the arm `a` at the end of the round: its empirical mean if `a ∈ S`, `0`
otherwise. -/
noncomputable def roundScore (S : Finset (Fin K)) (s n : ℕ) (y : Fin (s * n) → ℝ) (a : Fin K) : ℝ :=
  if h : S.card = s then
    (if ha : a ∈ S then empMean s n y ((S.orderIsoOfFin h).symm ⟨a, ha⟩) else 0) else 0

/-- The surviving set after the round: the `m` arms of `S` with the largest scores. -/
noncomputable def roundNext (S : Finset (Fin K)) (s n m : ℕ) (y : Fin (s * n) → ℝ) :
    Finset (Fin K) :=
  S.topBy (roundScore S s n y) m

/-! ### Basic properties -/

lemma roundArm_finProdFinEquiv (hS : S.card = s) (a₀ : Fin K) (i : Fin s) (r : Fin n) :
    roundArm S s n a₀ (finProdFinEquiv (i, r)) = S.orderEmbOfFin hS i := by
  rw [roundArm, dite_eq_left hS, Equiv.symm_apply_apply]

lemma roundScore_eq (hS : S.card = s) (y : Fin (s * n) → ℝ) {a : Fin K} (ha : a ∈ S) :
    roundScore S s n y a = empMean s n y ((S.orderIsoOfFin hS).symm ⟨a, ha⟩) := by
  rw [roundScore, dite_eq_left hS, dite_eq_left ha]

lemma roundNext_subset : roundNext S s n m y ⊆ S := topBy_subset

lemma card_roundNext (hm : m ≤ S.card) : (roundNext S s n m y).card = m := card_topBy hm

lemma orderEmbOfFin_orderIsoOfFin_symm (hS : S.card = s) {a : Fin K} (ha : a ∈ S) :
    S.orderEmbOfFin hS ((S.orderIsoOfFin hS).symm ⟨a, ha⟩) = a := by
  rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- Observations `μ (arm) + η` give scores `μ a + (average noise of a)` on `S`. -/
lemma roundScore_add (hS : S.card = s) (hn : 0 < n) (a₀ : Fin K) (μ : Fin K → ℝ)
    (η : Fin (s * n) → ℝ) {a : Fin K} (ha : a ∈ S) :
    roundScore S s n (fun j ↦ μ (roundArm S s n a₀ j) + η j) a =
      μ a + empMean s n η ((S.orderIsoOfFin hS).symm ⟨a, ha⟩) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [roundScore_eq hS _ ha]
  simp only [empMean, roundArm_finProdFinEquiv hS, orderEmbOfFin_orderIsoOfFin_symm hS ha,
    sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [add_div, mul_div_cancel_left₀ _ hn']

lemma measurable_empMean (i : Fin s) : Measurable fun y : Fin (s * n) → ℝ ↦ empMean s n y i := by
  unfold empMean
  fun_prop

lemma measurable_roundScore (a : Fin K) :
    Measurable fun y : Fin (s * n) → ℝ ↦ roundScore S s n y a := by
  unfold roundScore
  split_ifs
  · exact measurable_empMean _
  · exact measurable_const
  · exact measurable_const

/-! ### Tail bounds for the empirical means under standard Gaussian noise -/

/-- Each coordinate of the product of standard Gaussians is sub-Gaussian with proxy `1`. -/
lemma hasSubgaussianMGF_eval (j : Fin (s * n)) :
    HasSubgaussianMGF (fun η : Fin (s * n) → ℝ ↦ η j) 1
      (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1) := by
  have h := hasSubgaussianMGF_fun_id_gaussianReal 1
  rw [← (measurePreserving_eval (fun _ : Fin (s * n) ↦ gaussianReal 0 1) j).map_eq] at h
  exact HasSubgaussianMGF.of_map (Y := fun η : Fin (s * n) → ℝ ↦ η j)
    (measurable_pi_apply j).aemeasurable h

/-- The coordinates of the product of standard Gaussians are independent. -/
lemma iIndepFun_eval :
    iIndepFun (fun j (η : Fin (s * n) → ℝ) ↦ η j)
      (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

/-- The empirical mean of `n` i.i.d. `N(0,1)` coordinates is sub-Gaussian with proxy `1 / n`. -/
lemma hasSubgaussianMGF_empMean (hn : 0 < n) (i : Fin s) :
    HasSubgaussianMGF (fun η ↦ empMean s n η i) (1 / n)
      (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hind : iIndepFun (fun (r : Fin n) (η : Fin (s * n) → ℝ) ↦ η (finProdFinEquiv (i, r)))
      (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1) :=
    iIndepFun_eval.precomp (finProdFinEquiv.injective.comp (Prod.mk_right_injective i))
  have h := (HasSubgaussianMGF.sum_of_iIndepFun hind (c := fun _ ↦ 1) (s := univ)
    fun r _ ↦ hasSubgaussianMGF_eval _).const_mul (1 / n)
  convert h using 1
  · ext η
    simp [empMean, div_eq_inv_mul]
  · apply NNReal.coe_injective
    change (1 : ℝ) / n = (1 / n : ℝ) ^ 2 * ((∑ _ : Fin n, (1 : ℝ≥0) : ℝ≥0) : ℝ)
    simp
    field_simp

/-- Upper tail of an empirical mean of `n` i.i.d. `N(0,1)` coordinates
(blueprint `lem:pm_empmean_tail`). -/
lemma measureReal_le_empMean_le (hn : 0 < n) (i : Fin s) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1).real {η | u ≤ empMean s n η i} ≤
      Real.exp (-n * u ^ 2 / 2) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  refine ((hasSubgaussianMGF_empMean hn i).measure_ge_le hu).trans_eq ?_
  congr 1
  push_cast
  field_simp

/-- Lower tail of an empirical mean of `n` i.i.d. `N(0,1)` coordinates
(blueprint `lem:pm_empmean_tail`). -/
lemma measureReal_empMean_le_le (hn : 0 < n) (i : Fin s) {u : ℝ} (hu : 0 ≤ u) :
    (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1).real {η | empMean s n η i ≤ -u} ≤
      Real.exp (-n * u ^ 2 / 2) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h := (hasSubgaussianMGF_empMean hn i).neg.measure_ge_le hu
  simp only [Pi.neg_apply, le_neg] at h
  refine h.trans_eq ?_
  congr 1
  push_cast
  field_simp

/-! ### One round of Median Elimination -/

/-- **One round of Median Elimination** (blueprint `lem:me_round`): if every surviving arm is pulled
`n ≥ 8 log(3/δ)/ε²` times, then with probability at least `1 - δ` over the noise, the best surviving
arm after the round is within `ε` of the best arm before the round. -/
lemma one_sub_le_measureReal_round (hS : S.card = s) (a₀ : Fin K) (μ : Fin K → ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) (hn : 8 * Real.log (3 / δ) / ε ^ 2 ≤ n) :
    1 - δ ≤ (Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1).real
      {η | ∀ a ∈ S, ∃ b ∈ roundNext S s n ((s + 1) / 2) (fun j ↦ μ (roundArm S s n a₀ j) + η j),
        μ a - ε ≤ μ b} := by
  set P := Measure.pi fun _ : Fin (s * n) ↦ gaussianReal 0 1 with hP
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · simp only [hS0, forall_mem_empty_iff, Set.ofPred_true, probReal_univ]
    linarith [hδ.1]
  have hs : 0 < s := hS ▸ hSne.card_pos
  have hlog : 0 < Real.log (3 / δ) := Real.log_pos (by rw [one_lt_div hδ.1]; linarith [hδ.2])
  have hn0 : 0 < n := by
    have h : (0 : ℝ) < 8 * Real.log (3 / δ) / ε ^ 2 := div_pos (by linarith) (by positivity)
    exact_mod_cast h.trans_le hn
  -- the tail bound `exp (-n (ε/2)² / 2) ≤ δ / 3`
  have htail : Real.exp (-n * (ε / 2) ^ 2 / 2) ≤ δ / 3 := by
    have h8 : 8 * Real.log (3 / δ) ≤ n * ε ^ 2 := (div_le_iff₀ (by positivity)).1 hn
    have hlog' : Real.log (δ / 3) = -Real.log (3 / δ) := by rw [← Real.log_inv, inv_div]
    rw [← Real.exp_log (div_pos hδ.1 (by norm_num) : (0 : ℝ) < δ / 3), hlog']
    refine Real.exp_le_exp.2 ?_
    have : -n * (ε / 2) ^ 2 / 2 = -(n * ε ^ 2) / 8 := by ring
    linarith
  -- the best arm `a₁` of `S`
  obtain ⟨a₁, ha₁, hmax⟩ := S.exists_max_image μ hSne
  -- the noise scores and their tails
  have hup : ∀ a ∈ S, P.real {η | ε / 2 ≤ roundScore S s n η a} ≤ δ / 3 := fun a ha ↦ by
    have : {η | ε / 2 ≤ roundScore S s n η a} =
        {η | ε / 2 ≤ empMean s n η ((S.orderIsoOfFin hS).symm ⟨a, ha⟩)} := by
      ext η
      simp only [Set.mem_ofPred_eq, roundScore_eq hS η ha]
    rw [this]
    exact (measureReal_le_empMean_le hn0 _ (by positivity)).trans htail
  have hE₁ : P.real {η | roundScore S s n η a₁ ≤ -(ε / 2)} ≤ δ / 3 := by
    have : {η | roundScore S s n η a₁ ≤ -(ε / 2)} =
        {η | empMean s n η ((S.orderIsoOfFin hS).symm ⟨a₁, ha₁⟩) ≤ -(ε / 2)} := by
      ext η
      simp only [Set.mem_ofPred_eq, roundScore_eq hS η ha₁]
    rw [this]
    exact (measureReal_empMean_le_le hn0 _ (by positivity)).trans htail
  -- the number of arms with a large noise score, and Markov's inequality
  have hmeas : ∀ a, MeasurableSet {η : Fin (s * n) → ℝ | ε / 2 ≤ roundScore S s n η a} := fun a ↦
    measurableSet_le measurable_const (measurable_roundScore a)
  set N : (Fin (s * n) → ℝ) → ℝ :=
    fun η ↦ ∑ a ∈ S, ({η | ε / 2 ≤ roundScore S s n η a} : Set _).indicator 1 η with hN_def
  have hN : ∀ η, ((S.filter fun a ↦ ε / 2 ≤ roundScore S s n η a).card : ℝ) = N η := fun η ↦ by
    simp only [hN_def, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  have hNint : Integrable N P :=
    integrable_finsetSum S fun a _ ↦ (integrable_const 1).indicator (hmeas a)
  have hNnn : 0 ≤ᵐ[P] N :=
    Filter.Eventually.of_forall fun η ↦
      sum_nonneg fun a _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hE₂ : P.real {η | (s : ℝ) / 2 ≤ N η} ≤ 2 * δ / 3 := by
    have hmk := mul_meas_ge_le_integral_of_nonneg hNnn hNint ((s : ℝ) / 2)
    have hint : ∫ η, N η ∂P ≤ s * (δ / 3) := by
      rw [hN_def, integral_finsetSum S fun a _ ↦ (integrable_const 1).indicator (hmeas a)]
      calc ∑ a ∈ S, ∫ η, ({η | ε / 2 ≤ roundScore S s n η a} : Set _).indicator 1 η ∂P
          = ∑ a ∈ S, P.real {η | ε / 2 ≤ roundScore S s n η a} :=
            sum_congr rfl fun a _ ↦ integral_indicator_one (hmeas a)
      _ ≤ ∑ a ∈ S, δ / 3 := sum_le_sum hup
      _ = s * (δ / 3) := by rw [sum_const, hS, nsmul_eq_mul]
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    have h := hmk.trans hint
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  -- on the good event, the best surviving arm is within `ε` of `a₁`
  have hgood : ∀ η, ¬ roundScore S s n η a₁ ≤ -(ε / 2) → ¬ (s : ℝ) / 2 ≤ N η →
      ∀ a ∈ S, ∃ b ∈ roundNext S s n ((s + 1) / 2) (fun j ↦ μ (roundArm S s n a₀ j) + η j),
        μ a - ε ≤ μ b := by
    intro η h₁ h₂ a ha
    push Not at h₁ h₂
    set v := roundScore S s n (fun j ↦ μ (roundArm S s n a₀ j) + η j) with hv
    have hv' : ∀ b ∈ S, v b = μ b + roundScore S s n η b := fun b hb ↦ by
      rw [hv, roundScore_add hS hn0 a₀ μ η hb, roundScore_eq hS η hb]
    have hB : (S.filter fun b ↦ μ b < μ a₁ - ε ∧ v a₁ ≤ v b) ⊆
        S.filter fun b ↦ ε / 2 ≤ roundScore S s n η b := by
      intro b hb
      rw [mem_filter] at hb ⊢
      refine ⟨hb.1, ?_⟩
      rw [hv' b hb.1, hv' a₁ ha₁] at hb
      linarith [hb.2.1, hb.2.2]
    have hcard : (S.filter fun b ↦ μ b < μ a₁ - ε ∧ v a₁ ≤ v b).card < (s + 1) / 2 := by
      have h1 : ((S.filter fun b ↦ μ b < μ a₁ - ε ∧ v a₁ ≤ v b).card : ℝ) ≤ N η := by
        rw [← hN η]
        exact_mod_cast card_le_card hB
      have h2 : (s : ℝ) / 2 ≤ ((s + 1) / 2 : ℕ) := by
        have : s ≤ 2 * ((s + 1) / 2) := by omega
        have : (s : ℝ) ≤ 2 * ((s + 1) / 2 : ℕ) := by exact_mod_cast this
        linarith
      exact_mod_cast h1.trans_lt (h₂.trans_le h2)
    obtain ⟨b, hb, hb'⟩ := exists_mem_topBy_of_card_filter_lt (v := v) ha₁
      (by linarith : μ a₁ - ε ≤ μ a₁) (by rw [hS]; omega : (s + 1) / 2 ≤ S.card) hcard
    exact ⟨b, hb, by linarith [hmax a ha]⟩
  -- conclusion
  set A := {η : Fin (s * n) → ℝ | ∀ a ∈ S,
    ∃ b ∈ roundNext S s n ((s + 1) / 2) (fun j ↦ μ (roundArm S s n a₀ j) + η j),
      μ a - ε ≤ μ b} with hA
  have hsub : Aᶜ ⊆ {η | roundScore S s n η a₁ ≤ -(ε / 2)} ∪ {η | (s : ℝ) / 2 ≤ N η} := by
    intro η hη
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at h
    exact hη (hgood η h.1 h.2)
  have h1 : (1 : ℝ) ≤ P.real A + P.real Aᶜ := by
    rw [← probReal_univ (μ := P), ← Set.union_compl_self A]
    exact measureReal_union_le _ _
  have h2 : P.real Aᶜ ≤ δ := by
    calc P.real Aᶜ
        ≤ P.real ({η | roundScore S s n η a₁ ≤ -(ε / 2)} ∪ {η | (s : ℝ) / 2 ≤ N η}) :=
          measureReal_mono hsub
      _ ≤ P.real {η | roundScore S s n η a₁ ≤ -(ε / 2)} + P.real {η | (s : ℝ) / 2 ≤ N η} :=
          measureReal_union_le _ _
      _ ≤ δ := by linarith
  linarith

end Learning.MedianElim
