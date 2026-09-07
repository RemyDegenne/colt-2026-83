/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.NormEstPlan

/-!
# Accuracy of the norm-estimation meta-algorithm

On the seed space, the estimate of the meta-algorithm is within `ε` of `‖θ‖` with probability at
least `1 - δ` (`nsMeasure_real_estimate_fail_le`).

The proof follows the paper (proof of Theorem 8): the event that some test of the multi-scale
phase is wrong has probability at most `3δ/8` (union bound over the scales,
`nsMeasure_real_bad_le`); if all tests are correct, the outcome `jsω` of the multi-scale phase
locates `‖θ‖` (`jStar_bounds`); the second phase then fails with probability at most `δ/2`,
and it is independent of the first phase (`nsMeasure_real_fail2_le`).
-/

@[expose] public section

open Real Finset MeasureTheory ProbabilityTheory Learning

namespace Maiti2026Power

namespace NormEstParam

variable {ι : Type*} [Fintype ι] (P : NormEstParam)

/-! ### The estimate only depends on the observations of the `T` rounds -/

lemma card_mul_n_le_N₂ : Fintype.card ι * P.n ≤ P.N₂ ι := le_max_left _ _

lemma s'_mul_K'_le_N₂ {j : ℕ} (hj : j < P.J ι) : P.s' ι j * P.K' j ≤ P.N₂ ι :=
  le_trans (Finset.le_sup (f := fun j ↦
    addS (Fintype.card ι) (nsScale P.ε j) * addK (nsScale P.ε j) P.ε P.δ) (mem_range.2 hj))
    (le_max_right _ _)

lemma lnIdx_lt (i : ι) (ℓ : Fin P.n) :
    P.T₁ ι + Fintype.equivFin ι i * P.n + ℓ < P.T₁ ι + Fintype.card ι * P.n := by
  have h1 : (Fintype.equivFin ι i : ℕ) + 1 ≤ Fintype.card ι := (Fintype.equivFin ι i).2
  have h2 : ((Fintype.equivFin ι i : ℕ) + 1) * P.n ≤ Fintype.card ι * P.n :=
    Nat.mul_le_mul_right _ h1
  have h3 : (ℓ : ℕ) < P.n := ℓ.2
  calc P.T₁ ι + Fintype.equivFin ι i * P.n + ℓ
      < P.T₁ ι + Fintype.equivFin ι i * P.n + P.n := by omega
    _ = P.T₁ ι + ((Fintype.equivFin ι i : ℕ) + 1) * P.n := by ring
    _ ≤ P.T₁ ι + Fintype.card ι * P.n := Nat.add_le_add_left h2 _

lemma lnRStat_congr {y y' : ℕ → ℝ}
    (h : ∀ r, P.T₁ ι ≤ r → r < P.T₁ ι + Fintype.card ι * P.n → y r = y' r) :
    P.lnRStat ι y = P.lnRStat ι y' := by
  have : (fun i ↦ (∑ ℓ : Fin P.n, y (P.T₁ ι + Fintype.equivFin ι i * P.n + ℓ)) / P.n)
      = fun i ↦ (∑ ℓ : Fin P.n, y' (P.T₁ ι + Fintype.equivFin ι i * P.n + ℓ)) / P.n := by
    funext i
    congr 1
    exact Finset.sum_congr rfl fun ℓ _ ↦ h _ (by omega) (P.lnIdx_lt i ℓ)
  unfold lnRStat
  rw [this]

lemma addStat_congr {j : ℕ} {y y' : ℕ → ℝ}
    (h : ∀ r, P.T₁ ι ≤ r → r < P.T₁ ι + P.s' ι j * P.K' j → y r = y' r) :
    P.addStat ι j y = P.addStat ι j y' :=
  winStat_congr h

lemma estimate_congr {y y' : ℕ → ℝ} (h : ∀ r < P.T ι, y r = y' r) :
    P.estimate ι y = P.estimate ι y' := by
  have hj : P.jStar ι y = P.jStar ι y' :=
    P.jStar_congr fun r hr ↦ h r (hr.trans_le (Nat.le_add_right _ _))
  unfold estimate
  rw [← hj]
  split_ifs with h0 hJ
  · rfl
  · rw [P.lnRStat_congr fun r _ hr2 ↦
      h r (hr2.trans_le (Nat.add_le_add_left P.card_mul_n_le_N₂ _))]
  · have hjJ : P.jStar ι y < P.J ι := lt_of_le_of_ne (P.jStar_le y) hJ
    rw [P.addStat_congr fun r _ hr2 ↦
      h r (hr2.trans_le (Nat.add_le_add_left (P.s'_mul_K'_le_N₂ hjJ) _))]

/-! ### The test outcomes locate the norm -/

/-- The test at scale `j` is correct for the reward vector `θ` on the observation sequence `y`:
it does not declare the norm large if `‖θ‖ ≤ t_j`, and declares it large if `2 t_j ≤ ‖θ‖`. -/
def testOK (ι : Type*) [Fintype ι] (θ : EuclideanSpace ℝ ι) (j : ℕ) (y : ℕ → ℝ) : Prop :=
  (‖θ‖ ≤ nsScale P.ε j → ¬ P.testH1 ι j y) ∧ (2 * nsScale P.ε j ≤ ‖θ‖ → P.testH1 ι j y)

/-- If all tests are correct, the outcome `jStar` of the multi-scale phase locates `‖θ‖`:
`‖θ‖ < 2ε` if `jStar = 0`, `‖θ‖ / 2 < t_{jStar} ≤ 2 ‖θ‖` if `0 < jStar < J` and `√d ≤ ‖θ‖` if
`jStar = J`. -/
lemma jStar_bounds (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) {y : ℕ → ℝ}
    (hOK : ∀ j < P.J ι, P.testOK ι θ j y) :
    (P.jStar ι y = 0 → ‖θ‖ < 2 * P.ε) ∧
    (0 < P.jStar ι y → P.jStar ι y < P.J ι →
      ‖θ‖ / 2 < nsScale P.ε (P.jStar ι y) ∧ nsScale P.ε (P.jStar ι y) ≤ 2 * ‖θ‖) ∧
    (P.jStar ι y = P.J ι → √(Fintype.card ι) ≤ ‖θ‖) := by
  have hJ := P.one_le_J ι hd
  refine ⟨fun h0 ↦ ?_, fun hpos hlt ↦ ?_, fun hJ' ↦ ?_⟩
  · have hn : ¬ P.testH1 ι (P.jStar ι y) y := P.not_testH1_jStar (by omega)
    rw [h0] at hn
    by_contra hc
    refine hn ((hOK 0 hJ).2 ?_)
    rw [nsScale, pow_zero, one_mul]
    exact not_lt.1 hc
  · obtain ⟨j, hj⟩ : ∃ j, P.jStar ι y = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have h1 : P.testH1 ι j y := P.testH1_of_lt_jStar (by omega)
    have h3 : nsScale P.ε j < ‖θ‖ := lt_of_not_ge fun h ↦ (hOK j (by omega)).1 h h1
    have h4 : ¬ P.testH1 ι (P.jStar ι y) y := P.not_testH1_jStar hlt
    have h6 : ‖θ‖ < 2 * nsScale P.ε (P.jStar ι y) := lt_of_not_ge fun h ↦ h4 ((hOK _ hlt).2 h)
    rw [hj, nsScale_succ] at h6 ⊢
    constructor <;> linarith
  · obtain ⟨j, hj⟩ : ∃ j, P.J ι = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hJ).symm⟩
    have h1 : P.testH1 ι j y := P.testH1_of_lt_jStar (by omega)
    have h3 : nsScale P.ε j < ‖θ‖ := lt_of_not_ge fun h ↦ (hOK j (by omega)).1 h h1
    have h4 : 2 * √(Fintype.card ι) ≤ nsScale P.ε (P.J ι) :=
      two_mul_sqrt_le_nsScale_nsJ P.hε.1
    rw [hj, nsScale_succ] at h4
    linarith

/-- If `jStar = 0` and `‖θ‖ < 2ε`, the estimate `ε` is accurate. -/
lemma abs_estimate_sub_le_of_jStar_eq_zero (θ : EuclideanSpace ℝ ι) {y : ℕ → ℝ}
    (h0 : P.jStar ι y = 0) (hθ : ‖θ‖ < 2 * P.ε) : |P.estimate ι y - ‖θ‖| ≤ P.ε := by
  unfold estimate
  rw [h0, ite_eq_left rfl]
  have := norm_nonneg θ
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ### Measurability and prefix representation on the seed space -/

variable [DecidableEq ι]

lemma measurable_yω (θ : EuclideanSpace ℝ ι) : Measurable (P.yω θ) :=
  measurable_pi_lambda _ fun t ↦
    (SeededAlg.measurable_seedStep (LinearBandit.measurable_uncurry_linearNoise _ θ) t).snd

lemma measurable_jsω (θ : EuclideanSpace ℝ ι) : Measurable (P.jsω θ) :=
  (P.measurable_jStar).comp (P.measurable_yω θ)

lemma measurableSet_jsω_eq (θ : EuclideanSpace ℝ ι) (j : ℕ) :
    MeasurableSet {ω | P.jsω θ ω = j} :=
  P.measurable_jsω θ (measurableSet_singleton j)

omit [DecidableEq ι] in
/-- Extension of a finite prefix by a default value. -/
def prefixExtend {α : Type*} [Inhabited α] (T : ℕ) (w : Fin T → α) : ℕ → α :=
  fun t ↦ if ht : t < T then w ⟨t, ht⟩ else default

omit [DecidableEq ι] in
lemma measurable_prefixExtend {α : Type*} [MeasurableSpace α] [Inhabited α] (T : ℕ) :
    Measurable (prefixExtend (α := α) T) := by
  refine measurable_pi_lambda _ fun t ↦ ?_
  unfold prefixExtend
  split_ifs
  exacts [measurable_pi_apply _, measurable_const]

lemma yω_prefixExtend (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) {r : ℕ}
    (hr : r < P.T₁ ι) :
    P.yω θ (prefixExtend (P.T₁ ι) fun t : Fin (P.T₁ ι) ↦ ω t) r = P.yω θ ω r := by
  unfold yω SeededAlg.seedFeedback
  refine congrArg Prod.snd (SeededAlg.seedStep_congr fun k hk ↦ ?_)
  simp [prefixExtend, hk.trans_lt hr]

lemma jsω_prefixExtend (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) :
    P.jsω θ (prefixExtend (P.T₁ ι) fun t : Fin (P.T₁ ι) ↦ ω t) = P.jsω θ ω :=
  P.jStar_congr fun _ hr ↦ P.yω_prefixExtend θ ω hr

lemma setOf_jsω_eq (θ : EuclideanSpace ℝ ι) (j : ℕ) :
    {ω | P.jsω θ ω = j} = (fun ω (t : Fin (P.T₁ ι)) ↦ ω t) ⁻¹'
      {w | P.jsω θ (prefixExtend (P.T₁ ι) w) = j} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [P.jsω_prefixExtend]

/-- The outcome of the multi-scale phase is independent of any function of the seeds and noises
of the rounds `T₁, T₁ + 1, …`. -/
lemma nsMeasure_real_jsω_inter_preimage_eq_mul (θ : EuclideanSpace ℝ ι) (j : ℕ) {β : Type*}
    [MeasurableSpace β] {g : (ℕ → (ι → Bool) × ℝ) → β}
    (hind : IndepFun (fun ω (t : Fin (P.T₁ ι)) ↦ ω t) g (nsMeasure ι)) {S : Set β}
    (hS : MeasurableSet S) :
    (nsMeasure ι).real ({ω | P.jsω θ ω = j} ∩ g ⁻¹' S)
      = (nsMeasure ι).real {ω | P.jsω θ ω = j} * (nsMeasure ι).real (g ⁻¹' S) := by
  have hS1 : MeasurableSet {w : Fin (P.T₁ ι) → (ι → Bool) × ℝ |
      P.jsω θ (prefixExtend (P.T₁ ι) w) = j} :=
    ((P.measurable_jsω θ).comp (measurable_prefixExtend _)) (measurableSet_singleton j)
  rw [P.setOf_jsω_eq, measureReal_def, measureReal_def, measureReal_def,
    hind.measure_inter_preimage_eq_mul _ _ hS1 hS, ENNReal.toReal_mul]

omit [DecidableEq ι] in
lemma nsMeasure_real_rbProj_preimage {a s K : ℕ} (hs : 0 < s)
    {S : Set ((Fin K → ι → Bool) × (Fin K → Fin s → ℝ))} (hS : MeasurableSet S) :
    (nsMeasure ι).real (rbProj a s K ⁻¹' S) = (rbMeasure ι s K).real S := by
  rw [measureReal_def, measureReal_def, ← Measure.map_apply measurable_rbProj hS,
    nsMeasure_map_rbProj hs]

omit [DecidableEq ι] in
lemma nsMeasure_real_lnProj_preimage {a n : ℕ} {S : Set (ι → Fin n → ℝ)} (hS : MeasurableSet S) :
    (nsMeasure ι).real (lnProj a n ⁻¹' S) = (lnNoise ι n).real S := by
  rw [measureReal_def, measureReal_def, ← Measure.map_apply measurable_lnProj hS,
    nsMeasure_map_lnProj]

/-! ### The bad event of the multi-scale phase -/

/-- The event that the test at scale `j` is wrong. -/
def badTest (θ : EuclideanSpace ℝ ι) (j : ℕ) : Set (ℕ → (ι → Bool) × ℝ) :=
  {ω | ¬ P.testOK ι θ j (P.yω θ ω)}

lemma nsMeasure_real_badTest_le (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) {j : ℕ}
    (hj : j < P.J ι) :
    (nsMeasure ι).real (P.badTest θ j) ≤ 3 * nsDelta P.δ j / 4 := by
  have ht : 0 < nsScale P.ε j := nsScale_pos P.hε.1 j
  have hδj := nsDelta_mem P.hδ j
  have hiff : ∀ ω, P.testH1 ι j (P.yω θ ω) ↔ 3 * nsScale P.ε j ^ 2 / 2
      ≤ rbStat (P.s ι j) (P.K j) θ (rbProj (P.start ι j) (P.s ι j) (P.K j) ω) := by
    intro ω
    unfold testH1
    rw [P.testStat_eq_rbStat hd θ ω hj]
  rcases le_or_gt ‖θ‖ (nsScale P.ε j) with hθ | hθ
  · have hsub : P.badTest θ j ⊆ rbProj (P.start ι j) (P.s ι j) (P.K j) ⁻¹'
        {p | 3 * nsScale P.ε j ^ 2 / 2 ≤ rbStat (P.s ι j) (P.K j) θ p} := by
      intro ω hω
      simp only [badTest, testOK, Set.mem_ofPred_eq, not_and_or, Classical.not_imp,
        not_not] at hω
      rcases hω with ⟨_, h⟩ | ⟨h, _⟩
      · exact (hiff ω).1 h
      · linarith
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    rw [nsMeasure_real_rbProj_preimage (P.s_pos ι hd j)
      (measurableSet_le measurable_const measurable_rbStat)]
    exact rbMeasure_real_test_h0_le hd ht hδj hθ
  rcases lt_or_ge ‖θ‖ (2 * nsScale P.ε j) with hθ2 | hθ2
  · have hsub : P.badTest θ j = ∅ := by
      ext ω
      simp only [badTest, testOK, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨fun h ↦ absurd h (not_le.2 hθ), fun h ↦ absurd h (not_le.2 hθ2)⟩
    rw [hsub, measureReal_empty]
    have := hδj.1
    positivity
  · have hsub : P.badTest θ j ⊆ rbProj (P.start ι j) (P.s ι j) (P.K j) ⁻¹'
        {p | rbStat (P.s ι j) (P.K j) θ p < 3 * nsScale P.ε j ^ 2 / 2} := by
      intro ω hω
      simp only [badTest, testOK, Set.mem_ofPred_eq, not_and_or, Classical.not_imp,
        not_not] at hω
      rcases hω with ⟨h, _⟩ | ⟨_, h⟩
      · linarith
      · exact not_le.1 fun h' ↦ h ((hiff ω).2 h')
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    rw [nsMeasure_real_rbProj_preimage (P.s_pos ι hd j)
      (measurableSet_lt measurable_rbStat measurable_const)]
    exact rbMeasure_real_test_h1_le hd ht hδj hθ2

/-- The event that some test of the multi-scale phase is wrong. -/
def bad (θ : EuclideanSpace ℝ ι) : Set (ℕ → (ι → Bool) × ℝ) :=
  ⋃ j ∈ range (P.J ι), P.badTest θ j

lemma nsMeasure_real_bad_le (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) :
    (nsMeasure ι).real (P.bad θ) ≤ 3 * P.δ / 8 :=
  (measureReal_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum fun _ hj ↦ P.nsMeasure_real_badTest_le hd θ (mem_range.1 hj)).trans
      (sum_nsDelta_le P.hδ.1.le _))

lemma testOK_of_notMem_bad {θ : EuclideanSpace ℝ ι} {ω : ℕ → (ι → Bool) × ℝ}
    (hb : ω ∉ P.bad θ) {j : ℕ} (hj : j < P.J ι) : P.testOK ι θ j (P.yω θ ω) := by
  by_contra h
  exact hb (Set.mem_biUnion (mem_range.2 hj) h)

/-! ### The failure events of the second phase -/

/-- The failure event of the second phase for the outcome `j` of the multi-scale phase: the
large-norm estimator is inaccurate if `j = J`, the additive estimator at scale `j` is inaccurate
otherwise. -/
def fail2 (θ : EuclideanSpace ℝ ι) (j : ℕ) : Set (ℕ → (ι → Bool) × ℝ) :=
  if j = P.J ι then lnProj (P.T₁ ι) P.n ⁻¹' {e | P.ε < |lnEst θ P.n e - ‖θ‖|}
  else rbProj (P.T₁ ι) (P.s' ι j) (P.K' j) ⁻¹'
    {p | P.ε / 2 < |√(max (rbStat (P.s' ι j) (P.K' j) θ p) 0) - ‖θ‖|}

/-- The estimate fails only if some test is wrong, or if the second phase fails at the outcome
of the first phase. -/
lemma fail_subset (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) :
    {ω | P.ε < |P.estimate ι (P.yω θ ω) - ‖θ‖|} ⊆ P.bad θ ∪
      ⋃ j ∈ Finset.Icc 1 (P.J ι), ((P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j) := by
  intro ω hω
  by_cases hb : ω ∈ P.bad θ
  · exact Or.inl hb
  refine Or.inr ?_
  obtain ⟨hb0, hbmid, hbJ⟩ := P.jStar_bounds hd θ fun j hj ↦ P.testOK_of_notMem_bad hb hj
  simp only [Set.mem_ofPred_eq] at hω
  have hle : P.jStar ι (P.yω θ ω) ≤ P.J ι := P.jStar_le (P.yω θ ω)
  have h0 : P.jStar ι (P.yω θ ω) ≠ 0 := fun h0 ↦
    absurd hω (not_lt.2 (P.abs_estimate_sub_le_of_jStar_eq_zero θ h0 (hb0 h0)))
  rw [Set.mem_iUnion₂]
  refine ⟨P.jsω θ ω, Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hle⟩, ⟨hb, rfl⟩, ?_⟩
  unfold fail2 jsω
  unfold estimate at hω
  rw [ite_eq_right h0] at hω
  by_cases hJ : P.jStar ι (P.yω θ ω) = P.J ι
  · rw [ite_eq_left hJ] at hω
    rw [ite_eq_left hJ]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rwa [P.lnRStat_eq_lnR hd θ ω hJ] at hω
  · rw [ite_eq_right hJ] at hω
    rw [ite_eq_right hJ]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have h := P.addStat_eq_rbStat hd θ ω (Nat.pos_of_ne_zero h0) (lt_of_le_of_ne hle hJ)
    unfold jsω at h
    rw [h] at hω
    exact lt_of_le_of_lt (half_le_self P.hε.1.le) hω

/-- The failure probability of the second phase at outcome `j`, given the outcome, is at most
`δ / 2`: the second phase is independent of the outcome, and its failure probability is at most
`3δ/8` (additive estimator) or `δ/2` (large-norm estimator) under the norm bounds implied by the
outcome. -/
lemma nsMeasure_real_fail2_le (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) {j : ℕ}
    (hj : 1 ≤ j) (hjJ : j ≤ P.J ι) :
    (nsMeasure ι).real ((P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j)
      ≤ (nsMeasure ι).real {ω | P.jsω θ ω = j} * (P.δ / 2) := by
  have hδ := P.hδ.1
  rcases Set.eq_empty_or_nonempty ((P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j}) with h | ⟨ω₀, hω₀, hj₀⟩
  · rw [h, Set.empty_inter, measureReal_empty]
    exact mul_nonneg measureReal_nonneg (by positivity)
  obtain ⟨_, hbmid, hbJ⟩ := P.jStar_bounds hd θ fun i hi ↦ P.testOK_of_notMem_bad hω₀ hi
  have hj₀' : P.jStar ι (P.yω θ ω₀) = j := hj₀
  rw [hj₀'] at hbmid hbJ
  have hsub : (P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j ⊆ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j :=
    Set.inter_subset_inter_left _ Set.inter_subset_right
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  unfold fail2
  split_ifs with hJ
  · have hS : MeasurableSet {e : ι → Fin P.n → ℝ | P.ε < |lnEst θ P.n e - ‖θ‖|} :=
      measurableSet_lt measurable_const
        (continuous_abs.measurable.comp ((measurable_lnEst θ P.n).sub_const _))
    rw [P.nsMeasure_real_jsω_inter_preimage_eq_mul θ j (indepFun_prefix_lnProj le_rfl) hS,
      nsMeasure_real_lnProj_preimage hS]
    exact mul_le_mul_of_nonneg_left (lnNoise_real_lnEst_gt_le θ hd P.hε P.hδ (hbJ hJ))
      measureReal_nonneg
  · obtain ⟨h1, h2⟩ := hbmid hj (lt_of_le_of_ne hjJ hJ)
    have hS : MeasurableSet {p : (Fin (P.K' j) → ι → Bool) × (Fin (P.K' j) → Fin (P.s' ι j) → ℝ) |
        P.ε / 2 < |√(max (rbStat (P.s' ι j) (P.K' j) θ p) 0) - ‖θ‖|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp
        ((Real.continuous_sqrt.measurable.comp
          (measurable_rbStat.max measurable_const)).sub_const _))
    rw [P.nsMeasure_real_jsω_inter_preimage_eq_mul θ j
      (indepFun_prefix_rbProj (P.s'_pos ι hd j) le_rfl) hS,
      nsMeasure_real_rbProj_preimage (P.s'_pos ι hd j) hS]
    refine mul_le_mul_of_nonneg_left ((rbMeasure_real_sqrt_addEst_gt_le hd P.hε P.hδ
      (le_nsScale P.hε.1 j) h1 h2).trans (by linarith)) measureReal_nonneg

lemma sum_real_jsω_eq_le (θ : EuclideanSpace ℝ ι) (s : Finset ℕ) :
    ∑ j ∈ s, (nsMeasure ι).real {ω | P.jsω θ ω = j} ≤ 1 := by
  rw [← measureReal_biUnion_finset]
  · exact measureReal_le_one
  · intro i _ j _ hij
    exact Set.disjoint_left.2 fun ω hi hj ↦ hij (hi.symm.trans hj)
  · exact fun j _ ↦ P.measurableSet_jsω_eq θ j

/-- **Accuracy of the norm-estimation meta-algorithm** on the seed space: the estimate is more
than `ε` away from `‖θ‖` with probability at most `7δ/8` (`3δ/8` for the multi-scale phase,
`δ/2` for the second phase). -/
theorem nsMeasure_real_estimate_fail_le (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) :
    (nsMeasure ι).real {ω | P.ε < |P.estimate ι (P.yω θ ω) - ‖θ‖|} ≤ 7 * P.δ / 8 := by
  have hδ0 := P.hδ.1
  calc (nsMeasure ι).real {ω | P.ε < |P.estimate ι (P.yω θ ω) - ‖θ‖|}
      ≤ (nsMeasure ι).real (P.bad θ ∪ ⋃ j ∈ Finset.Icc 1 (P.J ι),
          ((P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j)) :=
        measureReal_mono (P.fail_subset hd θ) (measure_ne_top _ _)
    _ ≤ (nsMeasure ι).real (P.bad θ) + (nsMeasure ι).real (⋃ j ∈ Finset.Icc 1 (P.J ι),
          ((P.bad θ)ᶜ ∩ {ω | P.jsω θ ω = j} ∩ P.fail2 θ j)) := measureReal_union_le _ _
    _ ≤ 3 * P.δ / 8 + ∑ j ∈ Finset.Icc 1 (P.J ι),
          (nsMeasure ι).real {ω | P.jsω θ ω = j} * (P.δ / 2) :=
        add_le_add (P.nsMeasure_real_bad_le hd θ) ((measureReal_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun _ hj ↦ P.nsMeasure_real_fail2_le hd θ (Finset.mem_Icc.1 hj).1
            (Finset.mem_Icc.1 hj).2))
    _ = 3 * P.δ / 8 + (∑ j ∈ Finset.Icc 1 (P.J ι), (nsMeasure ι).real {ω | P.jsω θ ω = j})
          * (P.δ / 2) := by rw [Finset.sum_mul]
    _ ≤ 3 * P.δ / 8 + 1 * (P.δ / 2) := by
        gcongr
        exact P.sum_real_jsω_eq_le θ _
    _ = 7 * P.δ / 8 := by ring

theorem one_sub_le_nsMeasure_real_estimate (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) :
    1 - P.δ ≤ (nsMeasure ι).real {ω | |P.estimate ι (P.yω θ ω) - ‖θ‖| ≤ P.ε} := by
  have hset : {ω | |P.estimate ι (P.yω θ ω) - ‖θ‖| ≤ P.ε}
      = {ω | P.ε < |P.estimate ι (P.yω θ ω) - ‖θ‖|}ᶜ := by
    ext ω
    simp
  have hm : MeasurableSet {ω | P.ε < |P.estimate ι (P.yω θ ω) - ‖θ‖|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      (((P.measurable_estimate).comp (P.measurable_yω θ)).sub_const _))
  rw [hset, probReal_compl_eq_one_sub hm]
  have hδ := P.hδ.1
  linarith [P.nsMeasure_real_estimate_fail_le hd θ]

/-! ### The output of the algorithm on the seed space -/

lemma yOf_seedFinHist (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) {r : ℕ}
    (hr : r < P.T ι) :
    yOf ((P.alg ι).seedFinHist (F θ) (P.T ι) ω) r = P.yω θ ω r := by
  rw [yOf, dite_eq_left hr]
  rfl

lemma estimate_yOf_seedFinHist (θ : EuclideanSpace ℝ ι) (ω : ℕ → (ι → Bool) × ℝ) :
    P.estimate ι (yOf ((P.alg ι).seedFinHist (F θ) (P.T ι) ω)) = P.estimate ι (P.yω θ ω) :=
  P.estimate_congr fun _ hr ↦ P.yOf_seedFinHist θ ω hr

lemma seedMeasure_alg : (P.alg ι).seedMeasure (gaussianReal 0 1) = nsMeasure ι := rfl

/-- **Accuracy of the norm-estimation meta-algorithm**, in the form required by the seeded PAC
guarantee `linearBandit_isPAC_fixedBudget_deterministic`. -/
theorem one_sub_le_seedMeasure_real_output (hd : 0 < Fintype.card ι) (θ : EuclideanSpace ℝ ι) :
    1 - P.δ ≤ ((P.alg ι).seedMeasure (gaussianReal 0 1)).real
      {ω | |P.output ι ((P.alg ι).seedFinHist
        (fun (x : unitBall ι) (e : ℝ) ↦ inner ℝ (x : EuclideanSpace ℝ ι) θ + e) (P.T ι) ω)
          - ‖θ‖| ≤ P.ε} := by
  have h : ∀ ω, P.output ι ((P.alg ι).seedFinHist
      (fun (x : unitBall ι) (e : ℝ) ↦ inner ℝ (x : EuclideanSpace ℝ ι) θ + e) (P.T ι) ω)
        = P.estimate ι (P.yω θ ω) := fun ω ↦ P.estimate_yOf_seedFinHist θ ω
  simp_rw [h]
  exact P.one_sub_le_nsMeasure_real_estimate hd θ

end NormEstParam

end Maiti2026Power
