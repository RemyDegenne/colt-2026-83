/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.NormEstSchedule
public import COLT83.MXJ2026.NormEstWindows

/-!
# The statistics of the norm-estimation meta-algorithm, as functions of the observations

* `winStat d a s K y`: the squared statistic of a window of `K` blocks of `s` rounds starting at
  round `a`, computed from the observation sequence `y`;
* `testH1 j y`: the test at scale `j` returns `H₁`;
* `jStar y`: the first scale whose test returns `H₀` (or `J`), the outcome of the multi-scale
  phase; it depends only on the observations of the first phase and is measurable;
* `addStat j y`, `lnRStat y`: the squared statistics of the second phase;
* `estimate y`: the final estimate.
-/

@[expose] public section

open Real Finset MeasureTheory

namespace COLT83

section WinStat

variable {ι : Type*} [Fintype ι]

/-- The squared statistic of a window of `K` blocks of `s` rounds starting at round `a`. -/
noncomputable def winStat (d a s K : ℕ) (y : ℕ → ℝ) : ℝ :=
  (∑ k : Fin K, (d : ℝ) * (((∑ ℓ : Fin s, y (a + k * s + ℓ)) / s) ^ 2 - 1 / s)) / K

lemma measurable_winStat (d a s K : ℕ) : Measurable (winStat d a s K) := by
  unfold winStat
  refine (Finset.measurable_sum _ fun k _ ↦ ?_).div_const _
  refine ((((Finset.measurable_sum _ fun ℓ _ ↦ ?_).div_const _).pow_const 2).sub_const _
    ).const_mul _
  exact measurable_pi_apply (a + k * s + ℓ)

lemma winStat_congr {d a s K : ℕ} {y y' : ℕ → ℝ} (h : ∀ r, a ≤ r → r < a + s * K → y r = y' r) :
    winStat d a s K y = winStat d a s K y' := by
  unfold winStat
  have hk : ∀ k : Fin K, (∑ ℓ : Fin s, y (a + k * s + ℓ)) = ∑ ℓ : Fin s, y' (a + k * s + ℓ) := by
    intro k
    refine Finset.sum_congr rfl fun ℓ _ ↦ h _ (by omega) ?_
    have : (k + 1) * s ≤ K * s := Nat.mul_le_mul_right _ k.2
    rw [Nat.succ_mul] at this
    have := ℓ.2
    rw [mul_comm s]
    omega
  simp_rw [hk]

/-- The statistic of a window whose observations are `⟪radDir (u k), θ⟫ + e k ℓ` is the
Rademacher block statistic `rbStat`. -/
lemma winStat_eq_rbStat {a s K : ℕ} (hs : 0 < s) (θ : EuclideanSpace ℝ ι) (u : Fin K → ι → Bool)
    (e : Fin K → Fin s → ℝ) {y : ℕ → ℝ}
    (hy : ∀ (k : Fin K) (ℓ : Fin s), y (a + k * s + ℓ) = inner ℝ (radDir (u k)) θ + e k ℓ) :
    winStat (Fintype.card ι) a s K y = rbStat s K θ (u, e) := by
  unfold winStat rbStat rbMean
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 3
  simp_rw [hy]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    add_div, mul_div_cancel_left₀ _ (by positivity : (s : ℝ) ≠ 0)]

end WinStat

namespace NormEstParam

variable {ι : Type*} [Fintype ι] (P : NormEstParam)

/-- The observation sequence of a history of length `T`, extended by `0`. -/
def yOf {𝓐 : Type*} {T : ℕ} (h : Fin T → 𝓐 × ℝ) : ℕ → ℝ :=
  fun t ↦ if ht : t < T then (h ⟨t, ht⟩).2 else 0

/-- The observation sequence of a history of rounds `0..n`, extended by `0`. -/
def yOfIic {𝓐 : Type*} {n : ℕ} (h : Iic n → 𝓐 × ℝ) : ℕ → ℝ :=
  fun t ↦ if ht : t ∈ Iic n then (h ⟨t, ht⟩).2 else 0

lemma measurable_yOf {𝓐 : Type*} [MeasurableSpace 𝓐] (T : ℕ) :
    Measurable (yOf : (Fin T → 𝓐 × ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun t ↦ ?_
  unfold yOf
  split_ifs
  exacts [(measurable_pi_apply _).snd, measurable_const]

lemma measurable_yOfIic {𝓐 : Type*} [MeasurableSpace 𝓐] (n : ℕ) :
    Measurable (yOfIic : (Iic n → 𝓐 × ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun t ↦ ?_
  unfold yOfIic
  split_ifs
  exacts [(measurable_pi_apply _).snd, measurable_const]

/-- The statistic of the test at scale `j`. -/
noncomputable def testStat (ι : Type*) [Fintype ι] (j : ℕ) (y : ℕ → ℝ) : ℝ :=
  winStat (Fintype.card ι) (P.start ι j) (P.s ι j) (P.K j) y

/-- The test at scale `j` returns `H₁`. -/
def testH1 (ι : Type*) [Fintype ι] (j : ℕ) (y : ℕ → ℝ) : Prop :=
  3 * nsScale P.ε j ^ 2 / 2 ≤ P.testStat ι j y

lemma measurableSet_testH1 (j : ℕ) : MeasurableSet {y | P.testH1 ι j y} :=
  measurableSet_le measurable_const (measurable_winStat _ _ _ _)

lemma testH1_congr {j : ℕ} (hj : j < P.J ι) {y y' : ℕ → ℝ} (h : ∀ r < P.T₁ ι, y r = y' r) :
    P.testH1 ι j y ↔ P.testH1 ι j y' := by
  unfold testH1 testStat
  rw [winStat_congr fun r h1 h2 ↦ h r ?_]
  have := P.start_lt_T₁ ι hj
  rw [start_succ] at this
  omega

open scoped Classical in
/-- The outcome of the multi-scale phase: the first scale whose test returns `H₀`, or `J`. -/
noncomputable def jStar (ι : Type*) [Fintype ι] (y : ℕ → ℝ) : ℕ :=
  Nat.find (p := fun j ↦ P.J ι ≤ j ∨ ¬ P.testH1 ι j y) ⟨P.J ι, Or.inl le_rfl⟩

open scoped Classical in
lemma jStar_le (y : ℕ → ℝ) : P.jStar ι y ≤ P.J ι :=
  Nat.find_min' _ (Or.inl le_rfl)

open scoped Classical in
lemma testH1_of_lt_jStar {y : ℕ → ℝ} {i : ℕ} (hi : i < P.jStar ι y) : P.testH1 ι i y := by
  have := Nat.find_min (p := fun j ↦ P.J ι ≤ j ∨ ¬ P.testH1 ι j y) ⟨P.J ι, Or.inl le_rfl⟩ hi
  push Not at this
  exact this.2

open scoped Classical in
lemma not_testH1_jStar {y : ℕ → ℝ} (h : P.jStar ι y < P.J ι) : ¬ P.testH1 ι (P.jStar ι y) y := by
  have := Nat.find_spec (p := fun j ↦ P.J ι ≤ j ∨ ¬ P.testH1 ι j y) ⟨P.J ι, Or.inl le_rfl⟩
  rcases this with h1 | h1
  · exact absurd h (not_lt.2 h1)
  · exact h1

open scoped Classical in
lemma jStar_eq_iff {y : ℕ → ℝ} {j : ℕ} :
    P.jStar ι y = j ↔ (P.J ι ≤ j ∨ ¬ P.testH1 ι j y) ∧ ∀ i < j, i < P.J ι ∧ P.testH1 ι i y := by
  unfold jStar
  rw [Nat.find_eq_iff]
  simp only [not_or, not_le, not_not]

/-- The outcome of the multi-scale phase depends only on the observations of the first phase. -/
lemma jStar_congr {y y' : ℕ → ℝ} (h : ∀ r < P.T₁ ι, y r = y' r) : P.jStar ι y = P.jStar ι y' := by
  have key : ∀ j, (P.J ι ≤ j ∨ ¬ P.testH1 ι j y) ↔ (P.J ι ≤ j ∨ ¬ P.testH1 ι j y') := by
    intro j
    rcases le_or_gt (P.J ι) j with hj | hj
    · simp [hj]
    · rw [P.testH1_congr hj h]
  classical
  apply le_antisymm
  · exact Nat.find_min' _ ((key _).2 (Nat.find_spec (p := fun j ↦ P.J ι ≤ j ∨ ¬ P.testH1 ι j y')
      ⟨P.J ι, Or.inl le_rfl⟩))
  · exact Nat.find_min' _ ((key _).1 (Nat.find_spec (p := fun j ↦ P.J ι ≤ j ∨ ¬ P.testH1 ι j y)
      ⟨P.J ι, Or.inl le_rfl⟩))

lemma measurableSet_jStar_eq (j : ℕ) : MeasurableSet {y | P.jStar ι y = j} := by
  classical
  have : {y | P.jStar ι y = j} = ({y | P.J ι ≤ j} ∪ {y | P.testH1 ι j y}ᶜ)
      ∩ ⋂ i, ⋂ (_ : i < j), ({y | i < P.J ι} ∩ {y | P.testH1 ι i y}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
      Set.mem_iInter, P.jStar_eq_iff]
  rw [this]
  refine ((MeasurableSet.const _).union (P.measurableSet_testH1 j).compl).inter
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
      (MeasurableSet.const _).inter (P.measurableSet_testH1 i))

lemma measurable_jStar : Measurable (P.jStar ι) :=
  measurable_to_countable' fun j ↦ P.measurableSet_jStar_eq j

/-- The squared statistic of the additive estimator at scale `j`. -/
noncomputable def addStat (ι : Type*) [Fintype ι] (j : ℕ) (y : ℕ → ℝ) : ℝ :=
  winStat (Fintype.card ι) (P.T₁ ι) (P.s' ι j) (P.K' j) y

/-- The squared-norm statistic of the large-norm estimator. -/
noncomputable def lnRStat (ι : Type*) [Fintype ι] (y : ℕ → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 fun i ↦ (∑ ℓ : Fin P.n, y (P.T₁ ι + (Fintype.equivFin ι i) * P.n + ℓ)) / P.n
    : EuclideanSpace ℝ ι)‖ ^ 2 - Fintype.card ι / P.n

lemma measurable_lnRStat : Measurable (P.lnRStat ι) := by
  unfold lnRStat
  have h1 : Measurable fun y : ℕ → ℝ ↦ (fun i : ι ↦
      (∑ ℓ : Fin P.n, y (P.T₁ ι + (Fintype.equivFin ι i) * P.n + ℓ)) / P.n) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    refine (Finset.measurable_sum _ fun ℓ _ ↦ ?_).div_const _
    exact measurable_pi_apply (P.T₁ ι + (Fintype.equivFin ι i) * P.n + ℓ)
  exact ((continuous_norm.measurable.comp
    ((PiLp.continuous_toLp 2 _).measurable.comp h1)).pow_const 2).sub_const _

/-- The statistic of the large-norm estimator computed from observations `θ i + e i ℓ` is
`lnR θ n e`. -/
lemma lnRStat_eq (θ : EuclideanSpace ℝ ι) (e : ι → Fin P.n → ℝ) {y : ℕ → ℝ}
    (hy : ∀ (i : ι) (ℓ : Fin P.n), y (P.T₁ ι + (Fintype.equivFin ι i) * P.n + ℓ) = θ i + e i ℓ) :
    P.lnRStat ι y = lnR θ P.n e := by
  unfold lnRStat lnR
  congr 3
  ext i
  simp only [PiLp.add_apply, lnDelta, hy, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (P.n : ℝ) ≠ 0 := by
    have := P.n_pos
    positivity
  field_simp

/-- The final estimate: `ε` if the multi-scale phase stops at scale `0`, the large-norm estimate
if it never stops, the additive estimate at the stopping scale otherwise. -/
noncomputable def estimate (ι : Type*) [Fintype ι] (y : ℕ → ℝ) : ℝ :=
  if P.jStar ι y = 0 then P.ε
  else if P.jStar ι y = P.J ι then √(max (P.lnRStat ι y) 0)
  else √(max (P.addStat ι (P.jStar ι y) y) 0)

lemma measurable_estimate : Measurable (P.estimate ι) := by
  have hF : ∀ j : ℕ, Measurable fun y : ℕ → ℝ ↦
      (if j = 0 then P.ε else if j = P.J ι then √(max (P.lnRStat ι y) 0)
        else √(max (P.addStat ι j y) 0)) := by
    intro j
    split_ifs
    · exact measurable_const
    · exact Real.continuous_sqrt.measurable.comp ((P.measurable_lnRStat).max measurable_const)
    · exact Real.continuous_sqrt.measurable.comp ((measurable_winStat _ _ _ _).max measurable_const)
  have h2 : Measurable fun p : ℕ × (ℕ → ℝ) ↦
      (if p.1 = 0 then P.ε else if p.1 = P.J ι then √(max (P.lnRStat ι p.2) 0)
        else √(max (P.addStat ι p.1 p.2) 0)) :=
    measurable_from_prod_countable_right fun j ↦ hF j
  exact h2.comp ((P.measurable_jStar).prodMk measurable_id)

end NormEstParam

end COLT83
