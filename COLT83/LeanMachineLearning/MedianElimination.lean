/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.Phased
public import COLT83.LeanMachineLearning.MedianEliminationSchedule
public import COLT83.LeanMachineLearning.MedianEliminationRound

/-!
# Median Elimination

Median Elimination (Even-Dar, Mannor, Mansour 2002) for `ε`-best arm identification among `K`
arms, as a phased algorithm (`MedianElim.medianElim`): the state is a pair of a map
`c : Fin K → 𝓐` from arms to actions and the set `S` of surviving arms; round `ℓ` pulls each
surviving arm `n_ℓ` times (round-robin, `MedianElim.roundArm`) and keeps the `⌈|S|/2⌉` arms with
the largest empirical means (`MedianElim.roundNext`), following the schedule of
`MedianEliminationSchedule.lean`. After `L = ⌈log₂ K⌉` rounds a single arm survives, which is the
recommendation (`MedianElim.meOut`); the budget is `MedianElim.budget K ε δ`.

`MedianElim.isPAC_medianElim` is the guarantee for candidate arms `c a ∈ 𝒳` of a linear Gaussian
bandit (blueprint `thm:median_elimination`, `cor:median_elimination_linear`): with probability at
least `1 - δ` the recommended arm `â` satisfies `⟪c â, θ⟫ ≥ max_a ⟪c a, θ⟫ - ε`, for every
reward vector `θ`. The proof is the phase-by-phase analysis of `Phased.lean`: the good states after
round `ℓ` are the surviving sets of the right size containing an arm within
`∑_{k < ℓ} ε_k` of the best arm (`MedianElim.goodSet`), and each round preserves goodness with
probability at least `1 - δ_ℓ` (`MedianElim.one_sub_le_measureReal_roundNext_mem`, from the
median counting argument of `MedianEliminationRound.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

universe u

namespace Learning.MedianElim

variable {𝓐 : Type*} [MeasurableSpace 𝓐] {K : ℕ} {ε δ : ℝ}

section goodSet

/-- The good surviving sets after `ℓ` rounds of Median Elimination for the means `μ` and the
target value `M`: sets of the scheduled size `s_ℓ` containing an arm with mean at least
`M - ∑_{k < ℓ} ε_k`. -/
def goodSet (μ : Fin K → ℝ) (M ε : ℝ) (ℓ : ℕ) : Set (Finset (Fin K)) :=
  {S | S.card = survivors K ℓ ∧ ∃ b ∈ S, M - ∑ k ∈ range ℓ, epsSched ε k ≤ μ b}

lemma measurableSet_goodSet (μ : Fin K → ℝ) (M ε : ℝ) (ℓ : ℕ) :
    MeasurableSet (goodSet μ M ε ℓ) :=
  .of_discrete

lemma measurable_roundNext {S : Finset (Fin K)} {s n m : ℕ} :
    Measurable fun y : Fin (s * n) → ℝ ↦ roundNext S s n m y :=
  Finset.measurable_topBy S m fun a ↦ measurable_roundScore a

/-- **One round of Median Elimination preserves goodness** (blueprint `lem:me_round`): from a good
surviving set after `ℓ` rounds, the surviving set after round `ℓ` is good with probability at
least `1 - δ_ℓ` over the noise of the round. -/
lemma one_sub_le_measureReal_roundNext_mem (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1)
    (μ : Fin K → ℝ) (M : ℝ) (ℓ : ℕ) (a₀ : Fin K) {S : Finset (Fin K)}
    (hS : S ∈ goodSet μ M ε ℓ) :
    1 - deltaSched δ ℓ ≤
      (Measure.pi fun _ : Fin (survivors K ℓ * numPulls ε δ ℓ) ↦ gaussianReal 0 1).real
        {η | roundNext S (survivors K ℓ) (numPulls ε δ ℓ) (survivors K (ℓ + 1))
          (fun j ↦ μ (roundArm S (survivors K ℓ) (numPulls ε δ ℓ) a₀ j) + η j) ∈
            goodSet μ M ε (ℓ + 1)} := by
  obtain ⟨hcard, b, hb, hMb⟩ := hS
  refine (one_sub_le_measureReal_round hcard a₀ μ (epsSched_pos hε ℓ)
    ⟨deltaSched_pos hδ.1 ℓ, deltaSched_lt_one hδ.2 ℓ⟩ (le_numPulls ε δ ℓ)).trans
    (measureReal_mono fun η hη ↦ ?_)
  simp only [goodSet, Set.mem_ofPred_eq, survivors_succ] at hη ⊢
  refine ⟨card_roundNext (by omega), ?_⟩
  obtain ⟨b', hb', hbb'⟩ := hη b hb
  refine ⟨b', hb', ?_⟩
  rw [sum_range_succ]
  linarith

end goodSet

section algorithm

/-- The design of round `ℓ` of Median Elimination in the state `(c, S)`: the arms of `S`
round-robin, each `n_ℓ` times, mapped to actions by `c`. -/
noncomputable def meAct (hK : 0 < K) (ε δ : ℝ) (ℓ : ℕ) (p : (Fin K → 𝓐) × Finset (Fin K))
    (j : Fin (survivors K ℓ * numPulls ε δ ℓ)) : 𝓐 :=
  p.1 (roundArm p.2 (survivors K ℓ) (numPulls ε δ ℓ) ⟨0, hK⟩ j)

lemma measurable_meAct (hK : 0 < K) (ε δ : ℝ) (ℓ : ℕ) (j : Fin (survivors K ℓ * numPulls ε δ ℓ)) :
    Measurable fun p ↦ meAct (𝓐 := 𝓐) hK ε δ ℓ p j :=
  measurable_from_prod_countable_left fun S ↦
    measurable_pi_apply (roundArm S (survivors K ℓ) (numPulls ε δ ℓ) ⟨0, hK⟩ j)

/-- The state update of round `ℓ` of Median Elimination: keep the arm map, select the
`s_{ℓ + 1}` arms with the largest empirical means. -/
noncomputable def meUpd (ε δ : ℝ) (ℓ : ℕ) (p : (Fin K → 𝓐) × Finset (Fin K))
    (y : Fin (survivors K ℓ * numPulls ε δ ℓ) → ℝ) : (Fin K → 𝓐) × Finset (Fin K) :=
  (p.1, roundNext p.2 (survivors K ℓ) (numPulls ε δ ℓ) (survivors K (ℓ + 1)) y)

lemma measurable_meUpd (ε δ : ℝ) (ℓ : ℕ) :
    Measurable (Function.uncurry (meUpd (𝓐 := 𝓐) (K := K) ε δ ℓ)) := by
  have h : Measurable fun q : Finset (Fin K) × (Fin (survivors K ℓ * numPulls ε δ ℓ) → ℝ) ↦
      roundNext q.1 (survivors K ℓ) (numPulls ε δ ℓ) (survivors K (ℓ + 1)) q.2 :=
    measurable_from_prod_countable_right fun S ↦ measurable_roundNext (S := S)
      (s := survivors K ℓ) (n := numPulls ε δ ℓ) (m := survivors K (ℓ + 1))
  have h2 : Measurable fun p : ((Fin K → 𝓐) × Finset (Fin K)) ×
      (Fin (survivors K ℓ * numPulls ε δ ℓ) → ℝ) ↦ (p.1.2, p.2) :=
    measurable_fst.snd.prodMk measurable_snd
  have h3 := h.comp h2
  exact measurable_fst.fst.prodMk h3

variable (𝓐) in
/-- **Median Elimination** as a phased algorithm on `K` arms with parameters `(ε, δ)`: the state is
`(c, S)` where `c : Fin K → 𝓐` maps arms to actions (fixed, initially `c₀`) and `S` is the set of
surviving arms (initially all arms); round `ℓ` pulls each arm of `S` `n_ℓ` times and keeps the
`s_{ℓ + 1}` arms with the largest empirical means. -/
noncomputable def medianElim (hK : 0 < K) (c₀ : Fin K → 𝓐) (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) :
    PhasedAlg 𝓐 ℝ ((Fin K → 𝓐) × Finset (Fin K)) where
  len ℓ := survivors K ℓ * numPulls ε δ ℓ
  len_pos ℓ := Nat.mul_pos (survivors_pos hK ℓ) (numPulls_pos hε hδ ℓ)
  init := (c₀, univ)
  act := meAct hK ε δ
  measurable_act := measurable_meAct hK ε δ
  upd := meUpd ε δ
  measurable_upd := measurable_meUpd ε δ

variable {hK : 0 < K} {c₀ : Fin K → 𝓐} {hε : 0 < ε} {hδ : δ ∈ Set.Ioo 0 1}

@[simp] lemma medianElim_len (ℓ : ℕ) :
    (medianElim 𝓐 hK c₀ hε hδ).len ℓ = survivors K ℓ * numPulls ε δ ℓ := rfl

@[simp] lemma medianElim_init : (medianElim 𝓐 hK c₀ hε hδ).init = (c₀, univ) := rfl

/-- The budget of Median Elimination: `L = ⌈log₂ K⌉` rounds take `budget K ε δ` samples. -/
lemma start_medianElim_numRounds :
    (medianElim 𝓐 hK c₀ hε hδ).start (numRounds K) = budget K ε δ := rfl

/-- The recommendation of Median Elimination: the action of the surviving arm (the smallest
surviving arm if several survive, the arm `0` if none does). -/
noncomputable def meOut (hK : 0 < K) (p : (Fin K → 𝓐) × Finset (Fin K)) : 𝓐 :=
  p.1 (if h : p.2.Nonempty then p.2.min' h else ⟨0, hK⟩)

lemma measurable_meOut (hK : 0 < K) : Measurable (meOut (𝓐 := 𝓐) hK) :=
  measurable_from_prod_countable_left fun S ↦
    measurable_pi_apply (if h : S.Nonempty then S.min' h else ⟨0, hK⟩)

omit [MeasurableSpace 𝓐] in
lemma meOut_singleton (c : Fin K → 𝓐) (b : Fin K) : meOut hK (c, {b}) = c b := by
  simp [meOut]

end algorithm

section linearGaussian

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} [MeasurableEq 𝒳]

/-- **Median Elimination is `(ε, δ)`-PAC** on candidate arms `c a ∈ 𝒳` of a linear Gaussian
bandit (blueprint `thm:median_elimination`, `cor:median_elimination_linear`): with probability at
least `1 - δ`, the recommended arm `â` satisfies `⟪c â, θ⟫ ≥ ⟪c a, θ⟫ - ε` for every arm `a`. -/
lemma isPAC_medianElim (hK : 0 < K) (c : Fin K → 𝒳) (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 1) :
    ((medianElim 𝒳 hK c hε hδ).toIdentAlg (numRounds K) (meOut hK) (measurable_meOut hK)).IsPAC.{u}
      (LinearBandit.linearGaussianEnv 𝒳) (fun θ x ↦ ∀ a, ⟪(c a : E), θ⟫ - ε ≤ ⟪(x : E), θ⟫) δ := by
  refine PhasedAlg.isPAC_toIdentAlg _ fun θ ↦ ?_
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨a₁, ha₁⟩ := Finite.exists_max fun a ↦ ⟪(c a : E), θ⟫
  refine ⟨fun ℓ ↦ {p | p.1 = c ∧ p.2 ∈ goodSet (fun a ↦ ⟪(c a : E), θ⟫) ⟪(c a₁ : E), θ⟫ ε ℓ},
    fun ℓ ↦ (measurable_fst (measurableSet_singleton c)).inter
      (measurable_snd (measurableSet_goodSet _ _ _ _)),
    ⟨rfl, by simp, a₁, mem_univ _, by simp⟩,
    ⟨deltaSched δ, fun ℓ ↦ (deltaSched_pos hδ.1 ℓ).le, sum_deltaSched_le hδ.1.le _, ?_⟩, ?_⟩
  · rintro ℓ - ⟨c', S⟩ ⟨hc, hS⟩
    have hc' : c' = c := hc
    subst hc'
    refine (one_sub_le_measureReal_roundNext_mem hε hδ _ _ ℓ ⟨0, hK⟩ hS).trans
      (measureReal_mono fun η hη ↦ ?_)
    exact ⟨rfl, hη⟩
  · rintro ⟨c', S⟩ ⟨hc, hcard, b, hb, hMb⟩ a
    have hc' : c' = c := hc
    subst hc'
    obtain ⟨b', rfl⟩ := Finset.card_eq_one.1 (hcard.trans (survivors_numRounds hK))
    rw [mem_singleton] at hb
    subst hb
    rw [meOut_singleton]
    have h1 := sum_epsSched_le hε.le (numRounds K)
    have h2 := ha₁ a
    linarith

end linearGaussian

end Learning.MedianElim
