/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.InfinitePiWindow
public import Maiti2026Power.MXJ2026.RademacherStat
public import Maiti2026Power.MXJ2026.LargeNormStat

/-!
# Windows of the seed-noise sequence of the norm-estimation algorithm

The norm-estimation algorithm is a seeded algorithm whose seeds are uniform Boolean vectors and
whose noises are standard Gaussians; its seed-noise sequence has law `nsMeasure ι`, the product
over the rounds of `uniformBoolVec ι ⊗ N(0, 1)`.

* `rbProj a s K`: the seeds at the block starts and the noises of a window of `K` blocks of
  length `s` starting at round `a`; its law is `rbMeasure ι s K` (`nsMeasure_map_rbProj`).
* `lnProj a n`: the noises of a basis-design window (`n` rounds for each basis vector) starting
  at round `a`; its law is `lnNoise ι n` (`nsMeasure_map_lnProj`).
* Both are independent of the first `T ≤ a` coordinates (`indepFun_prefix_rbProj`,
  `indepFun_prefix_lnProj`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Maiti2026Power

variable {ι : Type*}

/-- Splitting a family of pairs into the pair of families. -/
def splitPairs {J : Type*} (v : J → (ι → Bool) × ℝ) : (J → ι → Bool) × (J → ℝ) :=
  (fun p ↦ (v p).1, fun p ↦ (v p).2)

lemma measurable_splitPairs {J : Type*} : Measurable (splitPairs (ι := ι) (J := J)) :=
  (measurable_pi_lambda _ fun p ↦ (measurable_pi_apply p).fst).prodMk
    (measurable_pi_lambda _ fun p ↦ (measurable_pi_apply p).snd)

section RBWindow

variable {a s K : ℕ}

/-- The round of offset `ℓ` in block `k` of a window starting at round `a` with blocks of
length `s`. -/
def winIdx (a s : ℕ) {K : ℕ} (p : (_ : Fin K) × Fin s) : ℕ := a + p.1 * s + p.2

lemma winIdx_injective : Function.Injective (winIdx a s (K := K)) := by
  rintro ⟨k, ℓ⟩ ⟨k', ℓ'⟩ h
  simp only [winIdx] at h
  have h1 : (k : ℕ) * s + ℓ = k' * s + ℓ' := by omega
  have hℓ := ℓ.2
  have hℓ' := ℓ'.2
  have hk : (k : ℕ) = k' := by
    rcases lt_trichotomy (k : ℕ) k' with hlt | heq | hgt
    · have := Nat.mul_le_mul_right s (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this
      linarith
    · exact heq
    · have := Nat.mul_le_mul_right s (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at this
      linarith
  have hℓe : (ℓ : ℕ) = ℓ' := by
    rw [hk] at h1
    omega
  exact Sigma.ext (Fin.ext hk) (heq_of_eq (Fin.ext hℓe))

lemma le_winIdx {T : ℕ} (haT : T ≤ a) (p : (_ : Fin K) × Fin s) : T ≤ winIdx a s p :=
  le_add_right (le_add_right haT)

/-- The seeds at the block starts and the noises of a window of `K` blocks of length `s` starting
at round `a`. -/
def rbProj (a s K : ℕ) (ω : ℕ → (ι → Bool) × ℝ) :
    (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) :=
  (fun k ↦ (ω (a + k * s)).1, fun k ℓ ↦ (ω (a + k * s + ℓ)).2)

lemma measurable_rbProj : Measurable (rbProj (ι := ι) a s K) :=
  (measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).fst).prodMk
    (measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).snd)

/-- The block-start seeds of a window. -/
def blockSeeds (hs : 0 < s) (v : (_ : Fin K) × Fin s → ι → Bool) : Fin K → ι → Bool :=
  fun k ↦ v ⟨k, ⟨0, hs⟩⟩

lemma measurable_blockSeeds (hs : 0 < s) : Measurable (blockSeeds (ι := ι) (K := K) hs) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma measurable_sigmaCurry {J : Type*} {κ : J → Type*} :
    Measurable (Sigma.curry (α := J) (β := κ) (γ := fun _ _ ↦ ℝ)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma rbProj_eq (hs : 0 < s) :
    rbProj (ι := ι) a s K
      = Prod.map (blockSeeds hs) (Sigma.curry (γ := fun _ _ ↦ ℝ)) ∘ splitPairs
        ∘ (fun ω (p : (_ : Fin K) × Fin s) ↦ ω (winIdx a s p)) := by
  funext ω
  refine Prod.ext ?_ ?_
  · funext k
    simp [rbProj, blockSeeds, splitPairs, winIdx]
  · funext k ℓ
    simp [rbProj, splitPairs, winIdx, Sigma.curry]

variable [Fintype ι]

/-- The law of the seed-noise sequence of the norm-estimation algorithm: i.i.d. pairs of a uniform
Boolean vector and a standard Gaussian. -/
noncomputable def nsMeasure (ι : Type*) [Fintype ι] : Measure (ℕ → (ι → Bool) × ℝ) :=
  Measure.infinitePi fun _ ↦ (uniformBoolVec ι).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure (nsMeasure ι) := by
  unfold nsMeasure
  infer_instance

/-- **Law of an RB window**: the seeds at the block starts and the noises of a window of the
seed-noise sequence have law `rbMeasure`. -/
theorem nsMeasure_map_rbProj (hs : 0 < s) :
    (nsMeasure ι).map (rbProj a s K) = rbMeasure ι s K := by
  have hproj : Measurable fun ω : ℕ → (ι → Bool) × ℝ ↦ fun p : (_ : Fin K) × Fin s ↦
      ω (winIdx a s p) := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  have hcurry : Measurable (Sigma.curry (α := Fin K) (β := fun _ ↦ Fin s) (γ := fun _ _ ↦ ℝ)) :=
    measurable_sigmaCurry
  have hg : Measurable (Prod.map (blockSeeds (ι := ι) (K := K) hs)
      (Sigma.curry (γ := fun _ _ ↦ ℝ))) :=
    (measurable_blockSeeds hs).prodMap hcurry
  rw [rbProj_eq hs, ← Measure.map_map hg (measurable_splitPairs.comp hproj),
    ← Measure.map_map measurable_splitPairs hproj, nsMeasure,
    Measure.infinitePi_map_eval_comp _ winIdx_injective]
  rw [show (splitPairs : ((_ : Fin K) × Fin s → (ι → Bool) × ℝ) → _)
      = fun v ↦ (fun p ↦ (v p).1, fun p ↦ (v p).2) from rfl,
    Measure.pi_prod_map_split, ← Measure.map_prod_map _ _ (measurable_blockSeeds hs) hcurry,
    rbMeasure]
  congr 1
  · rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_eval_comp _ fun k k' h ↦ by
      simpa using congrArg Sigma.fst h
  · exact Measure.pi_sigma_map_curry _

/-- The RB window starting at round `a ≥ T` is independent of the first `T` coordinates. -/
theorem indepFun_prefix_rbProj (hs : 0 < s) {T : ℕ} (haT : T ≤ a) :
    IndepFun (fun ω (t : Fin T) ↦ ω t) (rbProj a s K) (nsMeasure ι) := by
  have h := indepFun_prefix_window ((uniformBoolVec ι).prod (gaussianReal 0 1))
    (f := winIdx a s (K := K)) (le_winIdx haT)
  rw [rbProj_eq hs]
  exact h.comp measurable_id
    (((measurable_blockSeeds hs).prodMap measurable_sigmaCurry).comp measurable_splitPairs)

end RBWindow

section LNWindow

variable [Fintype ι] {a n : ℕ}

/-- The round of the `ℓ`-th repetition of the basis vector `e_i` in a basis-design window
starting at round `a`. -/
noncomputable def lnIdx (a n : ℕ) (p : (_ : ι) × Fin n) : ℕ :=
  a + (Fintype.equivFin ι p.1) * n + p.2

lemma lnIdx_injective : Function.Injective (lnIdx (ι := ι) a n) := by
  rintro ⟨i, ℓ⟩ ⟨i', ℓ'⟩ h
  simp only [lnIdx] at h
  have h1 : (Fintype.equivFin ι i : ℕ) * n + ℓ = (Fintype.equivFin ι i') * n + ℓ' := by omega
  have hℓ := ℓ.2
  have hℓ' := ℓ'.2
  have hk : (Fintype.equivFin ι i : ℕ) = Fintype.equivFin ι i' := by
    rcases lt_trichotomy (Fintype.equivFin ι i : ℕ) (Fintype.equivFin ι i') with hlt | heq | hgt
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this
      linarith
    · exact heq
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at this
      linarith
  have hi : i = i' := (Fintype.equivFin ι).injective (Fin.ext hk)
  subst hi
  have hℓe : (ℓ : ℕ) = ℓ' := by omega
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hℓe))

lemma le_lnIdx {T : ℕ} (haT : T ≤ a) (p : (_ : ι) × Fin n) : T ≤ lnIdx a n p :=
  le_add_right (le_add_right haT)

/-- The noises of a basis-design window starting at round `a`: `n` rounds for each basis
vector `e_i`, in the order of `Fintype.equivFin ι`. -/
noncomputable def lnProj (a n : ℕ) (ω : ℕ → (ι → Bool) × ℝ) : ι → Fin n → ℝ :=
  fun i ℓ ↦ (ω (a + (Fintype.equivFin ι i) * n + ℓ)).2

lemma measurable_lnProj : Measurable (lnProj (ι := ι) a n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).snd

lemma lnProj_eq :
    lnProj (ι := ι) a n = Sigma.curry (γ := fun _ _ ↦ ℝ) ∘ Prod.snd ∘ splitPairs
      ∘ (fun ω (p : (_ : ι) × Fin n) ↦ ω (lnIdx a n p)) := by
  funext ω i ℓ
  simp [lnProj, splitPairs, lnIdx, Sigma.curry]

/-- **Law of a basis-design window**: the noises of a basis-design window of the seed-noise
sequence have law `lnNoise`. -/
theorem nsMeasure_map_lnProj :
    (nsMeasure ι).map (lnProj a n) = lnNoise ι n := by
  have hproj : Measurable fun ω : ℕ → (ι → Bool) × ℝ ↦ fun p : (_ : ι) × Fin n ↦
      ω (lnIdx a n p) := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  have hcurry : Measurable (Sigma.curry (α := ι) (β := fun _ ↦ Fin n) (γ := fun _ _ ↦ ℝ)) :=
    measurable_sigmaCurry
  rw [lnProj_eq, ← Measure.map_map hcurry (measurable_snd.comp (measurable_splitPairs.comp hproj)),
    ← Measure.map_map measurable_snd (measurable_splitPairs.comp hproj),
    ← Measure.map_map measurable_splitPairs hproj, nsMeasure,
    Measure.infinitePi_map_eval_comp _ lnIdx_injective]
  rw [show (splitPairs : ((_ : ι) × Fin n → (ι → Bool) × ℝ) → _)
      = fun v ↦ (fun p ↦ (v p).1, fun p ↦ (v p).2) from rfl,
    Measure.pi_prod_map_split]
  have hsnd : ((Measure.pi fun _ : (_ : ι) × Fin n ↦ uniformBoolVec ι).prod
      (Measure.pi fun _ : (_ : ι) × Fin n ↦ gaussianReal 0 1)).map Prod.snd
      = Measure.pi fun _ : (_ : ι) × Fin n ↦ gaussianReal 0 1 := Measure.snd_prod
  rw [hsnd, Measure.pi_sigma_map_curry, lnNoise]

/-- The basis-design window starting at round `a ≥ T` is independent of the first `T`
coordinates. -/
theorem indepFun_prefix_lnProj {T : ℕ} (haT : T ≤ a) :
    IndepFun (fun ω (t : Fin T) ↦ ω t) (lnProj a n) (nsMeasure ι) := by
  have h := indepFun_prefix_window ((uniformBoolVec ι).prod (gaussianReal 0 1))
    (f := lnIdx (ι := ι) a n) (le_lnIdx haT)
  rw [lnProj_eq]
  exact h.comp measurable_id
    (measurable_sigmaCurry.comp (measurable_snd.comp measurable_splitPairs))

end LNWindow

end Maiti2026Power
