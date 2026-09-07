/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.UnitBall

/-!
# The block-ball action set

The block-ball set `blockBallSet k d ⊆ ℝ^(Fin k × Fin d)` is the union over the `k` blocks `i` of
the unit balls of the coordinate subspaces of the blocks (blueprint `def:block_ball_set`). This
file provides the block embeddings `blockEmb i : ℝ^d → ℝ^(k × d)` and projections
`blockProj i : ℝ^(k × d) → ℝ^d`, which are adjoint (`inner_blockEmb_left`), and the basic
properties of the block-ball set (blueprint `lem:block_ball_basic`): it is the union of the
images of the unit ball by the block embeddings, compact, contained in the unit ball, spanning,
its support function is `θ ↦ max_i ‖θ⁽ⁱ⁾‖` (`supportFn_blockBallSet`) and the simple regret of a
reward vector supported on block `i` is the simple regret on the unit ball of `ℝ^d` of the
projected recommendation (`simpleRegret_blockBallSet_blockEmb`).
-/

@[expose] public section

open Learning.LinearBandit Finset
open scoped RealInnerProductSpace

namespace Maiti2026Power

variable {k d : ℕ}

/-- The embedding of `ℝ^d` on the `i`-th block of coordinates of `ℝ^(k × d)`. -/
noncomputable def blockEmb (i : Fin k) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k × Fin d) where
  toFun u := WithLp.toLp 2 fun p ↦ if p.1 = i then u p.2 else 0
  map_add' u v := by
    ext p
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext p
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

/-- The projection of `ℝ^(k × d)` on the `i`-th block of coordinates. -/
noncomputable def blockProj (i : Fin k) :
    EuclideanSpace ℝ (Fin k × Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 fun l ↦ x (i, l)
  map_add' x y := by ext l; simp
  map_smul' c x := by ext l; simp

@[simp]
lemma blockEmb_apply (i : Fin k) (u : EuclideanSpace ℝ (Fin d)) (p : Fin k × Fin d) :
    blockEmb i u p = if p.1 = i then u p.2 else 0 := rfl

@[simp]
lemma blockProj_apply (i : Fin k) (x : EuclideanSpace ℝ (Fin k × Fin d)) (l : Fin d) :
    blockProj i x l = x (i, l) := rfl

/-- The block embedding and the block projection are adjoint. -/
lemma inner_blockEmb_left (i : Fin k) (u : EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    ⟪blockEmb i u, x⟫ = ⟪u, blockProj i x⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_ite_eq']

lemma inner_blockEmb_right (i : Fin k) (x : EuclideanSpace ℝ (Fin k × Fin d))
    (u : EuclideanSpace ℝ (Fin d)) :
    ⟪x, blockEmb i u⟫ = ⟪blockProj i x, u⟫ := by
  rw [real_inner_comm, inner_blockEmb_left, real_inner_comm]

lemma norm_blockEmb (i : Fin k) (u : EuclideanSpace ℝ (Fin d)) : ‖blockEmb i u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [Fintype.sum_prod_type, ite_pow, Finset.sum_ite_eq']

lemma sum_norm_sq_blockProj (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    ∑ i, ‖blockProj i x‖ ^ 2 = ‖x‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

lemma norm_blockProj_le (i : Fin k) (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    ‖blockProj i x‖ ≤ ‖x‖ := by
  have h : ‖blockProj i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sum_norm_sq_blockProj x]
    exact Finset.single_le_sum (f := fun j ↦ ‖blockProj j x‖ ^ 2) (fun j _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  calc ‖blockProj i x‖ = √(‖blockProj i x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

@[simp]
lemma blockProj_blockEmb_same (i : Fin k) (u : EuclideanSpace ℝ (Fin d)) :
    blockProj i (blockEmb i u) = u := by
  ext l
  simp

lemma blockProj_blockEmb_of_ne {i j : Fin k} (h : j ≠ i) (u : EuclideanSpace ℝ (Fin d)) :
    blockProj j (blockEmb i u) = 0 := by
  ext l
  simp [h]

lemma continuous_blockProj (i : Fin k) : Continuous (blockProj (d := d) i) :=
  (blockProj i).continuous_of_finiteDimensional

lemma continuous_blockEmb (i : Fin k) : Continuous (blockEmb (d := d) i) :=
  (blockEmb i).continuous_of_finiteDimensional

lemma measurable_blockProj (i : Fin k) : Measurable (blockProj (d := d) i) :=
  (continuous_blockProj i).measurable

section blockBallSet

variable {x : EuclideanSpace ℝ (Fin k × Fin d)}

lemma norm_le_one_of_mem_blockBallSet (hx : x ∈ blockBallSet k d) : ‖x‖ ≤ 1 := hx.1

lemma blockBallSet_subset_unitBall : blockBallSet k d ⊆ unitBall (Fin k × Fin d) :=
  fun _ hx ↦ mem_unitBall_iff.2 hx.1

lemma blockEmb_mem_blockBallSet {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ≤ 1) (i : Fin k) :
    blockEmb i u ∈ blockBallSet k d :=
  ⟨by rw [norm_blockEmb]; exact hu, i, fun j hj l ↦ by simp [hj]⟩

/-- A point of the block-ball set vanishes on all blocks but one. -/
lemma exists_blockProj_eq_zero (hx : x ∈ blockBallSet k d) :
    ∃ i, ∀ j ≠ i, blockProj j x = 0 := by
  obtain ⟨-, i, hi⟩ := hx
  exact ⟨i, fun j hj ↦ by ext l; simp [hi j hj l]⟩

lemma eq_blockEmb_blockProj {i : Fin k} (hi : ∀ j ≠ i, blockProj j x = 0) :
    x = blockEmb i (blockProj i x) := by
  ext ⟨j, l⟩
  simp only [blockEmb_apply, blockProj_apply]
  split_ifs with h
  · subst h
    rfl
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin d) ↦ v l) (hi j h)
    simpa using this

/-- The block-ball set is the union of the images of the unit ball by the block embeddings. -/
lemma blockBallSet_eq_iUnion :
    blockBallSet k d = ⋃ i, blockEmb i '' unitBall (Fin d) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := exists_blockProj_eq_zero hx
    exact Set.mem_iUnion.2 ⟨i, blockProj i x,
      mem_unitBall_iff.2 ((norm_blockProj_le i x).trans hx.1), (eq_blockEmb_blockProj hi).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, u, hu, rfl⟩
    exact blockEmb_mem_blockBallSet (mem_unitBall_iff.1 hu) i

lemma isCompact_blockBallSet : IsCompact (blockBallSet k d) := by
  rw [blockBallSet_eq_iUnion]
  exact isCompact_iUnion fun i ↦ isCompact_unitBall.image (continuous_blockEmb i)

/-- The block-ball set is spanning: it contains the standard basis. -/
lemma span_blockBallSet : Submodule.span ℝ (blockBallSet k d) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (EuclideanSpace.basisFun _ ℝ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨i, l⟩, rfl⟩
  refine ⟨by simp [EuclideanSpace.basisFun_apply], i, fun j hj l' ↦ ?_⟩
  simp [EuclideanSpace.basisFun_apply, hj]

lemma blockBallSet_nonempty (i : Fin k) : (blockBallSet k d).Nonempty :=
  ⟨blockEmb i 0, blockEmb_mem_blockBallSet (by simp) i⟩

/-- The norm of every block of `θ` is at most the support function of the block-ball set at
`θ`. -/
lemma norm_blockProj_le_supportFn (i : Fin k) (θ : EuclideanSpace ℝ (Fin k × Fin d)) :
    ‖blockProj i θ‖ ≤ supportFn (blockBallSet k d) θ := by
  have hR : ∀ y ∈ blockBallSet k d, ‖y‖ ≤ 1 := fun y hy ↦ hy.1
  set v := blockProj i θ with hv
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero]
    simpa using inner_le_supportFn hR (blockEmb_mem_blockBallSet (u := 0) (by simp) i) θ
  · have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    have hmem := blockEmb_mem_blockBallSet (u := ‖v‖⁻¹ • v)
      (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv']) i
    have := inner_le_supportFn hR hmem θ
    rwa [inner_blockEmb_left, ← hv, real_inner_smul_left, real_inner_self_eq_norm_sq, sq,
      inv_mul_cancel_left₀ hv'] at this

/-- The support function of the block-ball set: `max_i ‖θ⁽ⁱ⁾‖`. -/
lemma supportFn_blockBallSet (θ : EuclideanSpace ℝ (Fin k × Fin d)) :
    supportFn (blockBallSet k d) θ = ⨆ i, ‖blockProj i θ‖ := by
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · have : blockBallSet k d = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ by
      obtain ⟨-, i, -⟩ := hx
      exact hk.elim i
    rw [this, supportFn, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
  obtain ⟨i₀⟩ := id hk
  refine le_antisymm (supportFn_le (blockBallSet_nonempty i₀) fun y hy ↦ ?_)
    (ciSup_le fun i ↦ norm_blockProj_le_supportFn i θ)
  obtain ⟨i, hi⟩ := exists_blockProj_eq_zero hy
  rw [eq_blockEmb_blockProj hi, inner_blockEmb_left]
  calc ⟪blockProj i y, blockProj i θ⟫ ≤ ‖blockProj i y‖ * ‖blockProj i θ‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖blockProj i θ‖ := by gcongr; exact (norm_blockProj_le i y).trans hy.1
    _ = ‖blockProj i θ‖ := one_mul _
    _ ≤ ⨆ i, ‖blockProj i θ‖ :=
        le_ciSup (f := fun i ↦ ‖blockProj i θ‖) (Set.finite_range _).bddAbove i

/-- The support function of the block-ball set at a reward vector supported on block `i`. -/
lemma supportFn_blockBallSet_blockEmb (i : Fin k) (ϑ : EuclideanSpace ℝ (Fin d)) :
    supportFn (blockBallSet k d) (blockEmb i ϑ) = ‖ϑ‖ := by
  refine le_antisymm (supportFn_le (blockBallSet_nonempty i) fun y hy ↦ ?_) ?_
  · rw [inner_blockEmb_right]
    calc ⟪blockProj i y, ϑ⟫ ≤ ‖blockProj i y‖ * ‖ϑ‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖ϑ‖ := by gcongr; exact (norm_blockProj_le i y).trans hy.1
      _ = ‖ϑ‖ := one_mul _
  · simpa using norm_blockProj_le_supportFn i (blockEmb i ϑ)

/-- **The simple regret of a reward vector supported on block `i`** is the simple regret on the
unit ball of `ℝ^d` of the projection of the recommendation on block `i`. -/
lemma simpleRegret_blockBallSet_blockEmb (i : Fin k) (ϑ : EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin k × Fin d)) :
    simpleRegret (blockBallSet k d) (blockEmb i ϑ) y =
      simpleRegret (unitBall (Fin d)) ϑ (blockProj i y) := by
  rw [simpleRegret_eq_supportFn_sub, simpleRegret_eq_supportFn_sub, supportFn_blockBallSet_blockEmb,
    supportFn_unitBall, inner_blockEmb_right]

end blockBallSet

section blockDesign

variable {T : ℕ}

/-- The projection of the block-ball set on block `i`, as a map to the unit ball of `ℝ^d`. -/
noncomputable def blockProjBall (i : Fin k) (y : blockBallSet k d) : unitBall (Fin d) :=
  ⟨blockProj i y,
    mem_unitBall_iff.2 ((norm_blockProj_le i _).trans (norm_le_one_of_mem_blockBallSet y.2))⟩

@[simp]
lemma coe_blockProjBall (i : Fin k) (y : blockBallSet k d) :
    (blockProjBall i y : EuclideanSpace ℝ (Fin d)) = blockProj i y := rfl

lemma measurable_blockProjBall (i : Fin k) : Measurable (blockProjBall (d := d) i) :=
  ((measurable_blockProj i).comp measurable_subtype_coe).subtype_mk

/-- The design `x` on the block-ball set projected on block `i`: a design on the unit ball of
`ℝ^d`. -/
noncomputable def blockDesign (i : Fin k) (x : ℕ → blockBallSet k d) : ℕ → unitBall (Fin d) :=
  fun t ↦ blockProjBall i (x t)

@[simp]
lemma coe_blockDesign (i : Fin k) (x : ℕ → blockBallSet k d) (t : ℕ) :
    (blockDesign i x t : EuclideanSpace ℝ (Fin d)) = blockProj i (x t) := rfl

/-- The rounds `t < T` in which the design `x` plays in block `i`. -/
noncomputable def blockRounds (i : Fin k) (x : ℕ → blockBallSet k d) (T : ℕ) : Finset (Fin T) :=
  Finset.univ.filter fun t ↦ blockProj i (x t : EuclideanSpace ℝ (Fin k × Fin d)) ≠ 0

/-- The trace of the design matrix of the projected design is at most the number of rounds
played in the block. -/
lemma trace_sum_outerSelf_blockDesign_le (i : Fin k) (x : ℕ → blockBallSet k d) :
    (∑ t : Fin T, outerSelf (blockDesign i x t : EuclideanSpace ℝ (Fin d))).trace ≤
      (blockRounds i x T).card := by
  rw [Matrix.trace_sum]
  simp_rw [trace_outerSelf]
  calc ∑ t : Fin T, ‖(blockDesign i x t : EuclideanSpace ℝ (Fin d))‖ ^ 2
      = ∑ t ∈ blockRounds i x T, ‖(blockDesign i x t : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun t _ ht ↦ ?_).symm
        simp only [blockRounds, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ht
        simp [ht]
    _ ≤ ∑ t ∈ blockRounds i x T, 1 :=
        Finset.sum_le_sum fun t _ ↦ pow_le_one₀ (norm_nonneg _)
          ((norm_blockProj_le i _).trans (norm_le_one_of_mem_blockBallSet (x t).2))
    _ = (blockRounds i x T).card := by simp

/-- The rounds played in the different blocks are disjoint. -/
lemma pairwiseDisjoint_blockRounds (x : ℕ → blockBallSet k d) (T : ℕ) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      fun i ↦ blockRounds i x T := by
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro t hti htj
  simp only [blockRounds, Finset.mem_filter, Finset.mem_univ, true_and] at hti htj
  obtain ⟨i₀, hi₀⟩ := exists_blockProj_eq_zero (x t).2
  by_cases hi : i = i₀
  · by_cases hj : j = i₀
    · exact hij (hi.trans hj.symm)
    · exact htj (hi₀ j hj)
  · exact hti (hi₀ i hi)

lemma sum_card_blockRounds_le (x : ℕ → blockBallSet k d) (T : ℕ) :
    ∑ i, (blockRounds i x T).card ≤ T := by
  classical
  rw [← Finset.card_biUnion (pairwiseDisjoint_blockRounds x T)]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin T)

/-- **Pigeonhole**: some block receives at most `T / k` rounds. -/
lemma exists_mul_card_blockRounds_le (hk : 0 < k) (x : ℕ → blockBallSet k d) (T : ℕ) :
    ∃ i, k * (blockRounds i x T).card ≤ T := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_contra h
  push Not at h
  have h1 : ∑ _i : Fin k, T < ∑ i, k * (blockRounds i x T).card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ h i
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have := Nat.mul_le_mul_left k (sum_card_blockRounds_le x T)
  omega

end blockDesign

end Maiti2026Power
