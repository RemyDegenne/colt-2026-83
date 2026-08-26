/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.IntrinsicWidth
public import COLT83.MXJ2026.StructuredSets
public import COLT83.Mathlib.Probability.SubgaussianMax

/-!
# The multi-task action set: structure, span and intrinsic width

For block sizes `d : Fin m → ℕ`, the multi-task action set `multitaskSet d ⊆ ℝ^(Σ j, Fin (d j))`
consists of the vectors of `{0, 1}^(Σ j, Fin (d j))` with exactly one `1` in each block.

* `oneHot d κ`: the element of the multi-task set with ones at the positions `κ j`;
  `multitaskSet d = range (oneHot d)` (`multitaskSet_eq_range`) and `|multitaskSet d| = ∏ d j`
  (`ncard_multitaskSet`);
* `supportFn_multitaskSet`: `sup_{x ∈ 𝒳} ⟪x, y⟫ = ∑ j, max_l y ⟨j, l⟩`;
* `mem_span_multitaskSet_iff`: the span of the multi-task set is the subspace of vectors whose
  block sums are all equal; `finrank_span_multitaskSet`: its dimension is `∑ j, d j - m + 1`;
* `unifDesignMatrix d`: the design matrix of the uniform design on the multi-task set, and its
  action on the vector `μ = (1 / d j)` and on block-centered vectors;
* `intrinsicGw_multitaskSet_le`: the intrinsic width of the multi-task set is at most
  `∑ j, √(2 d_j log d_j)` (Proposition `prop:width_multitask`).

Blueprint: `def:multitask_set`, `lem:multitask_basis`, `lem:multitask_design_cov`,
`lem:multitask_width_reduction`, `lem:centered_gaussian_max`, `prop:width_multitask`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix Finset
open scoped RealInnerProductSpace

namespace COLT83

variable {m : ℕ} {d : Fin m → ℕ}

section oneHot

/-- The element of the multi-task set with ones at the positions `κ j`, `j < m`. -/
noncomputable def oneHot (d : Fin m → ℕ) (κ : ∀ j, Fin (d j)) :
    EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ if i.2 = κ i.1 then 1 else 0

lemma oneHot_apply (κ : ∀ j, Fin (d j)) (i : Σ j, Fin (d j)) :
    oneHot d κ i = if i.2 = κ i.1 then 1 else 0 := rfl

lemma oneHot_apply_mk (κ : ∀ j, Fin (d j)) (j : Fin m) (l : Fin (d j)) :
    oneHot d κ ⟨j, l⟩ = if l = κ j then 1 else 0 := rfl

lemma inner_oneHot (κ : ∀ j, Fin (d j)) (y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪oneHot d κ, y⟫ = ∑ j, y ⟨j, κ j⟩ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [oneHot_apply_mk]

lemma oneHot_mem_multitaskSet (κ : ∀ j, Fin (d j)) : oneHot d κ ∈ multitaskSet d := by
  refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [oneHot_apply]
    split_ifs <;> simp
  · simp [oneHot_apply_mk]

lemma multitaskSet_eq_range : multitaskSet d = Set.range (oneHot d) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨h01, hsum⟩ := hx
    have hex : ∀ j, ∃ l, x ⟨j, l⟩ = 1 := fun j ↦ by
      by_contra h
      push Not at h
      have h0 : ∀ l, x ⟨j, l⟩ = 0 := fun l ↦ (h01 ⟨j, l⟩).resolve_right (h l)
      have := hsum j
      simp [h0] at this
    choose κ hκ using hex
    refine ⟨κ, ?_⟩
    ext i
    obtain ⟨j, l⟩ := i
    rw [oneHot_apply_mk]
    split_ifs with hl
    · rw [hl, hκ]
    · rcases h01 ⟨j, l⟩ with h0 | h1
      · exact h0.symm
      · exfalso
        have h2 : (2 : ℝ) ≤ ∑ l', x ⟨j, l'⟩ := by
          calc (2 : ℝ) = x ⟨j, l⟩ + x ⟨j, κ j⟩ := by rw [h1, hκ]; norm_num
            _ = ∑ l' ∈ {l, κ j}, x ⟨j, l'⟩ := by rw [Finset.sum_pair hl]
            _ ≤ ∑ l', x ⟨j, l'⟩ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l' _ _ ↦ by
                rcases h01 ⟨j, l'⟩ with h | h <;> simp [h]
        linarith [hsum j]
  · rintro ⟨κ, rfl⟩
    exact oneHot_mem_multitaskSet κ

lemma oneHot_injective : Function.Injective (oneHot d) := by
  intro κ κ' h
  funext j
  have := congrArg (fun x : EuclideanSpace ℝ (Σ j, Fin (d j)) ↦ x ⟨j, κ j⟩) h
  simp only [oneHot_apply_mk, ite_true] at this
  by_contra hne
  rw [if_neg hne] at this
  exact one_ne_zero this

lemma ncard_multitaskSet : (multitaskSet d).ncard = ∏ j, d j := by
  rw [multitaskSet_eq_range, Set.ncard_range_of_injective oneHot_injective, Nat.card_pi]
  simp

lemma multitaskSet_finite : (multitaskSet d).Finite := by
  rw [multitaskSet_eq_range]
  exact Set.finite_range _

lemma multitaskSet_nonempty (hd : ∀ j, 0 < d j) : (multitaskSet d).Nonempty :=
  ⟨oneHot d fun j ↦ ⟨0, hd j⟩, oneHot_mem_multitaskSet _⟩

lemma norm_le_of_mem_multitaskSet {x : EuclideanSpace ℝ (Σ j, Fin (d j))}
    (hx : x ∈ multitaskSet d) : ‖x‖ ≤ √m := by
  rw [multitaskSet_eq_range] at hx
  obtain ⟨κ, rfl⟩ := hx
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [oneHot_apply, Real.norm_eq_abs, Fintype.sum_sigma]
  calc ∑ j, ∑ l : Fin (d j), |if l = κ j then (1 : ℝ) else 0| ^ 2
      = ∑ j : Fin m, (1 : ℝ) := Finset.sum_congr rfl fun j _ ↦ by simp
    _ ≤ m := by simp

/-- The support function of the multi-task set is the sum over the blocks of the block maxima. -/
lemma supportFn_multitaskSet (hd : ∀ j, 0 < d j) (y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    supportFn (multitaskSet d) y = ∑ j, ⨆ l, y ⟨j, l⟩ := by
  have : ∀ j, Nonempty (Fin (d j)) := fun j ↦ ⟨⟨0, hd j⟩⟩
  rw [multitaskSet_eq_range, supportFn_eq_sSup, ← Set.range_comp]
  change ⨆ κ, ⟪oneHot d κ, y⟫ = _
  simp_rw [inner_oneHot]
  apply le_antisymm
  · exact ciSup_le fun κ ↦ Finset.sum_le_sum fun j _ ↦
      le_ciSup (Finite.bddAbove_range fun l ↦ y ⟨j, l⟩) (κ j)
  · choose κ hκ using fun j ↦ Finite.exists_max fun l ↦ y ⟨j, l⟩
    exact (Finset.sum_le_sum fun j _ ↦ ciSup_le (hκ j)).trans
      (le_ciSup (Finite.bddAbove_range fun κ ↦ ∑ j, y ⟨j, κ j⟩) κ)

end oneHot

section span

/-- The sum of the coordinates of `y` in the block `j`. -/
def blockSum (y : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) : ℝ := ∑ l, y ⟨j, l⟩

lemma blockSum_add (y z : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) :
    blockSum (y + z) j = blockSum y j + blockSum z j := by
  simp [blockSum, Finset.sum_add_distrib]

lemma blockSum_smul (c : ℝ) (y : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) :
    blockSum (c • y) j = c * blockSum y j := by
  simp [blockSum, Finset.mul_sum]

lemma blockSum_sum {α : Type*} (s : Finset α) (y : α → EuclideanSpace ℝ (Σ j, Fin (d j)))
    (j : Fin m) :
    blockSum (∑ a ∈ s, y a) j = ∑ a ∈ s, blockSum (y a) j := by
  simp only [blockSum, WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_comm

lemma blockSum_sub (y z : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) :
    blockSum (y - z) j = blockSum y j - blockSum z j := by
  simp [blockSum, Finset.sum_sub_distrib]

lemma blockSum_oneHot (κ : ∀ j, Fin (d j)) (j : Fin m) : blockSum (oneHot d κ) j = 1 := by
  simp [blockSum, oneHot_apply_mk]

/-- The block sums of `single ⟨j', l⟩ a`. -/
lemma blockSum_single (j' : Fin m) (l : Fin (d j')) (a : ℝ) (j : Fin m) :
    blockSum (EuclideanSpace.single ⟨j', l⟩ a) j = if j = j' then a else 0 := by
  simp only [blockSum, PiLp.single_apply]
  by_cases hj : j = j'
  · subst hj
    simp
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun l' _ ↦ ?_
    rw [if_neg]
    exact fun h ↦ hj (Sigma.mk.inj_iff.1 h).1

/-- The block-sum linear functional. -/
noncomputable def blockSumLin (d : Fin m → ℕ) (j : Fin m) :
    EuclideanSpace ℝ (Σ j, Fin (d j)) →ₗ[ℝ] ℝ :=
  ∑ l, (EuclideanSpace.proj (𝕜 := ℝ) (⟨j, l⟩ : Σ j, Fin (d j)) : _ →ₗ[ℝ] ℝ)

lemma blockSumLin_apply (j : Fin m) (y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockSumLin d j y = blockSum y j := by
  simp [blockSumLin, blockSum]

/-- `oneHot κ` as a sum of coordinate vectors. -/
lemma oneHot_apply_eq_sum (κ : ∀ j, Fin (d j)) (i : Σ j, Fin (d j)) :
    oneHot d κ i = ∑ j, if i = ⟨j, κ j⟩ then 1 else 0 := by
  obtain ⟨j', l'⟩ := i
  rw [oneHot_apply_mk, Finset.sum_eq_single j']
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h ↦ hj (Sigma.mk.inj_iff.1 h).1.symm
  · simp

/-- The difference of two coordinate vectors of the same block lies in the span of the
multi-task set. -/
lemma single_sub_single_mem_span (hd : ∀ j, 0 < d j) (i : Σ j, Fin (d j)) (l : Fin (d i.1)) :
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single ⟨i.1, l⟩ 1 ∈
      Submodule.span ℝ (multitaskSet d) := by
  classical
  let κ₀ : ∀ j, Fin (d j) := fun j ↦ ⟨0, hd j⟩
  let κ₁ : ∀ j, Fin (d j) := Function.update κ₀ i.1 i.2
  let κ₂ : ∀ j, Fin (d j) := Function.update κ₀ i.1 l
  have h : EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single ⟨i.1, l⟩ 1 =
      oneHot d κ₁ - oneHot d κ₂ := by
    ext k
    simp only [PiLp.sub_apply, PiLp.single_apply, oneHot_apply_eq_sum,
      ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i.1]
    · simp only [κ₁, κ₂, Function.update_self]
    · intro j _ hj
      simp [κ₁, κ₂, Function.update_of_ne hj]
    · simp
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span (oneHot_mem_multitaskSet κ₁))
    (Submodule.subset_span (oneHot_mem_multitaskSet κ₂))

/-- **The span of the multi-task set** is the subspace of vectors whose block sums are all
equal. -/
lemma mem_span_multitaskSet_iff (hd : ∀ j, 0 < d j) {y : EuclideanSpace ℝ (Σ j, Fin (d j))} :
    y ∈ Submodule.span ℝ (multitaskSet d) ↔ ∀ j j', blockSum y j = blockSum y j' := by
  constructor
  · intro hy
    let W : Submodule ℝ (EuclideanSpace ℝ (Σ j, Fin (d j))) :=
      ⨅ j, ⨅ j', LinearMap.ker (blockSumLin d j - blockSumLin d j')
    have hW : Submodule.span ℝ (multitaskSet d) ≤ W := by
      rw [Submodule.span_le]
      intro x hx
      rw [multitaskSet_eq_range] at hx
      obtain ⟨κ, rfl⟩ := hx
      simp only [W, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        blockSumLin_apply, blockSum_oneHot, sub_self, implies_true]
    have := hW hy
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      blockSumLin_apply, sub_eq_zero] at this
    exact this
  · intro hy
    classical
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hy0 : y = 0 := by
        ext i
        exact Fin.elim0 i.1
      rw [hy0]
      exact Submodule.zero_mem _
    let κ₀ : ∀ j, Fin (d j) := fun j ↦ ⟨0, hd j⟩
    let j₀ : Fin m := ⟨0, hm⟩
    set c := blockSum y j₀ with hc
    have hyc : ∀ j, blockSum y j = c := fun j ↦ hy j j₀
    -- `y = c • oneHot κ₀ + ∑ i, y i • (single i 1 - single ⟨i.1, κ₀ i.1⟩ 1)`
    have hdecomp : y = c • oneHot d κ₀ + ∑ i, y i •
        (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single ⟨i.1, κ₀ i.1⟩ 1) := by
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.sub_apply, PiLp.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      have h1 : ∑ i, y i * (if k = i then (1 : ℝ) else 0) = y k := by simp
      have h2 : ∑ i : Σ j, Fin (d j), y i * (if k = ⟨i.1, κ₀ i.1⟩ then (1 : ℝ) else 0) =
          c * oneHot d κ₀ k := by
        rw [oneHot_apply_eq_sum, Finset.mul_sum, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        dsimp only
        rw [← hyc j, blockSum, Finset.sum_mul]
      rw [h1, h2]
      ring
    rw [hdecomp]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span (oneHot_mem_multitaskSet κ₀))) (Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (single_sub_single_mem_span hd i _))

/-- **Dimension of the span of the multi-task set**: `finrank (span 𝒳) = ∑ j, d j - (m - 1)`
(stated additively). -/
lemma finrank_span_multitaskSet_add (hd : ∀ j, 0 < d j) (hm : 0 < m) :
    Module.finrank ℝ (Submodule.span ℝ (multitaskSet d)) + (m - 1) =
      Fintype.card (Σ j, Fin (d j)) := by
  classical
  set j₀ : Fin m := ⟨0, hm⟩
  let L : EuclideanSpace ℝ (Σ j, Fin (d j)) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi fun j ↦ blockSumLin d j - blockSumLin d j₀
  have hker : LinearMap.ker L = Submodule.span ℝ (multitaskSet d) := by
    ext y
    rw [LinearMap.mem_ker, mem_span_multitaskSet_iff hd]
    simp only [L, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, blockSumLin_apply,
      Pi.zero_apply, sub_eq_zero]
    exact ⟨fun h j j' ↦ (h j).trans (h j').symm, fun h j ↦ h j j₀⟩
  have hrange : LinearMap.range L =
      LinearMap.ker (LinearMap.proj j₀ : (Fin m → ℝ) →ₗ[ℝ] ℝ) := by
    ext c
    rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.proj_apply]
    constructor
    · rintro ⟨y, rfl⟩
      simp [L]
    · intro hc
      refine ⟨∑ j, c j • EuclideanSpace.single (⟨j, ⟨0, hd j⟩⟩ : Σ j, Fin (d j)) (1 : ℝ), ?_⟩
      ext j
      simp only [L, LinearMap.pi_apply, LinearMap.sub_apply, blockSumLin_apply, blockSum_sum,
        blockSum_smul, blockSum_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [hc, sub_zero]
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj j₀ : (Fin m → ℝ) →ₗ[ℝ] ℝ)
  have hproj : LinearMap.range (LinearMap.proj j₀ : (Fin m → ℝ) →ₗ[ℝ] ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun x ↦ ⟨fun _ ↦ x, rfl⟩
  rw [hproj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h2
  rw [hker, hrange, finrank_euclideanSpace] at h1
  omega

end span

section counting

/-- Splitting a sum over `∀ j, Fin (d j)` according to the `l`-th coordinate. -/
lemma sum_pi_split (l : Fin m) (F : (∀ j, Fin (d j)) → ℝ) :
    ∑ κ, F κ = ∑ a : Fin (d l), ∑ r : ∀ j : {j // j ≠ l}, Fin (d j),
      F ((Equiv.piSplitAt l fun j ↦ Fin (d j)).symm (a, r)) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt l fun j ↦ Fin (d j)).symm, Fintype.sum_prod_type]

lemma piSplitAt_symm_apply_self (l : Fin m) (a : Fin (d l))
    (r : ∀ j : {j // j ≠ l}, Fin (d j)) :
    (Equiv.piSplitAt l fun j ↦ Fin (d j)).symm (a, r) l = a := by
  simp

lemma piSplitAt_symm_apply_of_ne (l : Fin m) (a : Fin (d l))
    (r : ∀ j : {j // j ≠ l}, Fin (d j)) {j : Fin m} (hj : j ≠ l) :
    (Equiv.piSplitAt l fun j ↦ Fin (d j)).symm (a, r) j = r ⟨j, hj⟩ := by
  simp [hj]

lemma card_pi_eq_mul (l : Fin m) :
    Fintype.card (∀ j, Fin (d j)) = d l * Fintype.card (∀ j : {j // j ≠ l}, Fin (d j)) := by
  rw [Fintype.card_congr (Equiv.piSplitAt l fun j ↦ Fin (d j)), Fintype.card_prod,
    Fintype.card_fin]

/-- `∑ κ, [κ l = k] = |∀ j ≠ l, Fin (d j)|`. -/
lemma sum_ite_apply_eq (l : Fin m) (k : Fin (d l)) :
    (∑ κ : ∀ j, Fin (d j), if k = κ l then (1 : ℝ) else 0) =
      Fintype.card (∀ j : {j // j ≠ l}, Fin (d j)) := by
  rw [sum_pi_split l]
  simp only [piSplitAt_symm_apply_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp

end counting

section design

/-- The design matrix of the uniform design on the multi-task set. -/
noncomputable def unifDesignMatrix (d : Fin m → ℕ) :
    Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) ℝ :=
  (Fintype.card (∀ j, Fin (d j)) : ℝ)⁻¹ • ∑ κ, outerSelf (oneHot d κ)

lemma unifDesignMatrix_mem_designSet (hd : ∀ j, 0 < d j) :
    unifDesignMatrix d ∈ designSet (multitaskSet d) := by
  have : Nonempty (∀ j, Fin (d j)) := ⟨fun j ↦ ⟨0, hd j⟩⟩
  rw [unifDesignMatrix, Finset.smul_sum]
  refine convex_designSet.sum_mem (fun _ _ ↦ by positivity) ?_
    fun κ _ ↦ outerSelf_mem_designSet (oneHot_mem_multitaskSet κ)
  have hN : (Fintype.card (∀ j, Fin (d j)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hN]

lemma toEuclideanLin_unifDesignMatrix (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    Matrix.toEuclideanLin (unifDesignMatrix d) v =
      (Fintype.card (∀ j, Fin (d j)) : ℝ)⁻¹ • ∑ κ, ⟪oneHot d κ, v⟫ • oneHot d κ := by
  apply WithLp.ofLp_injective
  change unifDesignMatrix d *ᵥ WithLp.ofLp v = _
  rw [unifDesignMatrix, Matrix.smul_mulVec, Matrix.sum_mulVec, WithLp.ofLp_smul, WithLp.ofLp_sum]
  congr 1
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [outerSelf, Matrix.vecMulVec_mulVec, IsCentralScalar.op_smul_eq_smul, WithLp.ofLp_smul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma toEuclideanLin_unifDesignMatrix_apply (v : EuclideanSpace ℝ (Σ j, Fin (d j)))
    (i : Σ j, Fin (d j)) :
    Matrix.toEuclideanLin (unifDesignMatrix d) v i =
      (Fintype.card (∀ j, Fin (d j)) : ℝ)⁻¹ * ∑ κ, ⟪oneHot d κ, v⟫ * oneHot d κ i := by
  rw [toEuclideanLin_unifDesignMatrix]
  simp [WithLp.ofLp_sum, Finset.sum_apply]

/-- The vector `μ` with coordinates `1 / d_j` on the block `j`. -/
noncomputable def muVec (d : Fin m → ℕ) : EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ (d i.1 : ℝ)⁻¹

lemma muVec_apply (i : Σ j, Fin (d j)) : muVec d i = (d i.1 : ℝ)⁻¹ := rfl

/-- `κ = ‖μ‖² = ∑ j, 1 / d_j`. -/
noncomputable def kappa (d : Fin m → ℕ) : ℝ := ∑ j, (d j : ℝ)⁻¹

lemma kappa_pos (hd : ∀ j, 0 < d j) (hm : 0 < m) : 0 < kappa d :=
  Finset.sum_pos (fun j _ ↦ by have := hd j; positivity) ⟨⟨0, hm⟩, Finset.mem_univ _⟩

lemma blockSum_muVec (hd : ∀ j, 0 < d j) (j : Fin m) : blockSum (muVec d) j = 1 := by
  have := hd j
  simp [blockSum, muVec_apply]
  field_simp

lemma inner_muVec (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪muVec d, v⟫ = ∑ j, (d j : ℝ)⁻¹ * blockSum v j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma, blockSum, muVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ mul_comm _ _

lemma inner_muVec_self (hd : ∀ j, 0 < d j) : ⟪muVec d, muVec d⟫ = kappa d := by
  rw [inner_muVec]
  simp [blockSum_muVec hd, kappa]

lemma inner_oneHot_muVec (κ : ∀ j, Fin (d j)) : ⟪oneHot d κ, muVec d⟫ = kappa d := by
  rw [inner_oneHot]
  rfl

/-- The block-centering of `v` on the block `l`: the coordinates of `v` in the block `l` minus
their mean, and `0` outside the block `l`. -/
noncomputable def blockCenter (l : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ if i.1 = l then v i - blockSum v l / d l else 0

lemma blockCenter_apply (l : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) (i : Σ j, Fin (d j)) :
    blockCenter l v i = if i.1 = l then v i - blockSum v l / d l else 0 := rfl

lemma blockCenter_apply_mk_self (l : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j)))
    (k : Fin (d l)) :
    blockCenter l v ⟨l, k⟩ = v ⟨l, k⟩ - blockSum v l / d l := by
  simp [blockCenter_apply]

lemma blockCenter_apply_mk_of_ne (l : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j)))
    {j : Fin m} (hj : j ≠ l) (k : Fin (d j)) :
    blockCenter l v ⟨j, k⟩ = 0 := by
  simp [blockCenter_apply, hj]

lemma blockCenter_add (l : Fin m) (v w : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockCenter l (v + w) = blockCenter l v + blockCenter l w := by
  ext i
  simp only [blockCenter_apply, PiLp.add_apply, blockSum_add]
  split_ifs <;> ring

lemma blockCenter_smul (l : Fin m) (c : ℝ) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockCenter l (c • v) = c • blockCenter l v := by
  ext i
  simp only [blockCenter_apply, PiLp.smul_apply, blockSum_smul, smul_eq_mul]
  split_ifs <;> ring

lemma blockCenter_sum {α : Type*} (l : Fin m) (s : Finset α)
    (v : α → EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockCenter l (∑ a ∈ s, v a) = ∑ a ∈ s, blockCenter l (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext i
    simp [blockCenter_apply, blockSum]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, blockCenter_add, ih]

lemma blockSum_blockCenter (hd : ∀ j, 0 < d j) (l : Fin m)
    (v : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) :
    blockSum (blockCenter l v) j = 0 := by
  by_cases hj : j = l
  · subst hj
    have := hd j
    simp only [blockSum, blockCenter_apply_mk_self, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · simp [blockSum, blockCenter_apply_mk_of_ne l v hj]

lemma inner_oneHot_blockCenter (κ : ∀ j, Fin (d j)) (l : Fin m)
    (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪oneHot d κ, blockCenter l v⟫ = blockCenter l v ⟨l, κ l⟩ := by
  rw [inner_oneHot, Finset.sum_eq_single l]
  · intro j _ hj
    exact blockCenter_apply_mk_of_ne l v hj _
  · simp

lemma inner_muVec_blockCenter (hd : ∀ j, 0 < d j) (l : Fin m)
    (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪muVec d, blockCenter l v⟫ = 0 := by
  simp [inner_muVec, blockSum_blockCenter hd]

lemma blockCenter_muVec (hd : ∀ j, 0 < d j) (l : Fin m) : blockCenter l (muVec d) = 0 := by
  ext i
  rw [blockCenter_apply, blockSum_muVec hd, muVec_apply]
  split_ifs with h
  · rw [h]
    simp
  · simp

lemma blockCenter_blockCenter (hd : ∀ j, 0 < d j) (l l' : Fin m)
    (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockCenter l (blockCenter l' v) = if l = l' then blockCenter l v else 0 := by
  ext i
  rw [blockCenter_apply, blockSum_blockCenter hd]
  by_cases hl : l = l'
  · subst hl
    rw [if_pos (rfl : l = l)]
    split_ifs with hi
    · simp
    · rw [blockCenter_apply, if_neg hi]
  · rw [if_neg hl]
    split_ifs with hi
    · have hi' : i.1 ≠ l' := by rw [hi]; exact hl
      rw [blockCenter_apply, if_neg hi']
      simp
    · simp

/-- `⟪blockCenter l x, y⟫ = ∑ k, x ⟨l, k⟩ y ⟨l, k⟩ - blockSum x l * blockSum y l / d l`. -/
lemma inner_blockCenter_left (l : Fin m) (x y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪blockCenter l x, y⟫ = ∑ k, x ⟨l, k⟩ * y ⟨l, k⟩ - blockSum x l * blockSum y l / d l := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · simp only [blockCenter_apply_mk_self, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      blockSum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    · ring
  · intro j _ hj
    simp [blockCenter_apply_mk_of_ne l x hj]
  · simp

lemma inner_blockCenter_symm (l : Fin m) (x y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪blockCenter l x, y⟫ = ⟪x, blockCenter l y⟫ := by
  rw [real_inner_comm (blockCenter l y) x, inner_blockCenter_left, inner_blockCenter_left]
  congr 1
  · exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  · ring

/-- Block-centering `v` on every block recovers `v` up to a multiple of `μ` when the block sums
of `v` are all equal to `c`. -/
lemma eq_smul_muVec_add_sum_blockCenter
    {v : EuclideanSpace ℝ (Σ j, Fin (d j))} {c : ℝ} (hv : ∀ j, blockSum v j = c) :
    v = c • muVec d + ∑ l, blockCenter l v := by
  ext i
  obtain ⟨j, k⟩ := i
  simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, muVec_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [blockCenter_apply_mk_self, hv j]
    ring
  · intro l _ hl
    exact blockCenter_apply_mk_of_ne l v (Ne.symm hl) k
  · simp

/-- The uniform design matrix acts on `μ` by multiplication by `κ`. -/
lemma toEuclideanLin_unifDesignMatrix_muVec (hd : ∀ j, 0 < d j) :
    Matrix.toEuclideanLin (unifDesignMatrix d) (muVec d) = kappa d • muVec d := by
  ext i
  obtain ⟨j, k⟩ := i
  rw [toEuclideanLin_unifDesignMatrix_apply]
  simp only [inner_oneHot_muVec, oneHot_apply_mk, PiLp.smul_apply, muVec_apply, smul_eq_mul,
    ← Finset.mul_sum, sum_ite_apply_eq, card_pi_eq_mul j]
  have := hd j
  have : ∀ j', Nonempty (Fin (d j')) := fun j' ↦ ⟨⟨0, hd j'⟩⟩
  have hr : (Fintype.card (∀ j' : {j' // j' ≠ j}, Fin (d j')) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

/-- The uniform design matrix acts on block-centered vectors of the block `l` by multiplication
by `1 / d_l`. -/
lemma toEuclideanLin_unifDesignMatrix_blockCenter (hd : ∀ j, 0 < d j) (l : Fin m)
    (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    Matrix.toEuclideanLin (unifDesignMatrix d) (blockCenter l v) =
      (d l : ℝ)⁻¹ • blockCenter l v := by
  ext i
  obtain ⟨j, k⟩ := i
  rw [toEuclideanLin_unifDesignMatrix_apply]
  simp only [inner_oneHot_blockCenter, oneHot_apply_mk, PiLp.smul_apply, smul_eq_mul]
  rw [sum_pi_split l]
  by_cases hj : j = l
  · subst hj
    simp only [piSplitAt_symm_apply_self, mul_ite, mul_one, mul_zero, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [card_pi_eq_mul j]
    have := hd j
    have : ∀ j', Nonempty (Fin (d j')) := fun j' ↦ ⟨⟨0, hd j'⟩⟩
    have hr : (Fintype.card (∀ j' : {j' // j' ≠ j}, Fin (d j')) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    push_cast
    field_simp
  · simp only [piSplitAt_symm_apply_of_ne l _ _ hj, blockCenter_apply_mk_of_ne l v hj, mul_zero]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have : ∑ a : Fin (d l), blockCenter l v ⟨l, a⟩ = 0 := blockSum_blockCenter hd l v l
    simp [this]

end design

section pseudoInverse

variable (d) in
/-- The normalizing constant `a = κ^{-3/2}`. -/
noncomputable def mtA : ℝ := (√(kappa d ^ 3))⁻¹

lemma mtA_sq_mul (hd : ∀ j, 0 < d j) (hm : 0 < m) : mtA d ^ 2 * kappa d ^ 3 = 1 := by
  have hκ := kappa_pos hd hm
  rw [mtA, inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]

variable (d) in
/-- The symmetric square root of the pseudo-inverse of the uniform design matrix:
`L v = a ⟪μ, v⟫ μ + ∑ l, √d_l blockCenter l v`. -/
noncomputable def mtL :
    EuclideanSpace ℝ (Σ j, Fin (d j)) →ₗ[ℝ] EuclideanSpace ℝ (Σ j, Fin (d j)) where
  toFun v := (mtA d * ⟪muVec d, v⟫) • muVec d + ∑ l, √(d l) • blockCenter l v
  map_add' v w := by
    simp only [inner_add_right, blockCenter_add, smul_add, Finset.sum_add_distrib, mul_add,
      add_smul]
    abel
  map_smul' c v := by
    simp only [inner_smul_right, blockCenter_smul, smul_smul, RingHom.id_apply, Finset.smul_sum,
      smul_add]
    congr 1
    · congr 1
      ring
    · exact Finset.sum_congr rfl fun l _ ↦ by rw [mul_comm]

lemma mtL_apply (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    mtL d v = (mtA d * ⟪muVec d, v⟫) • muVec d + ∑ l, √(d l) • blockCenter l v := rfl

lemma blockSum_mtL (hd : ∀ j, 0 < d j) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m) :
    blockSum (mtL d v) j = mtA d * ⟪muVec d, v⟫ := by
  simp [mtL_apply, blockSum_add, blockSum_smul, blockSum_sum, blockSum_muVec hd,
    blockSum_blockCenter hd]

lemma mtL_mem_span (hd : ∀ j, 0 < d j) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    mtL d v ∈ Submodule.span ℝ (multitaskSet d) :=
  (mem_span_multitaskSet_iff hd).2 fun j j' ↦ by rw [blockSum_mtL hd, blockSum_mtL hd]

lemma inner_muVec_mtL (hd : ∀ j, 0 < d j) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪muVec d, mtL d v⟫ = mtA d * ⟪muVec d, v⟫ * kappa d := by
  rw [mtL_apply, inner_add_right, inner_sum, real_inner_smul_right, inner_muVec_self hd]
  simp [real_inner_smul_right, inner_muVec_blockCenter hd]

lemma blockCenter_mtL (hd : ∀ j, 0 < d j) (l : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    blockCenter l (mtL d v) = √(d l) • blockCenter l v := by
  rw [mtL_apply, blockCenter_add, blockCenter_smul, blockCenter_muVec hd, smul_zero, zero_add,
    blockCenter_sum]
  simp_rw [blockCenter_smul, blockCenter_blockCenter hd]
  simp

lemma mtL_mtL (hd : ∀ j, 0 < d j) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    mtL d (mtL d v) = (mtA d ^ 2 * kappa d * ⟪muVec d, v⟫) • muVec d +
      ∑ l, (d l : ℝ) • blockCenter l v := by
  rw [mtL_apply (mtL d v), inner_muVec_mtL hd]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [blockCenter_mtL hd, smul_smul, Real.mul_self_sqrt (by positivity)]

lemma inner_mtL_left (x y : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪mtL d x, y⟫ = ⟪x, mtL d y⟫ := by
  simp only [mtL_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_blockCenter_symm]
  rw [real_inner_comm (muVec d) x, real_inner_comm y (muVec d)]
  ring_nf

/-- The uniform design matrix inverts `L ∘ L` on the span of the multi-task set. -/
lemma toEuclideanLin_unifDesignMatrix_mtL_mtL (hd : ∀ j, 0 < d j) (hm : 0 < m)
    {v : EuclideanSpace ℝ (Σ j, Fin (d j))} (hv : v ∈ Submodule.span ℝ (multitaskSet d)) :
    Matrix.toEuclideanLin (unifDesignMatrix d) (mtL d (mtL d v)) = v := by
  rw [mem_span_multitaskSet_iff hd] at hv
  set c := blockSum v ⟨0, hm⟩ with hc
  have hvc : ∀ j, blockSum v j = c := fun j ↦ hv j _
  have hμv : ⟪muVec d, v⟫ = c * kappa d := by
    rw [inner_muVec, kappa, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hvc j, mul_comm]
  rw [mtL_mtL hd, map_add, map_smul, map_sum, toEuclideanLin_unifDesignMatrix_muVec hd]
  simp_rw [map_smul, toEuclideanLin_unifDesignMatrix_blockCenter hd, smul_smul]
  conv_rhs => rw [eq_smul_muVec_add_sum_blockCenter hvc]
  congr 1
  · rw [hμv]
    congr 1
    have := mtA_sq_mul hd hm
    linear_combination c * this
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    have := hd l
    rw [mul_inv_cancel₀ (by positivity), one_smul]

variable (d) in
/-- The matrix of `mtL`. -/
noncomputable def mtLmat : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) ℝ :=
  Matrix.toEuclideanLin.symm (mtL d)

lemma toEuclideanLin_mtLmat : Matrix.toEuclideanLin (mtLmat d) = mtL d :=
  LinearEquiv.apply_symm_apply _ _

lemma toEuclideanLin_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  apply WithLp.ofLp_injective
  change (A * B) *ᵥ WithLp.ofLp v = A *ᵥ (B *ᵥ WithLp.ofLp v)
  rw [Matrix.mulVec_mulVec]

lemma transpose_mtLmat : (mtLmat d)ᵀ = mtLmat d := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (mtLmat d)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  apply Matrix.toEuclideanLin.injective
  rw [h, toEuclideanLin_mtLmat]
  symm
  rw [LinearMap.eq_adjoint_iff]
  exact fun x y ↦ inner_mtL_left x y

variable (d) in
/-- The pseudo-inverse `S = L L` of the uniform design matrix (a covariance matrix supported on
the span of the multi-task set). -/
noncomputable def mtS : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) ℝ := mtLmat d * mtLmat d

lemma toEuclideanLin_mtS (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    Matrix.toEuclideanLin (mtS d) v = mtL d (mtL d v) := by
  rw [mtS, toEuclideanLin_mul_apply, toEuclideanLin_mtLmat]

lemma mtS_posSemidef : (mtS d).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (mtLmat d)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_mtLmat] at h

lemma multivariateGaussian_mtS :
    multivariateGaussian 0 (mtS d) =
      (stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j)))).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (mtLmat d)) := by
  rw [← multivariateGaussian_zero_one, multivariateGaussian_zero_map_toEuclideanCLM
    Matrix.PosSemidef.one, Matrix.mul_one, transpose_mtLmat, mtS]

end pseudoInverse

section width

/-- The indicator vector of the block `j`. -/
noncomputable def blockInd (d : Fin m → ℕ) (j : Fin m) : EuclideanSpace ℝ (Σ j, Fin (d j)) :=
  WithLp.toLp 2 fun i ↦ if i.1 = j then 1 else 0

lemma inner_blockInd (j : Fin m) (v : EuclideanSpace ℝ (Σ j, Fin (d j))) :
    ⟪blockInd d j, v⟫ = blockSum v j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [dotProduct, Fintype.sum_sigma, blockInd, blockSum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

/-- The coordinates of `L g` in the block `j`: a linear form of `g` (constant on the block) plus
`√d_j g ⟨j, k⟩`. -/
lemma mtL_apply_mk (hd : ∀ j, 0 < d j) (g : EuclideanSpace ℝ (Σ j, Fin (d j))) (j : Fin m)
    (k : Fin (d j)) :
    mtL d g ⟨j, k⟩ = ⟪(mtA d * (d j : ℝ)⁻¹) • muVec d - (√(d j) / d j) • blockInd d j, g⟫ +
      √(d j) * ⟪EuclideanSpace.single ⟨j, k⟩ 1, g⟫ := by
  rw [mtL_apply, inner_sub_left, real_inner_smul_left, real_inner_smul_left, inner_blockInd,
    EuclideanSpace.inner_single_left]
  simp only [PiLp.add_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, muVec_apply,
    smul_eq_mul, conj_trivial, one_mul]
  rw [Finset.sum_eq_single j]
  · rw [blockCenter_apply_mk_self]
    have := hd j
    field_simp
    ring
  · intro l _ hl
    rw [blockCenter_apply_mk_of_ne l g (Ne.symm hl), mul_zero]
  · simp

/-- `⨆ i, (b + c * f i) = b + c * ⨆ i, f i` for `c ≥ 0` over a finite nonempty index set. -/
lemma ciSup_const_add_const_mul {ι : Type*} [Finite ι] [Nonempty ι] (b : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (f : ι → ℝ) :
    ⨆ i, (b + c * f i) = b + c * ⨆ i, f i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
  have hsup : ⨆ i, f i = f i₀ :=
    le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range f) i₀)
  rw [hsup]
  refine le_antisymm (ciSup_le fun i ↦ by gcongr; exact hi₀ i) ?_
  exact le_ciSup (Finite.bddAbove_range fun i ↦ b + c * f i) i₀

/-- The expected block maximum of `L g` is at most `√(2 d_j log d_j)`. -/
lemma integral_iSup_mtL_le (hd : ∀ j, 0 < d j) (j : Fin m) :
    ∫ g, ⨆ k, mtL d g ⟨j, k⟩ ∂stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j))) ≤
      √(2 * d j * log (d j)) := by
  have : Nonempty (Fin (d j)) := ⟨⟨0, hd j⟩⟩
  set w := (mtA d * (d j : ℝ)⁻¹) • muVec d - (√(d j) / d j) • blockInd d j with hw
  have hfun : (fun g : EuclideanSpace ℝ (Σ j, Fin (d j)) ↦ ⨆ k, mtL d g ⟨j, k⟩) =
      fun g ↦ ⟪w, g⟫ + √(d j) * ⨆ k, ⟪EuclideanSpace.single ⟨j, k⟩ (1 : ℝ), g⟫ := by
    ext g
    simp_rw [mtL_apply_mk hd g j]
    exact ciSup_const_add_const_mul _ (Real.sqrt_nonneg _) _
  have hsg : ∀ k : Fin (d j), HasSubgaussianMGF
      (fun g ↦ ⟪EuclideanSpace.single (⟨j, k⟩ : Σ j, Fin (d j)) (1 : ℝ), g⟫) 1
      (stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j)))) := fun k ↦
    (hasSubgaussianMGF_inner_stdGaussian _).mono (by simp)
  have hint1 : Integrable (fun g : EuclideanSpace ℝ (Σ j, Fin (d j)) ↦ ⟪w, g⟫)
      (stdGaussian _) := IsGaussian.integrable_id.const_inner w
  have hint2 : Integrable (fun g : EuclideanSpace ℝ (Σ j, Fin (d j)) ↦
      ⨆ k, ⟪EuclideanSpace.single (⟨j, k⟩ : Σ j, Fin (d j)) (1 : ℝ), g⟫) (stdGaussian _) :=
    integrable_iSup_of_hasSubgaussianMGF hsg
  have hw0 : ∫ g, ⟪w, g⟫ ∂stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j))) = 0 := by
    have := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id
      (μ := stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j))))) w
    simp only [id] at this
    rw [this, integral_id_stdGaussian, inner_zero_right]
  rw [hfun, integral_add hint1 (hint2.const_mul _), integral_const_mul, hw0, zero_add]
  have h := integral_iSup_inner_stdGaussian_le (E := EuclideanSpace ℝ (Σ j, Fin (d j)))
    (y := fun k : Fin (d j) ↦ EuclideanSpace.single (⟨j, k⟩ : Σ j, Fin (d j)) (1 : ℝ))
    (σ := 1) (fun k ↦ by simp)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, one_mul] at h
  calc √(d j) * ∫ g, ⨆ k, ⟪EuclideanSpace.single (⟨j, k⟩ : Σ j, Fin (d j)) (1 : ℝ), g⟫
        ∂stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j)))
      ≤ √(d j) * √(2 * log (d j)) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = √(2 * d j * log (d j)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring

/-- **Width of the multi-task set** (Proposition `prop:width_multitask`): the intrinsic width of
the multi-task set with block sizes `d_j ≥ 1` is at most `∑ j, √(2 d_j log d_j)`. -/
theorem intrinsicGw_multitaskSet_le (hd : ∀ j, 0 < d j) :
    intrinsicGw (multitaskSet d) ≤ ∑ j, √(2 * d j * log (d j)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [intrinsicGw]
    have : IsEmpty (Fin (Module.finrank ℝ (Submodule.span ℝ (multitaskSet d)))) := by
      rw [Submodule.span_eq_bot.2 (fun x _ ↦ Subsingleton.elim x 0), finrank_bot]
      exact Fin.isEmpty'
    rw [gw_of_isEmpty]
    simp
  have hne := multitaskSet_nonempty hd
  calc intrinsicGw (multitaskSet d)
      ≤ gaussianWidth (multitaskSet d) (multivariateGaussian 0 (mtS d)) :=
        intrinsicGw_le_gaussianWidth hne (fun x hx ↦ norm_le_of_mem_multitaskSet hx)
          mtS_posSemidef (unifDesignMatrix_mem_designSet hd)
          (fun y ↦ by rw [toEuclideanLin_mtS]; exact mtL_mem_span hd _)
          (fun v hv ↦ by
            rw [toEuclideanLin_mtS]
            exact toEuclideanLin_unifDesignMatrix_mtL_mtL hd hm hv)
    _ = ∫ g, ∑ j, ⨆ k, mtL d g ⟨j, k⟩ ∂stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j))) := by
        rw [multivariateGaussian_mtS, gaussianWidth, integral_map
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (mtLmat d)).continuous.aemeasurable
          (continuous_supportFn hne fun x hx ↦ norm_le_of_mem_multitaskSet hx).aestronglyMeasurable]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
        dsimp only
        have hL : Matrix.toEuclideanCLM (𝕜 := ℝ) (mtLmat d) g = mtL d g := by
          rw [← toEuclideanLin_mtLmat]
          apply WithLp.ofLp_injective
          rw [Matrix.ofLp_toEuclideanCLM]
          rfl
        rw [supportFn_multitaskSet hd, hL]
    _ = ∑ j, ∫ g, ⨆ k, mtL d g ⟨j, k⟩ ∂stdGaussian (EuclideanSpace ℝ (Σ j, Fin (d j))) := by
        refine integral_finsetSum _ fun j _ ↦ ?_
        have : Nonempty (Fin (d j)) := ⟨⟨0, hd j⟩⟩
        have hfun : (fun g : EuclideanSpace ℝ (Σ j, Fin (d j)) ↦ ⨆ k, mtL d g ⟨j, k⟩) =
            fun g ↦ ⟪(mtA d * (d j : ℝ)⁻¹) • muVec d - (√(d j) / d j) • blockInd d j, g⟫ +
              √(d j) * ⨆ k, ⟪EuclideanSpace.single ⟨j, k⟩ (1 : ℝ), g⟫ := by
          ext g
          simp_rw [mtL_apply_mk hd g j]
          exact ciSup_const_add_const_mul _ (Real.sqrt_nonneg _) _
        rw [hfun]
        refine (IsGaussian.integrable_id.const_inner _).add ((integrable_iSup_of_hasSubgaussianMGF
          fun k ↦ (hasSubgaussianMGF_inner_stdGaussian _).mono (c' := 1) (by simp)).const_mul _)
    _ ≤ ∑ j, √(2 * d j * log (d j)) := Finset.sum_le_sum fun j _ ↦ integral_iSup_mtL_le hd j

end width

end COLT83
