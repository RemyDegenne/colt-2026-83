/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.Mathlib.Analysis.InnerProductSpace.SupportFn
public import COLT83.MXJ2026.StructuredSets

/-!
# Boxes with two values per coordinate

The two hypercubes `hypercubePM ι = {-1, 1}^ι` and `hypercube01 ι = {0, 1}^ι` of the paper's
Table 1 are the sets of vertices of a box with the same two values `u false < u true` in every
coordinate:

`cubeSet u = {x : ℝ^ι | ∀ i, x i = u true ∨ x i = u false}`,

parametrized by the vertex map `cubeVec u s = (u (s i))_i`, `s : ι → Bool`. This file collects
what the lower bound of `COLT83/MXJ2026/LowerCube.lean` needs: `cubeSet u` is a finite (hence
compact) set of vectors of norm at most `M √d` when `|u b| ≤ M`, its support function is
`∑ i, max (u true * θ i) (u false * θ i)`, and, for the reward vectors `c • signVec s` of the
lower bound (`signVec s` being the sign pattern `s` as a vector of `{-1, 1}^ι`), the simple
regret of a vertex is proportional to its Hamming distance to `cubeVec u s`
(`simpleRegret_smul_signVec`).
-/

@[expose] public section

open MeasureTheory Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] {u : Bool → ℝ} {c M : ℝ} {s : ι → Bool} {j : ι}

/-- The inner product of `EuclideanSpace ℝ ι` as a sum of products of coordinates. -/
lemma inner_euclidean_eq_sum (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

section cubeSet

variable (u)

/-- The set of vertices of the box with values `u false` and `u true` in every coordinate. -/
def cubeSet : Set (EuclideanSpace ℝ ι) := {x | ∀ i, x i = u true ∨ x i = u false}

/-- The vertex of `cubeSet u` whose coordinate `i` is `u (s i)`. -/
def cubeVec (s : ι → Bool) : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ u (s i)

variable {u}

omit [Fintype ι] in
@[simp] lemma cubeVec_apply (s : ι → Bool) (i : ι) : cubeVec u s i = u (s i) := rfl

omit [Fintype ι] in
lemma cubeVec_mem_cubeSet (s : ι → Bool) : cubeVec u s ∈ cubeSet u := fun i ↦ by
  cases h : s i <;> simp [h]

omit [Fintype ι] in
lemma cubeSet_eq_range : cubeSet (ι := ι) u = Set.range (cubeVec u) := by
  classical
  refine Set.Subset.antisymm (fun x hx ↦ ⟨fun i ↦ if x i = u true then true else false, ?_⟩) ?_
  · ext i
    change u (if x i = u true then true else false) = x i
    split_ifs with h
    · exact h.symm
    · exact ((hx i).resolve_left h).symm
  · rintro _ ⟨s, rfl⟩
    exact cubeVec_mem_cubeSet s

omit [Fintype ι] in
lemma cubeSet_finite [Finite ι] : (cubeSet (ι := ι) u).Finite := by
  rw [cubeSet_eq_range]
  exact Set.finite_range _

omit [Fintype ι] in
lemma isCompact_cubeSet [Finite ι] : IsCompact (cubeSet (ι := ι) u) := cubeSet_finite.isCompact

omit [Fintype ι] in
lemma cubeSet_nonempty : (cubeSet (ι := ι) u).Nonempty :=
  ⟨cubeVec u fun _ ↦ true, cubeVec_mem_cubeSet _⟩

lemma norm_le_of_mem_cubeSet (hM : ∀ b, |u b| ≤ M) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ cubeSet u) : ‖x‖ ≤ √(Fintype.card ι * M ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, M ^ 2 := by
        refine sum_le_sum fun i _ ↦ ?_
        have h1 : ‖x i‖ ≤ M := by
          rcases hx i with h | h <;> rw [h, Real.norm_eq_abs] <;> exact hM _
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Fintype.card ι * M ^ 2 := by rw [sum_const, nsmul_eq_mul, Fintype.card]

lemma inner_cubeVec (s : ι → Bool) (θ : EuclideanSpace ℝ ι) :
    ⟪cubeVec u s, θ⟫ = ∑ i, u (s i) * θ i := inner_euclidean_eq_sum _ _

/-- The support function of a box is the sum of the coordinatewise maxima. -/
lemma supportFn_cubeSet (θ : EuclideanSpace ℝ ι) :
    supportFn (cubeSet u) θ = ∑ i, max (u true * θ i) (u false * θ i) := by
  classical
  rw [cubeSet_eq_range, supportFn_eq_sSup, ← Set.range_comp]
  change ⨆ s, ⟪cubeVec u s, θ⟫ = _
  simp_rw [inner_cubeVec]
  refine le_antisymm (ciSup_le fun s ↦ sum_le_sum fun i _ ↦ ?_) ?_
  · cases h : s i <;> simp
  · refine le_trans (le_of_eq ?_)
      (le_ciSup (Finite.bddAbove_range fun s ↦ ∑ i, u (s i) * θ i)
        (fun i ↦ decide (u false * θ i ≤ u true * θ i)))
    refine sum_congr rfl fun i _ ↦ ?_
    by_cases h : u false * θ i ≤ u true * θ i <;> simp only [h, decide_true, decide_false] <;>
      [exact max_eq_left h; exact max_eq_right (by linarith)]

end cubeSet

section signVec

variable (s j)

/-- The sign pattern `s` as a vector of `{-1, 1}^ι`. -/
def signVec : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ if s i then 1 else -1

/-- The sign pattern `s` as a vector of `{-1, 1}^ι`, with the coordinate `j` set to `0`. -/
def signVecZero [DecidableEq ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if i = j then 0 else if s i then 1 else -1

variable {s j}

omit [Fintype ι] in
@[simp] lemma signVec_apply (i : ι) : signVec s i = if s i then 1 else -1 := rfl

omit [Fintype ι] in
@[simp] lemma signVecZero_apply [DecidableEq ι] (i : ι) :
    signVecZero s j i = if i = j then 0 else if s i then 1 else -1 := rfl

omit [Fintype ι] in
lemma signVec_apply_ne_zero (i : ι) : signVec s i ≠ 0 := by
  cases h : s i <;> simp [h]

omit [Fintype ι] in
lemma sq_signVec_apply (i : ι) : signVec s i ^ 2 = 1 := by
  cases h : s i <;> simp [h]

omit [Fintype ι] in
/-- The vector `signVecZero s j` does not depend on the coordinate `j` of `s`. -/
lemma signVecZero_update [DecidableEq ι] (b : Bool) :
    signVecZero (Function.update s j b) j = signVecZero s j := by
  ext i
  by_cases h : i = j <;> simp [h]

/-- The difference of the central instance and the instance `s` is supported on `j`. -/
lemma inner_smul_signVecZero_sub [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    ⟪x, c • signVecZero s j - c • signVec s⟫ = -(c * signVec s j * x j) := by
  rw [inner_euclidean_eq_sum]
  change ∑ i, x i * (c * signVecZero s j i - c * signVec s i) = _
  rw [← Finset.sum_erase_add _ _ (mem_univ j)]
  have hzero : ∀ i ∈ univ.erase j, x i * (c * signVecZero s j i - c * signVec s i) = 0 := by
    intro i hi
    rw [signVecZero_apply, ite_eq_right (mem_erase.1 hi).1]
    simp
  rw [sum_eq_zero hzero, zero_add, signVecZero_apply, ite_eq_left rfl]
  ring

omit [Fintype ι] in
/-- Flipping the coordinate `j` of a sign pattern. -/
lemma flipAt_apply_self [DecidableEq ι] (j : ι) (s : ι → Bool) :
    Function.update s j (!(s j)) j = !(s j) := Function.update_self ..

omit [Fintype ι] in
lemma flipAt_involutive [DecidableEq ι] (j : ι) :
    Function.Involutive fun s : ι → Bool ↦ Function.update s j (!(s j)) := by
  intro s
  change Function.update (Function.update s j (!(s j))) j
    (!(Function.update s j (!(s j)) j)) = s
  rw [flipAt_apply_self, Bool.not_not, Function.update_idem, Function.update_eq_self]

omit [Fintype ι] in
lemma signVecZero_flipAt [DecidableEq ι] (j : ι) (s : ι → Bool) :
    signVecZero (Function.update s j (!(s j))) j = signVecZero s j := signVecZero_update _

end signVec

section regret

/-- The number of coordinates in which the vertex `x` differs from `cubeVec u s`. -/
noncomputable def hammingCard (u : Bool → ℝ) (s : ι → Bool) (x : EuclideanSpace ℝ ι) : ℕ :=
  (univ.filter fun i ↦ x i ≠ u (s i)).card

lemma hammingCard_le_card (u : Bool → ℝ) (s : ι → Bool) (x : EuclideanSpace ℝ ι) :
    hammingCard u s x ≤ Fintype.card ι :=
  (card_filter_le _ _).trans_eq card_univ

/-- The support function of the box at the reward vector `c • signVec s`, `c > 0`. -/
lemma supportFn_cubeSet_smul_signVec (hu : u false < u true) (hc : 0 < c) (s : ι → Bool) :
    supportFn (cubeSet u) (c • signVec s) = c * ∑ i, u (s i) * signVec s i := by
  rw [supportFn_cubeSet, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  have h : (c • signVec s) i = c * signVec s i := rfl
  rw [h]
  cases hsi : s i
  · have h1 : signVec s i = -1 := by simp [signVec_apply, hsi]
    rw [h1, max_eq_right (by nlinarith)]
    ring
  · have h1 : signVec s i = 1 := by simp [signVec_apply, hsi]
    rw [h1, max_eq_left (by nlinarith)]
    ring

/-- **The simple regret on a box is a Hamming distance**: for `c > 0` and `u false < u true`,
the simple regret of the vertex `x` under the reward vector `c • signVec s` is
`c (u true - u false)` times the number of coordinates in which `x` differs from
`cubeVec u s`. -/
lemma simpleRegret_smul_signVec (hu : u false < u true) (hc : 0 < c) (s : ι → Bool)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ cubeSet u) :
    simpleRegret (cubeSet u) (c • signVec s) x =
      c * (u true - u false) * hammingCard u s x := by
  have hinner : ⟪x, c • signVec s⟫ = c * ∑ i, x i * signVec s i := by
    rw [inner_euclidean_eq_sum, mul_sum]
    exact sum_congr rfl fun i _ ↦ by
      change x i * (c * signVec s i) = c * (x i * signVec s i)
      ring
  have hsr : simpleRegret (cubeSet u) (c • signVec s) x =
      supportFn (cubeSet u) (c • signVec s) - ⟪x, c • signVec s⟫ := rfl
  rw [hsr, supportFn_cubeSet_smul_signVec hu hc, hinner, ← mul_sub, ← sum_sub_distrib]
  have hterm : ∀ i, u (s i) * signVec s i - x i * signVec s i =
      if x i = u (s i) then 0 else u true - u false := by
    intro i
    by_cases h : x i = u (s i)
    · simp [h]
    · rw [ite_eq_right h]
      have hxi : x i = u (!s i) := by
        rcases hx i with h' | h' <;> cases hsi : s i <;> simp_all
      cases hsi : s i
      · simp only [hsi, Bool.not_false] at hxi
        have h1 : signVec s i = -1 := by simp [signVec_apply, hsi]
        rw [h1, hxi]
        ring
      · simp only [hsi, Bool.not_true] at hxi
        have h1 : signVec s i = 1 := by simp [signVec_apply, hsi]
        rw [h1, hxi]
        ring
  simp_rw [hterm]
  rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, hammingCard]
  simp only [ne_eq]
  ring

end regret

section hypercubes

omit [Fintype ι] in
lemma hypercubePM_eq_cubeSet :
    hypercubePM ι = cubeSet (ι := ι) (fun b ↦ if b then 1 else -1) := by
  ext x
  simp [hypercubePM, cubeSet]

omit [Fintype ι] in
lemma hypercube01_eq_cubeSet :
    hypercube01 ι = cubeSet (ι := ι) (fun b ↦ if b then 1 else 0) := by
  ext x
  simp only [hypercube01, cubeSet, Set.mem_ofPred_eq, ite_true]
  exact forall_congr' fun i ↦ or_comm

end hypercubes

end COLT83
