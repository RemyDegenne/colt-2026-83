/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Analysis.BarrierSum
public import COLT83.Mathlib.Matrix.HermitianCFC
public import COLT83.MXJ2026.OptimalDesign

/-!
# Rounding a design distribution to a fixed design

Given a design distribution `w` on `𝒳` with positive definite design matrix `A = ∑ₓ w x • x xᵀ`
and a budget `T ≥ 4 d` (`d = card ι`), we build `T` points `x₀, …, x_{T-1}` of the support of `w`
(with repetitions) whose empirical design matrix dominates `(T / 4) A` in the Loewner order
(`exists_rounding`). This is the lower-barrier half of the argument of Batson, Spielman and
Srivastava (*Twice-Ramanujan sparsifiers*), with all rank-one updates given weight one.

## The barrier argument

Whitening by `√(A⁻¹)` reduces to a design distribution `w'` with design matrix `1`. For a symmetric
matrix `B` and `l` below the spectrum of `B`, the *lower barrier potential* is
`barrier l B = tr (B - l • 1)⁻¹` (`barrier`). The greedy construction keeps the invariant
"`l_t < λ_min (B_t)` and `barrier l_t B_t ≤ 1`" with `l_t = -d + t / 2` and
`B_t = ∑_{s < t} u_s u_sᵀ`:

* `barrier_average`: if `barrier l B ≤ 1` and `∑ w' u • u uᵀ = 1`, some `u` in the support of
  `w'` has barrier score `barrierScore l B u ≥ 1` (the `w'`-average of the scores is at least
  `2 - barrier l B ≥ 1`; this is where the eigenvalue inequality `barrier_sum_ineq` enters);
* `barrier_step`: adding such a `u uᵀ` to `B` and moving `l` to `l + 1 / 2` preserves the
  invariant (Sherman–Morrison).

After `T` steps, `λ_min (B_T) > -d + T / 2 ≥ T / 4`, and un-whitening by `√A` gives the result.
The corollary `cor:fixed_design_from_distribution` of the blueprint follows: the rounded design
matrix `Σ` is positive definite, `xᵀ Σ⁻¹ x ≤ (4 / T) xᵀ A⁻¹ x` and
`gwMat 𝒳 Σ ≤ (2 / √T) gwMat 𝒳 A` (`gwMat_le_of_smul_le`).
-/

@[expose] public section

open Real
open scoped MatrixOrder Matrix

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ} {l : ℝ} {u : ι → ℝ}

section barrier

/-- The lower barrier potential `Φ_l(B) = tr (B - l I)⁻¹` of a symmetric matrix `B` at a level `l`
(meaningful for `l` below the spectrum of `B`). -/
noncomputable def barrier (l : ℝ) (B : Matrix ι ι ℝ) : ℝ := (B - l • 1)⁻¹.trace

/-- The barrier score of a vector `u` for the step from level `l` to `l + 1/2` at `B`:
`L_B(u) = uᵀ M⁻² u / Δ - uᵀ M⁻¹ u` with `M = B - (l + 1/2) I` and `Δ = Φ_{l + 1/2}(B) - Φ_l(B)`. -/
noncomputable def barrierScore (l : ℝ) (B : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  (u ⬝ᵥ ((B - (l + 1 / 2) • 1)⁻¹ * (B - (l + 1 / 2) • 1)⁻¹) *ᵥ u) /
      (barrier (l + 1 / 2) B - barrier l B) -
    u ⬝ᵥ (B - (l + 1 / 2) • 1)⁻¹ *ᵥ u

lemma eigenvalues_gt (hB : B.IsHermitian) (hl : ∀ x ∈ spectrum ℝ B, l < x) (i : ι) :
    l < hB.eigenvalues i :=
  hl _ (hB.eigenvalues_mem_spectrum_real i)

/-- `Φ_l(B) = ∑ᵢ (λᵢ - l)⁻¹` for `l` below the spectrum of `B`. -/
lemma barrier_eq_sum (hB : B.IsHermitian) (hl : ∀ x ∈ spectrum ℝ B, l < x) :
    barrier l B = ∑ i, (hB.eigenvalues i - l)⁻¹ :=
  hB.trace_inv_sub_smul_one fun x hx ↦ (hl x hx).ne'

/-- `Φ_{-d}(0) = 1`. -/
lemma barrier_neg_card_zero [Nonempty ι] :
    barrier (-(Fintype.card ι : ℝ)) (0 : Matrix ι ι ℝ) = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have h : ((0 : Matrix ι ι ℝ) - (-(Fintype.card ι : ℝ)) • 1)⁻¹ = (Fintype.card ι : ℝ)⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [zero_sub, neg_smul, neg_neg, smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hd, one_smul]
  rw [barrier, h, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hd]

/-- The barrier potential increases with the level: `Φ_l(B) < Φ_{l + 1/2}(B)`. -/
lemma barrier_lt_barrier_add_half [Nonempty ι] (hB : B.IsHermitian)
    (hl : ∀ x ∈ spectrum ℝ B, l + 1 / 2 < x) :
    barrier l B < barrier (l + 1 / 2) B := by
  have hl' : ∀ x ∈ spectrum ℝ B, l < x := fun x hx ↦ by linarith [hl x hx]
  rw [barrier_eq_sum hB hl, barrier_eq_sum hB hl']
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ ?_
  have h1 := eigenvalues_gt hB hl i
  exact inv_strictAnti₀ (by linarith) (by linarith)

/-- **One barrier step.** If `l + 1/2` is below the spectrum of `B` and `u` has barrier score at
least `1`, then `l + 1/2` is below the spectrum of `B + u uᵀ` and
`Φ_{l + 1/2}(B + u uᵀ) ≤ Φ_l(B)`. -/
lemma barrier_step [Nonempty ι] (hB : B.IsHermitian) (hl : ∀ x ∈ spectrum ℝ B, l + 1 / 2 < x)
    (hu : 1 ≤ barrierScore l B u) :
    (∀ x ∈ spectrum ℝ (B + Matrix.vecMulVec u u), l + 1 / 2 < x) ∧
      barrier (l + 1 / 2) (B + Matrix.vecMulVec u u) ≤ barrier l B := by
  have hM : (B - (l + 1 / 2) • 1).PosDef := hB.posDef_sub_smul_one_iff.2 hl
  have hMdet : IsUnit (B - (l + 1 / 2) • 1).det := (Matrix.isUnit_iff_isUnit_det _).1 hM.isUnit
  have hMt : (B - (l + 1 / 2) • 1)ᵀ = B - (l + 1 / 2) • 1 := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.isHermitian.eq
  have huu : (Matrix.vecMulVec u u).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star u
  have hB' : (B + Matrix.vecMulVec u u).IsHermitian := hB.add huu.1
  have hM' : B + Matrix.vecMulVec u u - (l + 1 / 2) • 1 =
      B - (l + 1 / 2) • 1 + Matrix.vecMulVec u u :=
    add_sub_right_comm _ _ _
  have hpos : 0 < 1 + u ⬝ᵥ (B - (l + 1 / 2) • 1)⁻¹ *ᵥ u := by
    have := hM.inv.posSemidef.dotProduct_mulVec_nonneg u
    rw [star_trivial] at this
    linarith
  have hΔ := barrier_lt_barrier_add_half hB hl
  refine ⟨?_, ?_⟩
  · rw [← hB'.posDef_sub_smul_one_iff, hM']
    exact hM.add_posSemidef huu
  · rw [barrier, hM', Matrix.trace_inv_add_vecMulVec_self hMdet hMt u hpos.ne']
    have htr : (B - (l + 1 / 2) • 1)⁻¹.trace = barrier (l + 1 / 2) B := rfl
    have key : barrier (l + 1 / 2) B - barrier l B ≤
        (u ⬝ᵥ ((B - (l + 1 / 2) • 1)⁻¹ * (B - (l + 1 / 2) • 1)⁻¹) *ᵥ u) /
          (1 + u ⬝ᵥ (B - (l + 1 / 2) • 1)⁻¹ *ᵥ u) := by
      unfold barrierScore at hu
      rw [le_div_iff₀ hpos]
      have h1 := le_sub_iff_add_le.1 hu
      rw [le_div_iff₀ (sub_pos.2 hΔ)] at h1
      linarith
    linarith

/-- **Averaging the barrier criterion.** Let `w` be a design distribution whose design matrix is
`1`. If `l` is below the spectrum of `B` and `Φ_l(B) ≤ 1`, then `l + 1/2` is below the spectrum of
`B` and some point `u` of the support of `w` has barrier score `L_B(u) ≥ 1`. -/
lemma barrier_average [Nonempty ι] (hB : B.IsHermitian) (hl : ∀ x ∈ spectrum ℝ B, l < x)
    (hΦ : barrier l B ≤ 1) {𝒴 : Set (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι →₀ ℝ}
    (hw : IsDesign 𝒴 w) (hwA : designMatrix w = 1) :
    (∀ x ∈ spectrum ℝ B, l + 1 / 2 < x) ∧
      ∃ x ∈ w.support, 1 ≤ barrierScore l B (WithLp.ofLp x) := by
  have hsum : barrier l B = ∑ i, (hB.eigenvalues i - l)⁻¹ := barrier_eq_sum hB hl
  have hapos : ∀ i, 0 < hB.eigenvalues i - l := fun i ↦ sub_pos.2 (eigenvalues_gt hB hl i)
  have ha1 : ∀ i, 1 ≤ hB.eigenvalues i - l := by
    intro i
    have h1 : (hB.eigenvalues i - l)⁻¹ ≤ 1 :=
      calc (hB.eigenvalues i - l)⁻¹ ≤ ∑ j, (hB.eigenvalues j - l)⁻¹ :=
            Finset.single_le_sum (fun j _ ↦ (inv_pos.2 (hapos j)).le) (Finset.mem_univ i)
        _ ≤ 1 := hsum ▸ hΦ
    exact (inv_le_one₀ (hapos i)).1 h1
  have hl' : ∀ x ∈ spectrum ℝ B, l + 1 / 2 < x := by
    intro x hx
    rw [hB.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    linarith [ha1 i]
  refine ⟨hl', ?_⟩
  have hΔ : 0 < barrier (l + 1 / 2) B - barrier l B :=
    sub_pos.2 (barrier_lt_barrier_add_half hB hl')
  have hl'' : ∀ x ∈ spectrum ℝ B, x ≠ l + 1 / 2 := fun x hx ↦ (hl' x hx).ne'
  have hP := hB.trace_inv_sub_smul_one_sq hl''
  have hΦ' : barrier (l + 1 / 2) B = ∑ i, (hB.eigenvalues i - (l + 1 / 2))⁻¹ :=
    barrier_eq_sum hB hl'
  -- the `w`-average of the scores is `P / Δ - Φ_{l + 1/2}(B)`
  have havg : ∑ x ∈ w.support, w x * barrierScore l B (WithLp.ofLp x) =
      ((B - (l + 1 / 2) • 1)⁻¹ * (B - (l + 1 / 2) • 1)⁻¹).trace /
        (barrier (l + 1 / 2) B - barrier l B) - barrier (l + 1 / 2) B := by
    simp_rw [barrierScore, mul_sub, mul_div_assoc']
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_mul_dotProduct_mulVec,
      sum_mul_dotProduct_mulVec, hwA, Matrix.mul_one, Matrix.mul_one]
    rfl
  have hineq : 2 - barrier l B ≤ ∑ x ∈ w.support, w x * barrierScore l B (WithLp.ofLp x) := by
    rw [havg, hP, hΦ', hsum]
    have := barrier_sum_ineq (fun i ↦ hB.eigenvalues i - l) ha1 (hsum ▸ hΦ)
    simpa only [sub_sub, Finset.sum_sub_distrib] using this
  by_contra! hcon
  obtain ⟨x₀, hx₀⟩ := hw.support_nonempty
  have hlt : ∑ x ∈ w.support, w x * barrierScore l B (WithLp.ofLp x) <
      ∑ x ∈ w.support, w x * 1 :=
    Finset.sum_lt_sum (fun x hx ↦ mul_le_mul_of_nonneg_left (hcon x hx).le (hw.nonneg x))
      ⟨x₀, hx₀, mul_lt_mul_of_pos_left (hcon x₀ hx₀) (hw.pos_of_mem_support hx₀)⟩
  simp only [mul_one, hw.sum_eq_one] at hlt
  linarith

end barrier

section rounding

variable {𝒳 : Set (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι →₀ ℝ}

omit [DecidableEq ι] in
/-- **Rounding a design distribution to a fixed design of any size `T ≥ 4 d`.** If `w` is a design
distribution on `𝒳` with positive definite design matrix `A`, then for every `T ≥ 4 d` there are
`T` points `x t` of the support of `w` (with repetitions) with `∑ₜ x t (x t)ᵀ ⪰ (T / 4) A`. -/
lemma exists_rounding [Nonempty ι] (hw : IsDesign 𝒳 w) (hA : (designMatrix w).PosDef) {T : ℕ}
    (hT : 4 * Fintype.card ι ≤ T) :
    ∃ x : Fin T → EuclideanSpace ℝ ι, (∀ t, x t ∈ w.support) ∧
      ((T : ℝ) / 4) • designMatrix w ≤ ∑ t, outerSelf (x t) := by
  classical
  set S := CFC.sqrt (designMatrix w)⁻¹ with hS
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) S with hL
  have hw' : IsDesign (L '' 𝒳) (Finsupp.mapDomain L w) := hw.mapDomain L
  have hw'A : designMatrix (Finsupp.mapDomain L w) = 1 := by
    rw [hL, designMatrix_mapDomain_toEuclideanCLM, hS, Matrix.transpose_sqrt,
      hA.sqrt_inv_mul_mul_sqrt_inv]
  have hd : (0 : ℝ) < Fintype.card ι := by positivity
  -- the greedy construction, by induction on the number of steps
  have key : ∀ t : ℕ, ∃ x : Fin t → EuclideanSpace ℝ ι, (∀ s, x s ∈ w.support) ∧
      (∀ μ ∈ spectrum ℝ (∑ s, outerSelf (L (x s))), -(Fintype.card ι : ℝ) + t / 2 < μ) ∧
      barrier (-(Fintype.card ι : ℝ) + t / 2) (∑ s, outerSelf (L (x s))) ≤ 1 := by
    intro t
    induction t with
    | zero =>
      refine ⟨Fin.elim0, fun s ↦ s.elim0, ?_, ?_⟩
      · rw [Fin.sum_univ_zero]
        intro μ hμ
        rw [spectrum.zero_eq, Set.mem_singleton_iff] at hμ
        rw [hμ]
        simp only [Nat.cast_zero, zero_div, add_zero]
        linarith
      · rw [Fin.sum_univ_zero]
        simpa using (barrier_neg_card_zero (ι := ι)).le
    | succ t ih =>
      obtain ⟨x, hxs, hspec, hΦ⟩ := ih
      have hB : (∑ s, outerSelf (L (x s))).IsHermitian := (posSemidef_sum_outerSelf _ _).1
      obtain ⟨hspec', y, hy, hscore⟩ := barrier_average hB hspec hΦ hw' hw'A
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
      have hstep := barrier_step hB hspec' hscore
      have hsum : ∑ s : Fin (t + 1),
          outerSelf (L ((Fin.snoc x x₀ : Fin (t + 1) → EuclideanSpace ℝ ι) s)) =
          ∑ s, outerSelf (L (x s)) +
            Matrix.vecMulVec (WithLp.ofLp (L x₀)) (WithLp.ofLp (L x₀)) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rfl
      have hlev : -(Fintype.card ι : ℝ) + ((t + 1 : ℕ) : ℝ) / 2 =
          -(Fintype.card ι : ℝ) + t / 2 + 1 / 2 := by push_cast; ring
      refine ⟨(Fin.snoc x x₀ : Fin (t + 1) → EuclideanSpace ℝ ι), ?_, ?_, ?_⟩
      · intro s
        refine Fin.lastCases ?_ (fun i ↦ ?_) s
        · simpa using hx₀
        · simpa using hxs i
      · rw [hsum, hlev]
        exact hstep.1
      · rw [hsum, hlev]
        exact hstep.2.trans hΦ
  obtain ⟨x, hxs, hspec, -⟩ := key T
  refine ⟨x, hxs, ?_⟩
  have hB : (∑ s, outerSelf (L (x s))).IsHermitian := (posSemidef_sum_outerSelf _ _).1
  -- `(T / 4) I ≤ B_T`
  have h1 : ((T : ℝ) / 4) • (1 : Matrix ι ι ℝ) ≤ ∑ s, outerSelf (L (x s)) := by
    refine hB.smul_one_le_iff.2 fun μ hμ ↦ ?_
    have hT' : (4 * Fintype.card ι : ℝ) ≤ T := by exact_mod_cast hT
    linarith [hspec μ hμ]
  -- un-whitening by `√A`
  have hcongr := Matrix.mul_mul_conjTranspose_le_of_le h1 (CFC.sqrt (designMatrix w))
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sqrt] at hcongr
  have hLHS : CFC.sqrt (designMatrix w) * (((T : ℝ) / 4) • (1 : Matrix ι ι ℝ)) *
      CFC.sqrt (designMatrix w) = ((T : ℝ) / 4) • designMatrix w := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hA.posSemidef.sqrt_mul_sqrt]
  have hmul : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)) * L = 1 := by
    rw [hL, hS, ← map_mul, hA.sqrt_mul_sqrt_inv, map_one]
  have hRHS : CFC.sqrt (designMatrix w) * (∑ s, outerSelf (L (x s))) * CFC.sqrt (designMatrix w) =
      ∑ s, outerSelf (x s) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hxs' : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)) (L (x s)) = x s := by
      simpa using congr_fun (congrArg DFunLike.coe hmul) (x s)
    conv_rhs => rw [← hxs', outerSelf_toEuclideanCLM, Matrix.transpose_sqrt]
  rwa [hLHS, hRHS] at hcongr

omit [Fintype ι] [DecidableEq ι] in
/-- The rounded design of `exists_rounding` has a positive definite design matrix. -/
lemma posDef_of_smul_le {A C : Matrix ι ι ℝ} (hA : A.PosDef) {T : ℕ} (hT : 0 < T)
    (h : ((T : ℝ) / 4) • A ≤ C) : C.PosDef :=
  (hA.smul (by positivity : (0 : ℝ) < T / 4)).of_le h

/-- For a design matrix `Σ ⪰ (T / 4) A`, `xᵀ Σ⁻¹ x ≤ (4 / T) xᵀ A⁻¹ x`. -/
lemma dotProduct_inv_mulVec_le_of_smul_le {A C : Matrix ι ι ℝ} (hA : A.PosDef) {T : ℕ}
    (hT : 0 < T) (h : ((T : ℝ) / 4) • A ≤ C) (x : ι → ℝ) :
    x ⬝ᵥ C⁻¹ *ᵥ x ≤ 4 / T * (x ⬝ᵥ A⁻¹ *ᵥ x) := by
  have := hA.dotProduct_inv_mulVec_le_of_smul_le (by positivity : (0 : ℝ) < T / 4) h x
  rwa [star_trivial, inv_div] at this

/-- For a design matrix `Σ ⪰ (T / 4) A`, `gwMat 𝒳 Σ ≤ (2 / √T) gwMat 𝒳 A`. -/
lemma gwMat_le_of_smul_le {A C : Matrix ι ι ℝ} {R : ℝ} (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hA : A.PosDef) {T : ℕ} (hT : 0 < T)
    (h : ((T : ℝ) / 4) • A ≤ C) :
    gwMat 𝒳 C ≤ 2 / √T * gwMat 𝒳 A := by
  have hT' : (0 : ℝ) < T / 4 := by positivity
  calc gwMat 𝒳 C ≤ gwMat 𝒳 (((T : ℝ) / 4) • A) := gwMat_anti h𝒳 hne (hA.smul hT') h
    _ = 2 / √T * gwMat 𝒳 A := by
      rw [gwMat_smul hne hR hA hT', Real.sqrt_div (by positivity) 4,
        show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        inv_div]

end rounding

end COLT83
