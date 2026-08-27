/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.TwoPoint
public import COLT83.LeanMachineLearning.Run
public import COLT83.MXJ2026.CubeSet

/-!
# The adaptive lower bound on a box

On the vertex set `cubeSet u` of a box with two values `u false < u true` per coordinate, no
identification algorithm — adaptive or not — with budget `T` can be `(ε, δ)`-PAC with
`δ < 1/6` unless `T (c M)² > 1/4`, where `c` is normalized by
`c (u true - u false) d = 10 ε` and `M` bounds `|u b|` (`le_of_isPAC_cubeSet`).

The instances are the `2^d` reward vectors `c • signVec s`, `s : ι → Bool`, whose simple regret
is `c (u true - u false)` times the Hamming distance to the vertex `cubeVec u s`
(`simpleRegret_smul_signVec`). For a coordinate `j`, the two instances `s` and `flip_j s` are
both at divergence at most `T c² M² / 2` from the common central instance
`c • signVecZero s j`, so by the three-point inequality
(`IsRun.one_sub_le_measureReal_add_of_sq_le`) the algorithm errs on the coordinate `j` of the
recommendation with probability at least `1/4` on average over `s`. Summing over the `d`
coordinates, the average expected regret is at least `2.5 ε`, while an `(ε, δ)`-PAC algorithm
has expected regret at most `ε + 9 ε δ` on every instance
(`integral_simpleRegret_le_of_measureReal_le`).

Blueprint: `thm:lower_hypercube_pm`, `thm:lower_hypercube_01`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The adaptive lower bound on a box** (blueprint `thm:lower_hypercube_pm`,
`thm:lower_hypercube_01`): an identification algorithm on `cubeSet u` with budget `T` which is
`(ε, δ)`-PAC has `δ ≥ 1/6` as soon as `T (c M)² ≤ 1/4`, where `c` is the scale of the hard
instances, normalized by `c (u true - u false) d = 10 ε`, and `M` bounds the coordinates of the
box. -/
lemma le_of_isPAC_cubeSet {𝒳 : Set (EuclideanSpace ℝ ι)} {u : Bool → ℝ} (h𝒳 : 𝒳 = cubeSet u)
    (hu : u false < u true) {M c : ℝ}
    (hM : ∀ b, |u b| ≤ M) {ε δ : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hnorm : c * (u true - u false) * Fintype.card ι = 10 * ε)
    {T : ℕ} (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T)
    (hpac : IsPAC 𝒳 A ε δ) (hbudget : (T : ℝ) * (c * M) ^ 2 ≤ 1 / 4) :
    1 / 6 ≤ δ := by
  subst h𝒳
  classical
  have hmk := hA.isMarkovKernel_output
  set g : ℝ := u true - u false with hg_def
  have hg : 0 < g := by rw [hg_def]; linarith
  have hune : u false ≠ u true := ne_of_lt hu
  -- the hard instances and their canonical runs
  set θ : (ι → Bool) → EuclideanSpace ℝ ι := fun s ↦ c • signVec s with hθ_def
  have hrun := fun s ↦ hA.isRun_fixedBudgetRunMeasure
    (env := linearGaussianEnv (cubeSet u) (θ s))
  obtain ⟨P, hP⟩ : ∃ P : (ι → Bool) → Measure ((ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u),
      ∀ s, P s = A.fixedBudgetRunMeasure (linearGaussianEnv (cubeSet u) (θ s)) T :=
    ⟨_, fun _ ↦ rfl⟩
  have hprob : ∀ s, IsProbabilityMeasure (P s) := fun s ↦ by rw [hP]; infer_instance
  -- the events "the recommendation has the wrong value in the coordinate `j`"
  have hcoord : ∀ j : ι, Continuous fun x : cubeSet (ι := ι) u ↦ (x : EuclideanSpace ℝ ι) j :=
    fun j ↦ ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)).comp continuous_subtype_val
  set Bset : ι → Set (cubeSet (ι := ι) u) :=
    fun j ↦ {x | (x : EuclideanSpace ℝ ι) j = u false} with hBset
  have hBm : ∀ j, MeasurableSet (Bset j) := fun j ↦
    (hcoord j).measurable (measurableSet_singleton (u false))
  obtain ⟨q, hq⟩ : ∃ q : (ι → Bool) → ι → ℝ, ∀ s j,
      q s j = (P s).real {ω | (ω.2 : EuclideanSpace ℝ ι) j ≠ u (s j)} := ⟨_, fun _ _ ↦ rfl⟩
  have hev_true : ∀ (s : ι → Bool) (j : ι), s j = true →
      {ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u |
        (ω.2 : EuclideanSpace ℝ ι) j ≠ u (s j)} = Prod.snd ⁻¹' Bset j := by
    intro s j hsj
    ext ω
    simp only [hsj, Set.mem_ofPred_eq, Set.mem_preimage, hBset]
    exact ⟨fun h ↦ ((ω.2).2 j).resolve_left h, fun h ↦ by rw [h]; exact hune⟩
  have hev_false : ∀ (s : ι → Bool) (j : ι), s j = false →
      {ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u |
        (ω.2 : EuclideanSpace ℝ ι) j ≠ u (s j)} = Prod.snd ⁻¹' (Bset j)ᶜ := by
    intro s j hsj
    ext ω
    simp only [hsj, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, hBset]
  -- the divergence bound and the three-point inequality
  have hsqrt : √(T * (c ^ 2 * M ^ 2) / 4) ≤ 1 / 4 := by
    have h1 : (T : ℝ) * (c ^ 2 * M ^ 2) / 4 ≤ 1 / 16 := by nlinarith [hbudget]
    calc √((T : ℝ) * (c ^ 2 * M ^ 2) / 4) ≤ √(1 / 16) := Real.sqrt_le_sqrt h1
      _ = 1 / 4 := by
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hC : ∀ (s : ι → Bool) (j : ι), ∀ x ∈ cubeSet (ι := ι) u,
      ⟪x, c • signVecZero s j - θ s⟫ ^ 2 ≤ c ^ 2 * M ^ 2 := by
    intro s j x hx
    rw [hθ_def, inner_smul_signVecZero_sub]
    have hxj : |x j| ≤ M := by rcases hx j with h | h <;> rw [h] <;> exact hM _
    have h1 : (signVec s j) ^ 2 = 1 := sq_signVec_apply _
    have h2 : (x j) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxj 2
    calc (-(c * signVec s j * x j)) ^ 2 = c ^ 2 * (signVec s j) ^ 2 * (x j) ^ 2 := by ring
      _ = c ^ 2 * (x j) ^ 2 := by rw [h1, mul_one]
      _ ≤ c ^ 2 * M ^ 2 := by nlinarith [sq_nonneg c]
  have key : ∀ (j : ι) (s : ι → Bool), s j = true →
      1 / 2 ≤ q s j + q (Function.update s j (!(s j))) j := by
    intro j s hsj
    set s' := Function.update s j (!(s j)) with hs'
    have hs'j : s' j = false := by rw [hs', flipAt_apply_self, hsj]; rfl
    have hrunQ := hA.isRun_fixedBudgetRunMeasure
      (env := linearGaussianEnv (cubeSet u) (c • signVecZero s j))
    have hCq : ∀ x ∈ cubeSet (ι := ι) u,
        ⟪x, c • signVecZero s j - θ s'⟫ ^ 2 ≤ c ^ 2 * M ^ 2 := by
      have heq : c • signVecZero s j = c • signVecZero s' j := by rw [hs', signVecZero_flipAt]
      rw [heq]
      exact hC s' j
    have h3 := IsRun.one_sub_le_measureReal_add_of_sq_le (hC s j) hCq hA hrunQ (hrun s)
      (hrun s') (hBm j)
    rw [hq s j, hq s' j, hev_true s j hsj, hev_false s' j hs'j, hP s, hP s']
    linarith [hsqrt, h3]
  have hpair : ∀ (j : ι) (s : ι → Bool),
      1 / 2 ≤ q s j + q (Function.update s j (!(s j))) j := by
    intro j s
    by_cases hsj : s j = true
    · exact key j s hsj
    · have hsj' : s j = false := by simpa using hsj
      have h1 := key j (Function.update s j (!(s j)))
        (by rw [flipAt_apply_self, hsj']; rfl)
      have hinv : Function.update (Function.update s j (!(s j))) j
          (!(Function.update s j (!(s j)) j)) = s := flipAt_involutive j s
      rw [hinv] at h1
      linarith
  -- averaging over the `2^d` sign patterns
  have hflipsum : ∀ j : ι, ∑ s : ι → Bool, q (Function.update s j (!(s j))) j =
      ∑ s : ι → Bool, q s j := fun j ↦
    Fintype.sum_bijective _ (flipAt_involutive j).bijective _ _ fun _ ↦ rfl
  have hcardfun : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by simp
  have hsum : ∀ j : ι, (2 : ℝ) ^ Fintype.card ι / 4 ≤ ∑ s : ι → Bool, q s j := by
    intro j
    have h1 : ∑ _s : ι → Bool, (1 / 2 : ℝ) ≤
        ∑ s : ι → Bool, (q s j + q (Function.update s j (!(s j))) j) :=
      sum_le_sum fun s _ ↦ hpair j s
    rw [sum_add_distrib, hflipsum j, sum_const, nsmul_eq_mul, card_univ, hcardfun] at h1
    push_cast at h1
    linarith
  -- the expected regret of one instance, from below and from above
  have hZ : c * g * Fintype.card ι = 10 * ε := hnorm
  have hreg : ∀ s : ι → Bool,
      ∫ ω, simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) ∂(P s) =
        c * g * ∑ j, q s j := by
    intro s
    have hmeasA : ∀ j : ι, MeasurableSet {ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u |
        (ω.2 : EuclideanSpace ℝ ι) j ≠ u (s j)} := by
      intro j
      by_cases hsj : s j = true
      · rw [hev_true s j hsj]
        exact measurable_snd (hBm j)
      · rw [hev_false s j (by simpa using hsj)]
        exact measurable_snd (hBm j).compl
    have hpt : ∀ ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u,
        simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) =
          ∑ j, Set.indicator {ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u |
            (ω.2 : EuclideanSpace ℝ ι) j ≠ u (s j)} (fun _ ↦ c * g) ω := by
      intro ω
      rw [hθ_def, simpleRegret_smul_signVec hu hc s (ω.2).2, hammingCard, card_filter]
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Set.indicator_apply]
      by_cases h : (ω.2 : EuclideanSpace ℝ ι) j = u (s j) <;> simp [h, ← hg_def]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ ↦ (integrable_const _).indicator (hmeasA j), mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [integral_indicator_const _ (hmeasA j), hq s j]
    simp [measureReal_def, mul_comm]
  have hupper : ∀ s : ι → Bool,
      ∫ ω, simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) ∂(P s) ≤
        ε + (10 * ε - ε) * δ := by
    intro s
    have hpacs : 1 - δ ≤ (P s).real
        {ω : (ℕ → cubeSet (ι := ι) u × ℝ) × cubeSet (ι := ι) u |
          simpleRegret (cubeSet u) (θ s)
            ((ω.2 : cubeSet (ι := ι) u) : EuclideanSpace ℝ ι) ≤ ε} := by
      rw [hP s]
      exact hpac (θ s) _ _ _ _ (hrun s)
    refine integral_simpleRegret_le_of_measureReal_le measurable_snd ?_ ?_ (by linarith) hpacs
    · intro x hx
      rw [hθ_def, simpleRegret_smul_signVec hu hc s hx]
      positivity
    · intro x hx
      rw [hθ_def, simpleRegret_smul_signVec hu hc s hx, ← hZ]
      have h1 : (hammingCard u s x : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast hammingCard_le_card u s x
      nlinarith [mul_pos hc hg]
  -- combining the two bounds
  have hlow : (2 : ℝ) ^ Fintype.card ι * (10 * ε / 4) ≤
      ∑ s : ι → Bool, ∫ ω, simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) ∂(P s) := by
    simp_rw [hreg]
    rw [← mul_sum, sum_comm]
    have h1 : ∑ _j : ι, (2 : ℝ) ^ Fintype.card ι / 4 ≤ ∑ j : ι, ∑ s : ι → Bool, q s j :=
      sum_le_sum fun j _ ↦ hsum j
    rw [sum_const, nsmul_eq_mul, card_univ] at h1
    have h2 : c * g * (Fintype.card ι * ((2 : ℝ) ^ Fintype.card ι / 4)) =
        (2 : ℝ) ^ Fintype.card ι * (10 * ε / 4) := by
      rw [show c * g * (Fintype.card ι * ((2 : ℝ) ^ Fintype.card ι / 4)) =
        c * g * Fintype.card ι * ((2 : ℝ) ^ Fintype.card ι / 4) by ring, hZ]
      ring
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hhigh :
      ∑ s : ι → Bool, ∫ ω, simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) ∂(P s) ≤
        (2 : ℝ) ^ Fintype.card ι * (ε + 9 * ε * δ) := by
    calc ∑ s : ι → Bool, ∫ ω, simpleRegret (cubeSet u) (θ s) (ω.2 : EuclideanSpace ℝ ι) ∂(P s)
        ≤ ∑ _s : ι → Bool, (ε + 9 * ε * δ) := by
          refine sum_le_sum fun s _ ↦ ?_
          have := hupper s
          linarith
      _ = (2 : ℝ) ^ Fintype.card ι * (ε + 9 * ε * δ) := by
          rw [sum_const, nsmul_eq_mul, card_univ, hcardfun]
          push_cast
          ring
  have hpow : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h1 : 10 * ε / 4 ≤ ε + 9 * ε * δ := le_of_mul_le_mul_left (hlow.trans hhigh) hpow
  by_contra hcon
  push Not at hcon
  nlinarith [h1, mul_pos hε (sub_pos.2 hcon)]

end COLT83
