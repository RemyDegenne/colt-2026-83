/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedBudget
public import COLT83.Mathlib.InformationTheory.Pinsker

/-!
# Two- and three-point inequalities for identification algorithms

Companions of the Bretagnolle–Huber inequality `IsRun.exp_neg_le_measureReal_add_of_sq_le`,
for the regime in which the divergence is *small*: there Pinsker's inequality is sharper.

For two runs of a fixed-budget identification algorithm with budget `T` in the linear Gaussian
environments of two reward vectors `θ`, `θ'` with `⟪x, θ - θ'⟫ ^ 2 ≤ C` on the action set, the
probabilities of a common event of the output differ by at most `√(T C / 4)`
(`IsRun.abs_measureReal_sub_le_of_sq_le`, the *two-point inequality*). Applying this to a third,
central reward vector `θ` and two alternatives `θ⁺`, `θ⁻` gives the *three-point inequality*
`Prob_{θ⁺}(out ∈ B) + Prob_{θ⁻}(out ∉ B) ≥ 1 - 2 √(T C / 4)`
(`IsRun.one_sub_le_measureReal_add_of_sq_le`): no algorithm can decide between `θ⁺` and `θ⁻`
when both are close to `θ`.

Finally, an `(ε, δ)`-PAC algorithm has expected simple regret at most `ε + (Z - ε) δ` on an
instance whose regret is bounded by `Z` (`integral_simpleRegret_le_of_measureReal_le`): the
lower bounds of the paper's Table 1 bound the *average* expected regret over a finite family of
instances from below and conclude with this inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal RealInnerProductSpace

namespace Learning.LinearBandit

open IdentAlg

variable {E 𝓞 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace.CountablyGenerated E] {m𝓞 : MeasurableSpace 𝓞}
  {𝒳 : Set E} {θ θ' : E} {A : IdentAlg 𝒳 ℝ 𝓞} {T : ℕ}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {X' : ℕ → Ω' → 𝒳} {Y' : ℕ → Ω' → ℝ} {out : Ω → 𝓞}
  {out' : Ω' → 𝓞}

/-- The divergence between the laws of the outputs of two runs of a fixed-budget algorithm with
budget `T` in the linear Gaussian environments with reward vectors `θ` and `θ'` is at most the
expected sum of the squared gaps along the trajectory of the first run (the *divergence
decomposition*, transferred to the outputs by data processing). -/
lemma IsRun.klDiv_map_out_le_sum_integral {C : ℝ} (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      ENNReal.ofReal (∑ t ∈ Finset.range T, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P) := by
  rcases Nat.eq_zero_or_eq_succ_pred T with hT | hT
  · subst hT
    rw [IdentAlg.IsRun.klDiv_map_out_eq_zero hA h h']
    exact bot_le
  · rw [hT] at hA ⊢
    exact (IdentAlg.IsRun.klDiv_map_out_le hA h h').trans
      (klDiv_map_history_of_sq_le h.isAlgEnvSeq h'.isAlgEnvSeq hC (T - 1)).le

/-- **Two-point inequality with a data-dependent divergence** (blueprint `lem:two_point_pinsker`):
if the expected sum of the squared gaps along the trajectory is at most `K`, the probabilities of
any event of the output differ by at most `√(K / 2)`. -/
lemma IsRun.abs_measureReal_sub_le_of_sum_le {C K : ℝ} (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C)
    (hK : ∑ t ∈ Finset.range T, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P ≤ K)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') X' Y' out' P') {B : Set 𝓞} (hB : MeasurableSet B) :
    |P.real (out ⁻¹' B) - P'.real (out' ⁻¹' B)| ≤ √(K / 2) := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hout' : AEMeasurable out' P' := h'.hasCondDistrib_output.aemeasurable_snd
  have hkl := (IsRun.klDiv_map_out_le_sum_integral hC hA h h').trans
    (ENNReal.ofReal_le_ofReal hK)
  have hne : klDiv (P.map out) (P'.map out') ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have : IsProbabilityMeasure (P.map out) := Measure.isProbabilityMeasure_map hout
  have : IsProbabilityMeasure (P'.map out') := Measure.isProbabilityMeasure_map hout'
  have hK0 : 0 ≤ K :=
    le_trans (Finset.sum_nonneg fun t _ ↦ integral_nonneg fun ω ↦ by positivity) hK
  rw [← map_measureReal_apply_of_aemeasurable hout hB,
    ← map_measureReal_apply_of_aemeasurable hout' hB]
  refine (abs_sub_le_sqrt_klDiv hB hne).trans (Real.sqrt_le_sqrt ?_)
  have : (klDiv (P.map out) (P'.map out')).toReal ≤ K :=
    ENNReal.toReal_le_of_le_ofReal hK0 hkl
  linarith

/-- **Two-point inequality** (blueprint `lem:two_point_pinsker`): for two runs of a fixed-budget
identification algorithm with budget `T` in the linear Gaussian environments with reward vectors
`θ` and `θ'`, with `⟪x, θ - θ'⟫ ^ 2 ≤ C` on the action set, the probabilities of any event of the
output differ by at most `√(T C / 4)`. -/
lemma IsRun.abs_measureReal_sub_le_of_sq_le {C : ℝ} (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') X' Y' out' P') {B : Set 𝓞} (hB : MeasurableSet B) :
    |P.real (out ⁻¹' B) - P'.real (out' ⁻¹' B)| ≤ √(T * C / 4) := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hout' : AEMeasurable out' P' := h'.hasCondDistrib_output.aemeasurable_snd
  have hkl := IsRun.klDiv_map_out_le_of_sq_le hC hA h h'
  have hne : klDiv (P.map out) (P'.map out') ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have : IsProbabilityMeasure (P.map out) := Measure.isProbabilityMeasure_map hout
  have : IsProbabilityMeasure (P'.map out') := Measure.isProbabilityMeasure_map hout'
  have hC0 : 0 ≤ C := by
    obtain ⟨ω⟩ := Measure.nonempty_of_neZero P
    exact (sq_nonneg _).trans (hC _ (X 0 ω).2)
  rw [← map_measureReal_apply_of_aemeasurable hout hB,
    ← map_measureReal_apply_of_aemeasurable hout' hB]
  refine (abs_sub_le_sqrt_klDiv hB hne).trans (Real.sqrt_le_sqrt ?_)
  have : (klDiv (P.map out) (P'.map out')).toReal ≤ T * (C / 2) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hkl
  linarith

/-- **Three-point inequality** (blueprint `lem:log_gains_three_point`): if the two reward vectors
`θp` and `θm` both satisfy `⟪x, θ - θp⟫ ^ 2 ≤ C`, resp. `⟪x, θ - θm⟫ ^ 2 ≤ C`, on the action set,
then no test on the output of a fixed-budget algorithm with budget `T` separates them:
`Prob_{θp}(out ∈ B) + Prob_{θm}(out ∉ B) ≥ 1 - 2 √(T C / 4)`. -/
lemma IsRun.one_sub_le_measureReal_add_of_sq_le {C : ℝ} {θp θm : E}
    {Ωp Ωm : Type*} {mΩp : MeasurableSpace Ωp} {mΩm : MeasurableSpace Ωm}
    {Pp : Measure Ωp} {Pm : Measure Ωm} [IsProbabilityMeasure Pp] [IsProbabilityMeasure Pm]
    {Xp : ℕ → Ωp → 𝒳} {Yp : ℕ → Ωp → ℝ} {outp : Ωp → 𝓞}
    {Xm : ℕ → Ωm → 𝒳} {Ym : ℕ → Ωm → ℝ} {outm : Ωm → 𝓞}
    (hCp : ∀ x ∈ 𝒳, ⟪x, θ - θp⟫ ^ 2 ≤ C) (hCm : ∀ x ∈ 𝒳, ⟪x, θ - θm⟫ ^ 2 ≤ C)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P)
    (hp : A.IsRun (linearGaussianEnv 𝒳 θp) Xp Yp outp Pp)
    (hm : A.IsRun (linearGaussianEnv 𝒳 θm) Xm Ym outm Pm)
    {B : Set 𝓞} (hB : MeasurableSet B) :
    1 - 2 * √(T * C / 4) ≤ Pp.real (outp ⁻¹' B) + Pm.real (outm ⁻¹' Bᶜ) := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hsum : P.real (out ⁻¹' B) + P.real (out ⁻¹' Bᶜ) = 1 := by
    have : IsProbabilityMeasure (P.map out) := Measure.isProbabilityMeasure_map hout
    rw [← map_measureReal_apply_of_aemeasurable hout hB,
      ← map_measureReal_apply_of_aemeasurable hout hB.compl]
    rw [measureReal_compl hB, probReal_univ]
    ring
  have h1 := abs_le.1 (IsRun.abs_measureReal_sub_le_of_sq_le hCp hA h hp hB)
  have h2 := abs_le.1 (IsRun.abs_measureReal_sub_le_of_sq_le hCm hA h hm hB.compl)
  linarith [h1.2, h2.2]

variable {ε δ Z : ℝ}

omit [MeasurableSpace.CountablyGenerated E] in
/-- **From a PAC guarantee to an expected regret bound** (blueprint
`lem:fail_prob_from_expected_value`): if the recommendation is `ε`-optimal with probability at
least `1 - δ` and the simple regret on the instance `θ` is between `0` and `Z ≥ ε`, then the
expected simple regret is at most `ε + (Z - ε) δ`. -/
lemma integral_simpleRegret_le_of_measureReal_le {out : Ω → 𝒳} (hout : Measurable out)
    (h0 : ∀ x ∈ 𝒳, 0 ≤ simpleRegret 𝒳 θ x) (hZ : ∀ x ∈ 𝒳, simpleRegret 𝒳 θ x ≤ Z)
    (hεZ : ε ≤ Z) (hpac : 1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε}) :
    ∫ ω, simpleRegret 𝒳 θ (out ω) ∂P ≤ ε + (Z - ε) * δ := by
  have hmeas : Measurable fun ω ↦ simpleRegret 𝒳 θ (out ω) :=
    ((continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable).comp hout
  set G : Set Ω := {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} with hG
  have hGm : MeasurableSet G := measurableSet_le hmeas measurable_const
  have hint : Integrable (fun ω ↦ simpleRegret 𝒳 θ (out ω)) P :=
    Integrable.of_bound hmeas.aestronglyMeasurable |Z|
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (h0 _ (out ω).2)]
        exact (hZ _ (out ω).2).trans (le_abs_self Z))
  have hind : Integrable (Gᶜ.indicator fun _ ↦ (Z - ε)) P :=
    (integrable_const (Z - ε)).indicator hGm.compl
  have hbound : (fun ω ↦ simpleRegret 𝒳 θ (out ω)) ≤
      fun ω ↦ ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω := by
    intro ω
    change simpleRegret 𝒳 θ (out ω) ≤ ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      have hε : simpleRegret 𝒳 θ (out ω) ≤ ε := hω
      linarith
    · rw [Set.indicator_of_mem hω]
      have := hZ _ (out ω).2
      linarith
  have hδ : P.real Gᶜ ≤ δ := by
    rw [measureReal_compl hGm, probReal_univ]
    linarith
  calc ∫ ω, simpleRegret 𝒳 θ (out ω) ∂P
      ≤ ∫ ω, ε + Gᶜ.indicator (fun _ ↦ (Z - ε)) ω ∂P :=
        integral_mono hint ((integrable_const ε).add hind) hbound
    _ = ε + P.real Gᶜ * (Z - ε) := by
        rw [integral_add (integrable_const ε) hind, integral_const,
          integral_indicator_const _ hGm.compl]
        simp [measureReal_def]
    _ ≤ ε + (Z - ε) * δ := by
        have : 0 ≤ Z - ε := by linarith
        nlinarith

end Learning.LinearBandit
