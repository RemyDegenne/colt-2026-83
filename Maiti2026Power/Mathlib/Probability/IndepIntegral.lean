/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals of inner products of independent random variables

If `W` is an integrable centered random vector, `V` is independent of `W` and `f` is a bounded
measurable function of `V`, then `⟪f (V ω), W ω⟫` is integrable with zero integral
(`IndepFun.integral_inner_comp_eq_zero`, blueprint `lem:indep_integral_zero`).
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω 𝓥 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓥 : MeasurableSpace 𝓥}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]
  {V : Ω → 𝓥} {W : Ω → E} {f : 𝓥 → E} {C : ℝ}

omit [CompleteSpace E] [IsProbabilityMeasure P] in
/-- `⟪f (V ω), W ω⟫` is integrable when `W` is integrable and `f` is bounded and measurable. -/
lemma integrable_inner_comp (hV : AEMeasurable V P) (hf : Measurable f) (hC : ∀ v, ‖f v‖ ≤ C)
    (hW : Integrable W P) :
    Integrable (fun ω ↦ ⟪f (V ω), W ω⟫) P := by
  refine (hW.norm.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
  · exact ((hf.comp_aemeasurable hV).aestronglyMeasurable.inner hW.aestronglyMeasurable)
  · rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))

/-- **Blueprint `lem:indep_integral_zero`**: if `W` is integrable and centered, `V` is independent
of `W` and `f` is bounded and measurable, then `E⟪f(V), W⟫ = 0`. -/
lemma IndepFun.integral_inner_comp_eq_zero (hind : IndepFun V W P) (hV : AEMeasurable V P)
    (hf : Measurable f) (hC : ∀ v, ‖f v‖ ≤ C) (hW : Integrable W P)
    (hW0 : ∫ ω, W ω ∂P = 0) :
    ∫ ω, ⟪f (V ω), W ω⟫ ∂P = 0 := by
  have hWm : AEMeasurable W P := hW.aemeasurable
  have hmap : P.map (fun ω ↦ (V ω, W ω)) = (P.map V).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hV hWm).1 hind
  have hWmap : Integrable (fun w : E ↦ w) (P.map W) :=
    (integrable_map_measure aestronglyMeasurable_id hWm).2 hW
  have hprob : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV
  have hmeas : ∀ μ : Measure (𝓥 × E), AEStronglyMeasurable (fun p : 𝓥 × E ↦ ⟪f p.1, p.2⟫) μ :=
    fun μ ↦ (hf.comp measurable_fst).aestronglyMeasurable.inner
      measurable_snd.aestronglyMeasurable
  have hint : Integrable (fun p : 𝓥 × E ↦ ⟪f p.1, p.2⟫) ((P.map V).prod (P.map W)) := by
    refine ((hWmap.norm.comp_snd (P.map V)).const_mul C).mono' (hmeas _)
      (Filter.Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  calc ∫ ω, ⟪f (V ω), W ω⟫ ∂P
      = ∫ p : 𝓥 × E, ⟪f p.1, p.2⟫ ∂(P.map (fun ω ↦ (V ω, W ω))) :=
        (integral_map (hV.prodMk hWm) (hmeas _)).symm
    _ = ∫ p : 𝓥 × E, ⟪f p.1, p.2⟫ ∂((P.map V).prod (P.map W)) := by rw [hmap]
    _ = ∫ v, ∫ w, ⟪f v, w⟫ ∂(P.map W) ∂(P.map V) := integral_prod _ hint
    _ = ∫ v, ⟪f v, ∫ w, w ∂(P.map W)⟫ ∂(P.map V) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun v ↦ integral_inner hWmap (f v))
    _ = 0 := by
        have : ∫ w : E, w ∂(P.map W) = 0 := by
          rw [integral_map (f := fun w : E ↦ w) hWm measurable_id.aestronglyMeasurable]
          exact hW0
        simp [this]

end ProbabilityTheory
