/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Constant conditional distributions and functions of a variable and an independent noise

* `Kernel.mapOfConst Q G`: the kernel `x ↦ Q.map (G x)`.
* `IndepFun.hasCondDistrib_const`: if `Y ⊥ X` and `Y ~ Q` then `Y | X ~ Q`.
* `HasLaw.hasCondDistrib_snd_const`: if `(X, Y) ~ Q ⊗ R` then `Y | X ~ R`.
* `HasCondDistrib.mapOfConst`: if `Y | X ~ Q` then `G X Y | X ~ Q.map (G X)`.
* `HasCondDistrib.snd_of_const_prod`: if `(Y, Z) | X ~ Q ⊗ R` then `Z | (X, Y) ~ R`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝓧]
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓩] {P : Measure Ω}

namespace Kernel

/-- The kernel `x ↦ Q.map (G x)`: the law of `G x e` for a fresh noise `e ~ Q`. -/
noncomputable def mapOfConst (Q : Measure 𝓨) (G : 𝓧 → 𝓨 → 𝓩)
    (hG : Measurable (Function.uncurry G)) : Kernel 𝓧 𝓩 :=
  (Kernel.id ×ₖ Kernel.const 𝓧 Q).mapOfMeasurable (Function.uncurry G) hG

variable {Q : Measure 𝓨} {G : 𝓧 → 𝓨 → 𝓩} {hG : Measurable (Function.uncurry G)}

lemma mapOfConst_apply [SFinite Q] (hG : Measurable (Function.uncurry G)) (x : 𝓧) :
    mapOfConst Q G hG x = Q.map (G x) := by
  rw [mapOfConst, Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ hG, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hG measurable_prodMk_left]
  rfl

instance : IsSFiniteKernel (mapOfConst Q G hG) := by
  unfold mapOfConst
  rw [Kernel.mapOfMeasurable_eq_map]
  infer_instance

instance [IsProbabilityMeasure Q] : IsMarkovKernel (mapOfConst Q G hG) := by
  unfold mapOfConst
  rw [Kernel.mapOfMeasurable_eq_map]
  exact IsMarkovKernel.map _ hG

lemma comap_mapOfConst [SFinite Q] {𝓦 : Type*} [MeasurableSpace 𝓦] {f : 𝓦 → 𝓧}
    (hf : Measurable f) (hGf : Measurable (Function.uncurry fun w ↦ G (f w))) :
    (mapOfConst Q G hG).comap f hf = mapOfConst Q (fun w ↦ G (f w)) hGf := by
  ext w : 1
  rw [Kernel.comap_apply, mapOfConst_apply hG, mapOfConst_apply hGf]

lemma const_compProd_const (Q : Measure 𝓨) [SFinite Q] (R : Measure 𝓩) [SFinite R] :
    Kernel.const 𝓧 (Q.prod R) = Kernel.const 𝓧 Q ⊗ₖ Kernel.const (𝓧 × 𝓨) R := by
  ext x s hs
  rw [Kernel.const_apply, Kernel.compProd_apply hs, Measure.prod_apply hs]
  simp [Kernel.const_apply]

end Kernel

/-- If `Y` is independent of `X` with law `Q`, then the conditional law of `Y` given `X` is the
constant kernel `Q`. -/
lemma IndepFun.hasCondDistrib_const [IsFiniteMeasure P] {X : Ω → 𝓧} {Y : Ω → 𝓨}
    {Q : Measure 𝓨} [SFinite Q] (h : IndepFun X Y P) (hX : AEMeasurable X P) (hY : HasLaw Y Q P) :
    HasCondDistrib Y X (Kernel.const 𝓧 Q) P := by
  unfold HasCondDistrib
  rw [Measure.compProd_const]
  exact h.hasLaw_prod ⟨hX, rfl⟩ hY

/-- If `(X, Y) ~ Q ⊗ R` then the conditional law of `Y` given `X` is the constant kernel `R`. -/
lemma HasLaw.hasCondDistrib_snd_const [IsFiniteMeasure P] {X : Ω → 𝓧} {Y : Ω → 𝓨}
    {Q : Measure 𝓧} {R : Measure 𝓨} [IsProbabilityMeasure R]
    (h : HasLaw (fun ω ↦ (X ω, Y ω)) (Q.prod R) P) :
    HasCondDistrib Y X (Kernel.const 𝓧 R) P := by
  unfold HasCondDistrib
  rw [Measure.compProd_const]
  have hX : P.map X = Q := by
    rw [← Measure.fst_map_prodMk₀ h.aemeasurable.snd, h.map_eq, Measure.fst_prod]
  rw [hX]
  exact h

/-- The law of a map `(x, y) ↦ (x, G x y)` applied to `μ ⊗ Q`. -/
lemma Measure.prod_map_mapOfConst {μ : Measure 𝓧} [SFinite μ] (Q : Measure 𝓨) [SFinite Q]
    {G : 𝓧 → 𝓨 → 𝓩} (hG : Measurable (Function.uncurry G)) :
    (μ.prod Q).map (fun p ↦ (p.1, G p.1 p.2)) = μ ⊗ₘ Kernel.mapOfConst Q G hG := by
  have hΦ : Measurable (fun p : 𝓧 × 𝓨 ↦ (p.1, G p.1 p.2)) := measurable_fst.prodMk hG
  rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod,
    ← Measure.deterministic_comp_eq_map hΦ, Measure.comp_assoc]
  congr 1
  ext x : 1
  rw [Kernel.comp_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.deterministic_comp_eq_map hΦ, Kernel.prod_apply, Kernel.id_apply,
    Kernel.mapOfConst_apply hG, Measure.dirac_prod, Measure.map_map hΦ measurable_prodMk_left]
  have hGx : Measurable (G x) := hG.comp measurable_prodMk_left
  rw [Measure.map_map measurable_prodMk_left hGx]
  rfl

/-- If the conditional law of `Y` given `X` is the constant `Q`, then the conditional law of
`G X Y` given `X` is `x ↦ Q.map (G x)`. -/
lemma HasCondDistrib.mapOfConst [IsFiniteMeasure P] {X : Ω → 𝓧} {Y : Ω → 𝓨} {Q : Measure 𝓨}
    [SFinite Q] (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) {G : 𝓧 → 𝓨 → 𝓩}
    (hG : Measurable (Function.uncurry G)) :
    HasCondDistrib (fun ω ↦ G (X ω) (Y ω)) X (Kernel.mapOfConst Q G hG) P := by
  have hX := h.aemeasurable_fst
  have hY := h.aemeasurable_snd
  refine ⟨by fun_prop, ?_⟩
  have h1 := h.map_eq
  rw [Measure.compProd_const] at h1
  calc P.map (fun ω ↦ (X ω, G (X ω) (Y ω)))
      = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (p.1, G p.1 p.2)) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = ((P.map X).prod Q).map (fun p ↦ (p.1, G p.1 p.2)) := by rw [h1]
    _ = P.map X ⊗ₘ Kernel.mapOfConst Q G hG := Measure.prod_map_mapOfConst Q hG

/-- If the conditional law of `(Y, Z)` given `X` is the constant `Q ⊗ R`, then the conditional
law of `Z` given `(X, Y)` is the constant `R`. -/
lemma HasCondDistrib.snd_of_const_prod [IsFiniteMeasure P] {X : Ω → 𝓧} {Y : Ω → 𝓨} {Z : Ω → 𝓩}
    {Q : Measure 𝓨} {R : Measure 𝓩} [SFinite Q] [IsProbabilityMeasure R]
    (h : HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (Kernel.const 𝓧 (Q.prod R)) P) :
    HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) (Kernel.const (𝓧 × 𝓨) R) P := by
  rw [Kernel.const_compProd_const] at h
  exact h.of_compProd

end ProbabilityTheory
