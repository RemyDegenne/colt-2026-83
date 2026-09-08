/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Lemmas on conditional distributions and kernels

General facts about `HasCondDistrib` (and a few kernel identities) used throughout the
sequential-learning developments:

* `Kernel.const_comap_eq`: a kernel identity;
* `HasCondDistrib.comp_hasLaw`: a conditional distribution is transported along a map `g`
  carrying `P` to `P'`;
* `HasCondDistrib.const_comp_right`: a constant conditional law given `Z` is a constant
  conditional law given any measurable function of `Z`;
* `hasCondDistrib_snd_compProd_comap`: the conditional law of the second coordinate under
  `μ ⊗ₘ η.comap f`, and the transport `map_prodMk_compProd_comap`,
  `map_snd_compProd_comap` of that measure along `f`;
* `HasCondDistrib.measureReal_le_mul`, `HasCondDistrib.measureReal_sub_le`: a uniform bound on
  the conditional probability of an event given `Z` bounds its probability (Fubini);
* `Measure.map_compProd_of_forall_map_eq`, `HasCondDistrib.map_of_forall_map_eq`: the image of a
  composition-product `μ ⊗ₘ κ` by a map `(a, b) ↦ (G a, F a b)` is the composition-product
  `μ.map G ⊗ₘ K` when `K (G a) = (κ a).map (F a)`;
* `HasCondDistrib.restrict_preimage`: a conditional law given `X` is preserved by restricting the
  measure to an event determined by `X`;
* `Measure.restrict_compProd_prod_univ`: `(μ ⊗ₘ κ).restrict (s ×ˢ univ) = μ.restrict s ⊗ₘ κ`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section kernel

variable {α β γ 𝓧 𝓩 : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩}

lemma Kernel.const_comap_eq (ν : Measure β) {f : 𝓧 → 𝓩} (hf : Measurable f) :
    (Kernel.const 𝓩 ν).comap f hf = Kernel.const 𝓧 ν := by
  ext a s _
  simp [Kernel.comap_apply]

end kernel

section transport

variable {Ω Ω' 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {P' : Measure Ω'}
  {g : Ω → Ω'}

/-- A conditional distribution is transported along a map `g` carrying `P` to `P'`. -/
lemma HasCondDistrib.comp_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩}
    {κ : Kernel 𝓧 𝓩} (h : HasCondDistrib Z X κ P') (hg : HasLaw g P' P) :
    HasCondDistrib (Z ∘ g) (X ∘ g) κ P := by
  have h' : HasLaw ((fun ω ↦ (X ω, Z ω)) ∘ g) (P'.map X ⊗ₘ κ) P := HasLaw.comp h hg
  have hX : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable (hg.map_eq ▸ h.aemeasurable_fst)
      hg.aemeasurable]
  rw [hX] at h'
  exact h'

end transport

section const

variable {Ω β 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {ν : Measure β} {Y : Ω → β}

/-- A constant conditional law given `Z` is a constant conditional law given any measurable
function of `Z`. -/
lemma HasCondDistrib.const_comp_right [SFinite P] [SFinite ν] {Z : Ω → 𝓩}
    (h : HasCondDistrib Y Z (Kernel.const 𝓩 ν) P)
    {f : 𝓩 → 𝓧} (hf : Measurable f) : HasCondDistrib Y (f ∘ Z) (Kernel.const 𝓧 ν) P := by
  refine HasCondDistrib.comp_right (hf := hf) ?_
  rwa [Kernel.const_comap_eq]

end const

section compProd

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Under `μ ⊗ₘ η.comap f`, the second coordinate has conditional law `η` given `f` of the
first coordinate, when `η` is a probability measure at every point of the range of `f`. -/
lemma hasCondDistrib_snd_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f)
    (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    HasCondDistrib Prod.snd (fun p : α × γ ↦ f p.1) η (μ ⊗ₘ η.comap f hf) := by
  have hκ : IsMarkovKernel (η.comap f hf) := ⟨fun a ↦ by rw [Kernel.comap_apply]; exact hη a⟩
  have hfst : (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1) = μ.map f := by
    calc (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1)
        = ((μ ⊗ₘ η.comap f hf).map Prod.fst).map f := (Measure.map_map hf measurable_fst).symm
      _ = μ.map f := by
        rw [show (μ ⊗ₘ η.comap f hf).map Prod.fst = (μ ⊗ₘ η.comap f hf).fst from rfl,
          Measure.fst_compProd]
  refine ⟨by fun_prop, ?_⟩
  rw [hfst]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.comap_apply]
  rfl

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`. -/
lemma map_prodMk_compProd_comap (μ : Measure α) [SFinite μ] (η : Kernel β γ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η := by
  have hκ : IsMarkovKernel (η.comap f hf) := ⟨fun a ↦ by rw [Kernel.comap_apply]; exact hη a⟩
  have h := (hasCondDistrib_snd_compProd_comap μ η hf hη).map_eq
  have hfst : (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1) = μ.map f := by
    calc (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1)
        = ((μ ⊗ₘ η.comap f hf).map Prod.fst).map f := (Measure.map_map hf measurable_fst).symm
      _ = μ.map f := by
        rw [show (μ ⊗ₘ η.comap f hf).map Prod.fst = (μ ⊗ₘ η.comap f hf).fst from rfl,
          Measure.fst_compProd]
  rwa [hfst] at h

/-- Transporting `μ ⊗ₘ η.comap f` along `f` in the first coordinate gives `μ.map f ⊗ₘ η`, for
any s-finite kernel `η`. -/
lemma _root_.MeasureTheory.Measure.map_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f) :
    (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ (f p.1, p.2)) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

/-- The image of `μ ⊗ₘ κ` by `(a, b) ↦ (G a, F a b)` is `μ.map G ⊗ₘ K` as soon as `K (G a)` is
the image of `κ a` by `F a` for every `a`. -/
lemma _root_.MeasureTheory.Measure.map_compProd_of_forall_map_eq {δ : Type*}
    {mδ : MeasurableSpace δ} (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {G : α → γ} (hG : Measurable G)
    {F : α → β → δ} (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ) [IsSFiniteKernel K]
    (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    (μ ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) = μ.map G ⊗ₘ K := by
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  ext s hs
  rw [Measure.map_apply hφ hs, Measure.compProd_apply (hφ hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hG]
  refine lintegral_congr fun a ↦ ?_
  have hFa : Measurable (F a) := hF.comp measurable_prodMk_left
  rw [hK a, Measure.map_apply hFa (measurable_prodMk_left hs)]
  rfl

/-- The restriction of `μ ⊗ₘ κ` to `s ×ˢ univ` is `μ.restrict s ⊗ₘ κ`. -/
lemma _root_.MeasureTheory.Measure.restrict_compProd_prod_univ (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ Set.univ) = μ.restrict s ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht, ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = Prod.mk a ⁻¹' t := by ext b; simp [ha]
    simp [Set.indicator, ha, this]
  · have : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = ∅ := by ext b; simp [ha]
    simp [Set.indicator, ha, this]

/-- The law of the second coordinate is unchanged by that transport. -/
lemma map_snd_compProd_comap (μ : Measure α) [SFinite μ] (η : Kernel β γ) [IsSFiniteKernel η]
    {f : α → β} (hf : Measurable f) (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    (μ ⊗ₘ η.comap f hf).map Prod.snd = (μ.map f ⊗ₘ η).map Prod.snd := by
  rw [← map_prodMk_compProd_comap μ η hf hη, Measure.map_map measurable_snd (by fun_prop)]
  rfl

end compProd

section map

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {P : Measure Ω}
  [SFinite P] {X : Ω → α} {Y : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ]

/-- If `Y` has conditional law `κ` given `X`, then `F X Y` has conditional law `K` given `G X`
as soon as `K (G a)` is the image of `κ a` by `F a` for every `a`. -/
lemma HasCondDistrib.map_of_forall_map_eq (h : HasCondDistrib Y X κ P) {G : α → γ}
    (hG : Measurable G) {F : α → β → δ} (hF : Measurable (Function.uncurry F)) (K : Kernel γ δ)
    [IsSFiniteKernel K] (hK : ∀ a, K (G a) = (κ a).map (F a)) :
    HasCondDistrib (fun ω ↦ F (X ω) (Y ω)) (G ∘ X) K P := by
  refine ⟨(hG.comp_aemeasurable h.aemeasurable_fst).prodMk (hF.comp_aemeasurable h.aemeasurable),
    ?_⟩
  have hφ : Measurable fun p : α × β ↦ (G p.1, F p.1 p.2) := (hG.comp measurable_fst).prodMk hF
  calc P.map (fun ω ↦ ((G ∘ X) ω, F (X ω) (Y ω)))
      = (P.map (fun ω ↦ (X ω, Y ω))).map (fun p ↦ (G p.1, F p.1 p.2)) := by
        rw [AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable h.aemeasurable]
        rfl
    _ = (P.map X ⊗ₘ κ).map (fun p ↦ (G p.1, F p.1 p.2)) := by rw [h.map_eq]
    _ = (P.map X).map G ⊗ₘ K := Measure.map_compProd_of_forall_map_eq _ _ hG hF K hK
    _ = P.map (G ∘ X) ⊗ₘ K := by
        rw [AEMeasurable.map_map_of_aemeasurable hG.aemeasurable h.aemeasurable_fst]

/-- A conditional law given `X` is a conditional law given `(c, X)` for any constant `c`. -/
lemma HasCondDistrib.prodMk_const_left (h : HasCondDistrib Y X κ P) (c : γ) :
    HasCondDistrib Y (fun ω ↦ (c, X ω)) (κ.prodMkLeft γ) P :=
  h.map_of_forall_map_eq (G := fun a ↦ (c, a)) (by fun_prop) (F := fun _ b ↦ b) measurable_snd _
    fun a ↦ by simp [Kernel.prodMkLeft_apply]

/-- A conditional law given `X` is a conditional law given `X` under the restriction of `P` to an
event determined by `X`. -/
lemma HasCondDistrib.restrict_preimage (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have h1 : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by ext ω; simp
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map (hX.prodMk hY) (hs.prod MeasurableSet.univ), h1]
    _ = (P.map X ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by rw [h.map_eq]
    _ = (P.map X).restrict s ⊗ₘ κ := Measure.restrict_compProd_prod_univ _ _ hs
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by rw [Measure.restrict_map hX hs]

end map

section bound

variable {Ω β 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} [IsFiniteMeasure P] {W : Ω → β} {Z : Ω → 𝓩}
  {κ : Kernel 𝓩 β} {G : Set 𝓩} {G' : Set (𝓩 × β)} {δ : ℝ}

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at most `δ`, then
`P(Z ∈ G, (Z, W) ∈ G') ≤ δ P(Z ∈ G)`. -/
lemma HasCondDistrib.measureReal_le_mul [IsFiniteKernel κ] (h : HasCondDistrib W Z κ P)
    (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, (κ z).real (Prod.mk z ⁻¹' G') ≤ δ) :
    P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤ δ * P.real (Z ⁻¹' G) := by
  have hS : MeasurableSet ((G ×ˢ Set.univ) ∩ G') := (hG.prod MeasurableSet.univ).inter hG'
  have h1 : Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G' =
      (fun ω ↦ (Z ω, W ω)) ⁻¹' ((G ×ˢ Set.univ) ∩ G') := by
    ext ω
    simp
  have h2 : ∀ z, κ z (Prod.mk z ⁻¹' ((G ×ˢ Set.univ) ∩ G')) =
      G.indicator (fun z ↦ κ z (Prod.mk z ⁻¹' G')) z := fun z ↦ by
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      congr 1
      ext w
      simp [hz]
    · rw [Set.indicator_of_notMem hz]
      convert measure_empty (μ := κ z)
      ext w
      simp [hz]
  rw [h1, measureReal_def, measureReal_def,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hG,
    ← Measure.map_apply_of_aemeasurable h.aemeasurable hS, h.map_eq, Measure.compProd_apply hS]
  simp_rw [h2]
  rw [lintegral_indicator hG, ← ENNReal.toReal_ofReal hδ0, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
  rw [← setLIntegral_const]
  refine setLIntegral_mono' hG fun z hz ↦ ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (κ z) _)]
  exact ENNReal.ofReal_le_ofReal (hδ z hz)

/-- If the conditional law of `W` given `Z` is `κ` and, for every `z` in the measurable set `G`,
the section of the measurable set `G'` at `z` has `κ z`-probability at least `1 - δ`, then
`P((Z, W) ∈ G') ≥ P(Z ∈ G) - δ`. -/
lemma HasCondDistrib.measureReal_sub_le [IsProbabilityMeasure P] [IsMarkovKernel κ]
    (h : HasCondDistrib W Z κ P) (hG : MeasurableSet G) (hG' : MeasurableSet G') (hδ0 : 0 ≤ δ)
    (hδ : ∀ z ∈ G, 1 - δ ≤ (κ z).real (Prod.mk z ⁻¹' G')) :
    P.real (Z ⁻¹' G) - δ ≤ P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := by
  have h1 := h.measureReal_le_mul hG hG'.compl hδ0 fun z hz ↦ by
    rw [Set.preimage_compl, measureReal_compl (measurable_prodMk_left hG'), probReal_univ]
    linarith [hδ z hz]
  have h2 : P.real (Z ⁻¹' G) ≤ P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') +
      P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G'ᶜ) := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro ω hω
    by_cases hω' : (Z ω, W ω) ∈ G' <;> simp [hω]
  have h3 : P.real (Z ⁻¹' G ∩ (fun ω ↦ (Z ω, W ω)) ⁻¹' G') ≤
      P.real ((fun ω ↦ (Z ω, W ω)) ⁻¹' G') := measureReal_mono Set.inter_subset_right
  have h4 : δ * P.real (Z ⁻¹' G) ≤ δ := by
    calc δ * P.real (Z ⁻¹' G) ≤ δ * 1 := by gcongr; exact measureReal_le_one
      _ = δ := mul_one δ
  linarith

end bound

end ProbabilityTheory
