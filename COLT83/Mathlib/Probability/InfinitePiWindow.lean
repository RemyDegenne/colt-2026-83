/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Finite windows of an i.i.d. sequence

* `Measure.infinitePi_map_eval_comp`: the joint law of finitely many distinct coordinates of an
  i.i.d. family is the finite product of the common law.
* `Measure.pi_prod_map_split`: a product of `d` copies of `μ ⊗ ν` splits as the product of the
  `d`-fold products of `μ` and of `ν`.
* `Measure.pi_sigma_map_curry`: currying a product indexed by a sigma type.
* `ProbabilityTheory.indepFun_prefix_window`: the first `T` coordinates of an i.i.d. sequence are
  independent of any finite family of coordinates of index `≥ T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The joint law of finitely many distinct coordinates of an i.i.d. family is the finite product
of the common law. -/
lemma infinitePi_map_eval_comp {J : Type*} [Fintype J] {f : J → ι} (hf : Function.Injective f) :
    (infinitePi fun _ : ι ↦ μ).map (fun ω (p : J) ↦ ω (f p)) = Measure.pi fun _ : J ↦ μ := by
  classical
  set I : Set ι := Set.range f with hI
  have : Fintype I := Set.fintypeRange f
  let e : J ≃ I := Equiv.ofInjective f hf
  have h1 : (infinitePi fun _ : ι ↦ μ).map I.domRestrict = infinitePi fun _ : I ↦ μ :=
    infinitePi_map_restrict' (μ := fun _ ↦ μ)
  rw [infinitePi_eq_pi (μ := fun _ : I ↦ μ)] at h1
  have h2 := (measurePreserving_piCongrLeft (μ := fun _ : I ↦ μ) e).symm.map_eq
  have h3 : (fun (ω : ι → X) (p : J) ↦ ω (f p))
      = (MeasurableEquiv.piCongrLeft (π := fun _ : I ↦ X) e).symm
        ∘ (I.domRestrict : (ι → X) → (I → X)) := by
    funext ω p
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, e, Set.domRestrict]
    rfl
  have hm : Measurable (I.domRestrict : (ι → X) → (I → X)) :=
    measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  rw [h3, ← Measure.map_map (MeasurableEquiv.measurable _) hm, h1, h2]

/-- A product of `J` copies of `μ ⊗ ν` is the product of the `J`-fold products of `μ` and `ν`. -/
lemma pi_prod_map_split {J : Type*} [Fintype J] {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : J ↦ μ.prod ν).map (fun v ↦ (fun p ↦ (v p).1, fun p ↦ (v p).2))
      = (Measure.pi fun _ : J ↦ μ).prod (Measure.pi fun _ : J ↦ ν) :=
  (measurePreserving_arrowProdEquivProdArrow X Y J (fun _ ↦ μ) (fun _ ↦ ν)).map_eq

/-- Currying a product indexed by a sigma type. -/
lemma pi_sigma_map_curry {K : Type*} [Fintype K] {s : K → Type*} [∀ k, Fintype (s k)] :
    (Measure.pi fun _ : (k : K) × s k ↦ μ).map Sigma.curry
      = Measure.pi fun k : K ↦ Measure.pi fun _ : s k ↦ μ := by
  have h := infinitePi_map_piCurry (κ := s) (X := fun (k : K) (_ : s k) ↦ X)
    (μ := fun (k : K) (_ : s k) ↦ μ)
  rw [MeasurableEquiv.coe_piCurry, infinitePi_eq_pi] at h
  rw [h]
  simp_rw [infinitePi_eq_pi]

/-- The coordinates of an i.i.d. sequence indexed by an injective family of indices form an
i.i.d. sequence with the same law (version for an arbitrary nonempty index type). -/
theorem infinitePi_map_eval_comp' {J : Type*} [Nonempty J] {f : J → ι} (hf : Function.Injective f) :
    (infinitePi fun _ : ι ↦ μ).map (fun ω (p : J) ↦ ω (f p)) = infinitePi fun _ : J ↦ μ := by
  have hm : Measurable fun ω : ι → X ↦ fun p : J ↦ ω (f p) :=
    measurable_pi_lambda _ fun p ↦ measurable_pi_apply _
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)]
  have hpre : (fun ω : ι → X ↦ fun p : J ↦ ω (f p)) ⁻¹' ((s : Set J).pi t)
      = ((s.map ⟨f, hf⟩ : Finset ι) : Set ι).pi fun i ↦ t (Function.invFun f i) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Function.Embedding.coeFn_mk,
      Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Function.leftInverse_invFun hf _]
  rw [hpre]
  refine (Measure.infinitePi_pi (μ := fun _ : ι ↦ μ) (s := s.map ⟨f, hf⟩)
    (t := fun i ↦ t (Function.invFun f i)) fun i _ ↦ ht _).trans ?_
  rw [Finset.prod_map]
  simp [Function.leftInverse_invFun hf _]

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The first `T` coordinates of an i.i.d. sequence are independent of any finite family of
coordinates of index at least `T`. -/
lemma indepFun_prefix_window {T : ℕ} {J : Type*} [Finite J] {f : J → ℕ} (hf : ∀ p, T ≤ f p) :
    IndepFun (fun ω (t : Fin T) ↦ ω t) (fun ω (p : J) ↦ ω (f p))
      (Measure.infinitePi fun _ : ℕ ↦ μ) := by
  classical
  have := Fintype.ofFinite J
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id) fun _ ↦ measurable_id
  have hdisj : Disjoint (Finset.range T) (Finset.univ.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx'
    exact absurd (Finset.mem_range.1 hx) (not_lt.2 (hf p))
  have h := hind.indepFun_finset (Finset.range T) (Finset.univ.image f) hdisj
    (fun i ↦ measurable_pi_apply i)
  exact h.comp (measurable_pi_lambda _ fun (t : Fin T) ↦
      measurable_pi_apply (⟨(t : ℕ), Finset.mem_range.2 t.2⟩ : Finset.range T))
    (measurable_pi_lambda _ fun p ↦
      measurable_pi_apply ⟨f p, Finset.mem_image_of_mem f (Finset.mem_univ p)⟩)

end ProbabilityTheory
