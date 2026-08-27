/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Top-`m` selection of a finite set by a score

For a finite set `S` in a linear order, a score `v : α → β` into a linear order and `m : ℕ`,
`S.topBy v m` is the set of the `m` elements of `S` with the largest scores, ties being broken in
favour of the smaller elements. It is obtained by sorting `S` by decreasing key
`topKey v a = toLex (v a, toDual a)` and keeping the first `m` elements.

The main result is the "median argument" `Finset.exists_mem_topBy_of_card_filter_lt`
(blueprint `lem:pm_selection`): if fewer than `m` elements have a low true score but an empirical
score at least that of a reference element, then some selected element has a high true score.
-/

@[expose] public section

namespace Finset

variable {α β : Type*}

/-- The key used to rank elements: first by score, then by the reverse of the ambient order, so
that among elements with equal scores the smaller ones have the larger keys. -/
def topKey (v : α → β) (a : α) : Lex (β × αᵒᵈ) := toLex (v a, OrderDual.toDual a)

lemma topKey_injective (v : α → β) : Function.Injective (topKey v) := by
  intro a b h
  exact (by simpa [topKey] using h : v a = v b ∧ a = b).2

variable [LinearOrder α] [LinearOrder β] {S : Finset α} {v : α → β} {m : ℕ} {a b : α}

lemma topKey_le_topKey : topKey v a ≤ topKey v b ↔ v a < v b ∨ (v a = v b ∧ b ≤ a) := by
  simp [topKey, Prod.Lex.toLex_le_toLex]

lemma topKey_lt_topKey : topKey v a < topKey v b ↔ v a < v b ∨ (v a = v b ∧ b < a) := by
  simp [topKey, Prod.Lex.toLex_lt_toLex]

lemma apply_le_of_topKey_le (h : topKey v a ≤ topKey v b) : v a ≤ v b := by
  rcases topKey_le_topKey.1 h with h | h
  · exact h.le
  · exact h.1.le

/-- The preference relation used to sort a set: `a` is preferred over `b` if its key is at least
that of `b`. -/
def TopByRel (v : α → β) (a b : α) : Prop := topKey v b ≤ topKey v a

instance (v : α → β) : DecidableRel (TopByRel v) := fun _ _ ↦ inferInstanceAs (Decidable (_ ≤ _))

instance (v : α → β) : IsTrans α (TopByRel v) := ⟨fun _ _ _ h₁ h₂ ↦ h₂.trans h₁⟩

instance (v : α → β) : Std.Antisymm (TopByRel v) :=
  ⟨fun _ _ h₁ h₂ ↦ topKey_injective v (h₂.antisymm h₁)⟩

instance (v : α → β) : Std.Total (TopByRel v) := ⟨fun _ _ ↦ le_total _ _⟩

/-- The `m` elements of `S` with the largest scores `v`, ties broken in favour of smaller
elements (if `S.card < m`, this is `S`). -/
def topBy (S : Finset α) (v : α → β) (m : ℕ) : Finset α :=
  ((S.sort (TopByRel v)).take m).toFinset

lemma mem_topBy_iff : a ∈ S.topBy v m ↔ a ∈ (S.sort (TopByRel v)).take m := List.mem_toFinset

lemma topBy_subset : S.topBy v m ⊆ S := fun _ ha ↦
  (mem_sort _).1 (List.mem_of_mem_take (mem_topBy_iff.1 ha))

lemma card_topBy (hm : m ≤ S.card) : (S.topBy v m).card = m := by
  rw [topBy, List.toFinset_card_of_nodup ((sort_nodup _ _).sublist (List.take_sublist _ _)),
    List.length_take, length_sort, min_eq_left hm]

lemma card_topBy_le : (S.topBy v m).card ≤ m :=
  (List.toFinset_card_le _).trans (List.length_take_le _ _)

lemma topBy_eq_self_of_card_le (h : S.card ≤ m) : S.topBy v m = S := by
  rw [topBy, List.take_of_length_le (by rwa [length_sort]), sort_toFinset]

/-- An element left out has a key at most the key of every selected element. -/
lemma topKey_le_of_notMem_topBy (ha : a ∈ S) (ha' : a ∉ S.topBy v m) (hb : b ∈ S.topBy v m) :
    topKey v a ≤ topKey v b := by
  rw [mem_topBy_iff] at ha' hb
  have ha'' : a ∈ (S.sort (TopByRel v)).drop m := by
    have h := (mem_sort (TopByRel v)).2 ha
    rw [← List.take_append_drop m (S.sort (TopByRel v)), List.mem_append] at h
    exact h.resolve_left ha'
  have h := pairwise_sort S (TopByRel v)
  rw [← List.take_append_drop m (S.sort (TopByRel v)), List.pairwise_append] at h
  exact h.2.2 b hb a ha''

/-- An element left out has a score at most the score of every selected element. -/
lemma apply_le_of_notMem_topBy (ha : a ∈ S) (ha' : a ∉ S.topBy v m) (hb : b ∈ S.topBy v m) :
    v a ≤ v b :=
  apply_le_of_topKey_le (topKey_le_of_notMem_topBy ha ha' hb)

/-- `a` is selected iff it is in `S` and fewer than `m` elements of `S` beat it. -/
lemma mem_topBy_iff_card_filter_lt :
    a ∈ S.topBy v m ↔ a ∈ S ∧ (S.filter fun b ↦ topKey v a < topKey v b).card < m := by
  constructor
  · intro ha
    refine ⟨topBy_subset ha, ?_⟩
    have hT : (S.filter fun b ↦ topKey v a < topKey v b) ⊆ S.topBy v m := by
      intro b hb
      rw [mem_filter] at hb
      by_contra hb'
      exact hb.2.not_ge (topKey_le_of_notMem_topBy hb.1 hb' ha)
    exact (card_lt_card ((ssubset_iff_of_subset hT).2 ⟨a, ha, by simp⟩)).trans_le card_topBy_le
  · rintro ⟨ha, hT⟩
    by_contra ha'
    rcases le_or_gt m S.card with hm | hm
    · have hsub : S.topBy v m ⊆ S.filter fun b ↦ topKey v a < topKey v b := by
        intro b hb
        refine mem_filter.2 ⟨topBy_subset hb, ?_⟩
        refine lt_of_le_of_ne (topKey_le_of_notMem_topBy ha ha' hb) fun h ↦ ha' ?_
        rw [topKey_injective v h]
        exact hb
      exact hT.not_ge ((card_topBy hm).symm.trans_le (card_le_card hsub))
    · rw [topBy_eq_self_of_card_le hm.le] at ha'
      exact ha' ha

/-- The top-`m` selection is a measurable function of the scores. -/
lemma measurable_topBy {ι : Type*} [MeasurableSpace ι] [TopologicalSpace β] [OrderClosedTopology β]
    [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (S : Finset α) (m : ℕ) {v : ι → α → β} (hv : ∀ a, Measurable fun x ↦ v x a) :
    Measurable fun x ↦ S.topBy (v x) m := by
  rw [measurable_finset_iff]
  intro a
  simp_rw [mem_topBy_iff_card_filter_lt, card_filter]
  have hlt (b : α) : Measurable fun x ↦ topKey (v x) a < topKey (v x) b := by
    simp_rw [topKey_lt_topKey]
    have h : ∀ x, (v x a = v x b) = ¬ (v x a < v x b ∨ v x b < v x a) := fun x ↦ by
      rw [lt_or_lt_iff_ne, not_not]
    simp_rw [h]
    have hab := (hv a).lt (hv b)
    exact hab.or ((hab.or ((hv b).lt (hv a))).not.and measurable_const)
  refine measurable_const.and ?_
  refine (Finset.measurable_sum S fun b _ ↦ ?_).lt measurable_const
  exact Measurable.ite (measurableSet_setOfPred.2 (hlt b)) measurable_const measurable_const

/-- **The median argument** (blueprint `lem:pm_selection`): if fewer than `m` elements are "bad"
(true score `μ` below `c` but empirical score `v` at least that of the reference element `a₀`),
then some selected element has true score at least `c`. -/
lemma exists_mem_topBy_of_card_filter_lt {γ : Type*} [LinearOrder γ] {μ : α → γ} {c : γ} {a₀ : α}
    (ha₀ : a₀ ∈ S) (hc : c ≤ μ a₀) (hm : m ≤ S.card)
    (hB : (S.filter fun a ↦ μ a < c ∧ v a₀ ≤ v a).card < m) :
    ∃ b ∈ S.topBy v m, c ≤ μ b := by
  by_cases h₀ : a₀ ∈ S.topBy v m
  · exact ⟨a₀, h₀, hc⟩
  rw [← card_topBy (v := v) hm] at hB
  obtain ⟨b, hb, hb'⟩ := exists_mem_notMem_of_card_lt_card hB
  refine ⟨b, hb, ?_⟩
  by_contra hlt
  exact hb' (mem_filter.2 ⟨topBy_subset hb, not_le.1 hlt, apply_le_of_notMem_topBy ha₀ h₀ hb⟩)

end Finset
