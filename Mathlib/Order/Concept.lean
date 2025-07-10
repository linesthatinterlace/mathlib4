/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Lattice

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## TODO

Prove the fundamental theorem of concept lattices.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]

## Tags

concept, formal concept analysis, intent, extend, attribute
-/


open Function OrderDual Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Polars -/

/-- The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

/-- The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

variable {r} {a : α} {b : β}

theorem mem_upperPolar_iff {b} : b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b := Iff.rfl
theorem mem_lowerPolar_iff {a} : a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b := Iff.rfl

theorem subset_upperPolar_iff_subset_lowerPolar :
    t ⊆ upperPolar r s ↔ s ⊆ lowerPolar r t := forall₂_swap

variable (r)

theorem gc_upperPolar_lowerPolar :
    GaloisConnection (toDual ∘ upperPolar r) (lowerPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

theorem gc_lowerPolar_upperPolar :
    GaloisConnection (toDual ∘ lowerPolar r) (upperPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

theorem upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t :=
  rfl

theorem lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s :=
  rfl

@[simp]
theorem upperPolar_empty : upperPolar r ∅ = univ := (gc_upperPolar_lowerPolar r).l_bot

@[simp]
theorem lowerPolar_empty : lowerPolar r ∅ = univ := (gc_upperPolar_lowerPolar r).u_top

theorem rel_iff_mem_upperPolar_singleton : r a b ↔ b ∈ upperPolar r {a} := by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

theorem rel_iff_mem_lowerPolar_singleton : r a b ↔ a ∈ lowerPolar r {b} := by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

theorem lowerPolar_upperPolar_univ : lowerPolar r (upperPolar r univ) = univ :=
  (gc_upperPolar_lowerPolar r).u_l_top

theorem upperPolar_lowerPolar_univ : upperPolar r (lowerPolar r univ) = univ :=
  (gc_upperPolar_lowerPolar r).l_u_bot

@[simp]
theorem upperPolar_union (s₁ s₂ : Set α) :
    upperPolar r (s₁ ∪ s₂) = upperPolar r s₁ ∩ upperPolar r s₂ :=
  (gc_upperPolar_lowerPolar r).l_sup

@[simp]
theorem lowerPolar_union (t₁ t₂ : Set β) :
    lowerPolar r (t₁ ∪ t₂) = lowerPolar r t₁ ∩ lowerPolar r t₂ :=
  (gc_upperPolar_lowerPolar r).u_inf

@[simp]
theorem upperPolar_iUnion (f : ι → Set α) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).l_iSup

@[simp]
theorem lowerPolar_iUnion (f : ι → Set β) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).u_iInf

theorem upperPolar_iUnion₂ (f : ∀ i, κ i → Set α) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).l_iSup₂

theorem lowerPolar_iUnion₂ (f : ∀ i, κ i → Set β) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).u_iInf₂

theorem lowerPolar_biUnion (S : Set γ) (f : γ → Set β) :
    lowerPolar r (⋃ i ∈ S, f i) = ⋂ i ∈ S, lowerPolar r (f i) := by
  simp_rw [lowerPolar_iUnion]

theorem upperPolar_biUnion (S : Set γ) (f : γ → Set α) :
    upperPolar r (⋃ i ∈ S, f i) = ⋂ i ∈ S, upperPolar r (f i) := by
  simp_rw [upperPolar_iUnion]

theorem subset_lowerPolar_upperPolar (s : Set α) :
    s ⊆ lowerPolar r (upperPolar r s) :=
  (gc_upperPolar_lowerPolar r).le_u_l _

theorem subset_upperPolar_lowerPolar (t : Set β) :
    t ⊆ upperPolar r (lowerPolar r t) :=
  (gc_upperPolar_lowerPolar r).l_u_le _

@[simp]
theorem upperPolar_lowerPolar_upperPolar (s : Set α) :
    upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s :=
  (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]
theorem lowerPolar_upperPolar_lowerPolar (t : Set β) :
    lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t :=
  (gc_upperPolar_lowerPolar r).u_l_u_eq_u _

theorem upperPolar_antitone : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l

theorem upperPolar_anti {s'} (h : s ⊆ s') : upperPolar r s' ⊆ upperPolar r s :=
  upperPolar_antitone r h

theorem lowerPolar_antitone : Antitone (lowerPolar r) := monotone_comp_ofDual_iff.mp <|
  (gc_upperPolar_lowerPolar r).monotone_u

theorem lowerPolar_anti {t'} (h : t ⊆ t') : lowerPolar r t' ⊆ lowerPolar r t :=
  lowerPolar_antitone r h

theorem lowerPolar_comp_upperPolar_monotone : Monotone ((lowerPolar r) ∘ (upperPolar r)) :=
  (lowerPolar_antitone r).comp (upperPolar_antitone r)

theorem upperPolar_comp_lowerPolar_monotone : Monotone ((upperPolar r) ∘ (lowerPolar r)) :=
  (upperPolar_antitone r).comp (lowerPolar_antitone r)

theorem lowerPolar_upperPolar_mono {s'} (h : s ⊆ s') :
    lowerPolar r (upperPolar r s) ⊆ lowerPolar r (upperPolar r s') :=
  lowerPolar_comp_upperPolar_monotone r h

theorem upperPolar_lowerPolar_mono {t'} (h : t ⊆ t') :
    upperPolar r (lowerPolar r t) ⊆ upperPolar r (lowerPolar r t') :=
  upperPolar_comp_lowerPolar_monotone r h

theorem upperBounds_eq_upperPolar [LE α] : upperBounds s = upperPolar (· ≤ ·) s := rfl
theorem lowerBounds_eq_lowerPolar [LE β] : lowerBounds t = lowerPolar (· ≤ ·) t := rfl

/-! ### `IsIntent` and `IsExtent` -/

namespace Set

variable {r}

def IsExtent (r : α → β → Prop) (s : Set α) := lowerPolar r (upperPolar r s) = s

@[simp] theorem isExtent_iff : IsExtent r s ↔ ∃ t, lowerPolar r t = s :=
  ⟨fun h => ⟨upperPolar r s, h⟩, fun ⟨t, h⟩ => h ▸ lowerPolar_upperPolar_lowerPolar r t⟩

theorem IsExtent.exists_lowerPolar (hs : IsExtent r s) : ∃ t, lowerPolar r t = s :=
    isExtent_iff.mp hs

theorem isExtent_lowerPolar (t : Set β) :
    IsExtent r (lowerPolar r t) := isExtent_iff.mpr ⟨_, rfl⟩

theorem isExtent_univ : IsExtent r univ := lowerPolar_upperPolar_univ r

theorem IsExtent.inter {s' : Set α} : s.IsExtent r → s'.IsExtent r → (s ∩ s').IsExtent r := by
  simp only [isExtent_iff, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨t ∪ t', lowerPolar_union r t t'⟩

theorem isExtent_iInter (f : ι → Set α) (hf : ∀ i, (f i).IsExtent r) : (⋂ i, f i).IsExtent r := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion r (fun i => upperPolar r (f i))).trans (Set.iInter_congr hf)⟩

theorem isExtent_biInter (S : Set γ) (f : γ → Set α) (hf : ∀ i ∈ S, (f i).IsExtent r) :
    (⋂ i ∈ S, f i).IsExtent r := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_biUnion r S (fun i => upperPolar r (f i))).trans <|
    Set.iInter_congr (fun _ => Set.iInter_congr (hf _))⟩

theorem isExtent_iInter₂ (f : ∀ i, κ i → Set α) (hf : ∀ i j, (f i j).IsExtent r) :
    (⋂ (i) (j), f i j).IsExtent r := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion₂ r (fun i j => upperPolar r (f i j))).trans (Set.iInter₂_congr hf)⟩

def IsIntent (r : α → β → Prop) (t : Set β) := upperPolar r (lowerPolar r t) = t

@[simp] theorem isIntent_iff : IsIntent r t ↔ ∃ s, upperPolar r s = t :=
  ⟨fun h => ⟨lowerPolar r t, h⟩, fun ⟨s, h⟩ => h ▸ upperPolar_lowerPolar_upperPolar r s⟩

theorem IsIntent.exists_upperPolar (hs : IsIntent r t) : ∃ s, upperPolar r s = t :=
    isIntent_iff.mp hs

theorem isIntent_upperPolar (s : Set α) :
    IsIntent r (upperPolar r s) := isIntent_iff.mpr ⟨_, rfl⟩

theorem isIntent_univ : IsIntent r univ := upperPolar_lowerPolar_univ r

theorem IsIntent.inter {t' : Set β} : t.IsIntent r → t'.IsIntent r → (t ∩ t').IsIntent r := by
  simp only [isIntent_iff, forall_exists_index]
  rintro s rfl s' rfl
  exact ⟨s ∪ s', upperPolar_union r s s'⟩

theorem isIntent_iInter (f : ι → Set β) (hf : ∀ i, (f i).IsIntent r) : (⋂ i, f i).IsIntent r := by
  rw [isIntent_iff]
  exact ⟨_, (upperPolar_iUnion r (fun i => lowerPolar r (f i))).trans (Set.iInter_congr hf)⟩

theorem isIntent_iInter₂ (f : ∀ i, κ i → Set β) (hf : ∀ i j, (f i j).IsIntent r) :
    (⋂ (i) (j), f i j).IsIntent r := by
  rw [isIntent_iff]
  exact ⟨_, (upperPolar_iUnion₂ r (fun i j => lowerPolar r (f i j))).trans (Set.iInter₂_congr hf)⟩

theorem isIntent_biInter (S : Set γ) (f : γ → Set β) (hf : ∀ i ∈ S, (f i).IsIntent r) :
    (⋂ i ∈ S, f i).IsIntent r := by
  rw [isIntent_iff]
  exact ⟨_, (upperPolar_biUnion r S (fun i => lowerPolar r (f i))).trans <|
    Set.iInter_congr (fun _ => Set.iInter_congr (hf _))⟩

end Set

/-! ### Concepts -/


variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept where
  extent : Set α
  intent : Set β
  /-- The axiom of a `Concept` stating that the closure of the first set is the second set. -/
  upperPolar_extent : upperPolar r extent = intent
  /-- The axiom of a `Concept` stating that the closure of the second set is the first set. -/
  lowerPolar_intent : lowerPolar r intent = extent

namespace Concept

variable {r α β}
variable {c d : Concept α β r}

attribute [simp] upperPolar_extent lowerPolar_intent

theorem extent_inj : c.extent = d.extent ↔ c = d := by
  obtain ⟨_, _, h₁, _⟩ := c
  obtain ⟨_, _, h₂, _⟩ := d
  substs h₁ h₂
  rw [mk.injEq, iff_self_and]
  exact (congrArg (upperPolar r) ·)

theorem intent_inj : c.intent = d.intent ↔ c = d := by
  obtain ⟨_, _, _, h₁⟩ := c
  obtain ⟨_, _, _, h₂⟩ := d
  substs h₁ h₂
  rw [mk.injEq, iff_and_self]
  exact (congrArg (lowerPolar r) ·)

theorem extent_injective : Injective (extent (r := r)) := fun _ _ => extent_inj.mp

theorem intent_injective : Injective (intent (r := r)) := fun _ _ => intent_inj.mp

@[simps!]
def _root_.Set.IsExtent.concept (hs : s.IsExtent r) : Concept α β r := ⟨s, upperPolar r s, rfl, hs⟩

theorem _root_.Set.IsExtent.exists_concept (hs : s.IsExtent r) :
    ∃ (c : Concept α β r), c.extent = s := ⟨hs.concept, rfl⟩

theorem extent_isExtent (c : Concept α β r) : c.extent.IsExtent r :=
  lowerPolar_intent c ▸ isExtent_lowerPolar c.intent

theorem isExtent_iff_exists_concept : s.IsExtent r ↔ ∃ (c : Concept α β r), c.extent = s :=
  ⟨Set.IsExtent.exists_concept, fun ⟨c, h⟩ => h ▸ c.extent_isExtent⟩

@[simps!]
def _root_.Set.IsIntent.concept (ht : t.IsIntent r) : Concept α β r := ⟨lowerPolar r t, t, ht, rfl⟩

theorem _root_.Set.IsIntent.exists_concept (ht : t.IsIntent r) :
    ∃ (c : Concept α β r), c.intent = t := ⟨ht.concept, rfl⟩

theorem intent_isIntent (c : Concept α β r) : c.intent.IsIntent r :=
  upperPolar_extent c ▸ isIntent_upperPolar c.extent

theorem isIntent_iff_exists_concept : t.IsIntent r ↔ ∃ (c : Concept α β r), c.intent = t :=
  ⟨Set.IsIntent.exists_concept, fun ⟨c, h⟩ => h ▸ c.intent_isIntent⟩

@[simps!]
def ofObjects (r : α → β → Prop) (s : Set α) : Concept α β r :=
  (isIntent_upperPolar s).concept

theorem leftInverse_ofObjects_extent : LeftInverse (ofObjects r) extent :=
    fun c => intent_injective c.upperPolar_extent

theorem leftInvOn_extent_ofObjects : Set.LeftInvOn extent (ofObjects r) {s | s.IsExtent r} :=
  fun _  => id

theorem surjective_ofObjects : Surjective (ofObjects r) :=
  leftInverse_ofObjects_extent.surjective

@[simps!]
def ofAttributes (r : α → β → Prop) (t : Set β) : Concept α β r :=
  (isExtent_lowerPolar t).concept

theorem leftInverse_ofAttributes_extent : LeftInverse (ofAttributes r) intent :=
    fun c => extent_injective c.lowerPolar_intent

theorem leftInvOn_ofObjects_intent : Set.LeftInvOn intent (ofAttributes r) {s | s.IsIntent r} :=
  fun _  => id

theorem surjective_ofAttributes : Surjective (ofAttributes r) :=
  leftInverse_ofAttributes_extent.surjective

@[simps!]
def ofObject (r : α → β → Prop) (a : α) : Concept α β r := ofObjects r {a}

@[simps!]
def ofAttribute (r : α → β → Prop) (b : β) : Concept α β r := ofAttributes r {b}

theorem intent_subset_intent_iff_extent_subset_extent :
    c.intent ⊆ d.intent ↔ d.extent ⊆ c.extent := by
  constructor
  · rw [← lowerPolar_intent, ← lowerPolar_intent]
    apply lowerPolar_antitone
  · rw [← upperPolar_extent, ← upperPolar_extent]
    apply upperPolar_antitone

theorem intent_ssubset_intent_iff_extent_ssubset_extent :
    c.intent ⊂ d.intent ↔ d.extent ⊂ c.extent := by
  simp_rw [ssubset_iff_subset_not_subset, intent_subset_intent_iff_extent_subset_extent]

instance : PartialOrder (Concept α β r) := PartialOrder.lift extent extent_injective

theorem le_iff_extent_subset_extent : c ≤ d ↔ c.extent ⊆ d.extent := Iff.rfl

theorem lt_iff_extent_ssubset_extent : c < d ↔ c.extent ⊂ d.extent := Iff.rfl

theorem le_iff_intent_subset_intent : d ≤ c ↔ c.intent ⊆ d.intent:= by
  rw [intent_subset_intent_iff_extent_subset_extent, le_iff_extent_subset_extent]

theorem lt_iff_intent_ssubset_intent : d < c ↔ c.intent ⊂ d.intent := by
  rw [intent_ssubset_intent_iff_extent_ssubset_extent, lt_iff_extent_ssubset_extent]

theorem strictMono_extent : StrictMono (extent : Concept α β r → Set α) := fun _ _ =>
  lt_iff_extent_ssubset_extent.1

theorem strictAnti_intent : StrictAnti (intent : Concept α β r → Set β) := fun _ _ =>
  lt_iff_intent_ssubset_intent.1

theorem rel_iff_ofObject_le_ofAttribute {a b} : r a b ↔ ofObject r a ≤ ofAttribute r b := by
  simp_rw [le_iff_extent_subset_extent, ofObject_extent, ofAttribute_extent]
  constructor
  · rw [rel_iff_mem_upperPolar_singleton r, ← Set.singleton_subset_iff]
    exact lowerPolar_anti r
  · intro h
    rw [rel_iff_mem_lowerPolar_singleton r, ← Set.singleton_subset_iff]
    exact (subset_lowerPolar_upperPolar r {a}).trans h

@[simps!]
instance : Max (Concept α β r) :=
  ⟨fun c d => (c.intent_isIntent.inter d.intent_isIntent).concept⟩

@[simps!]
instance : Min (Concept α β r) :=
  ⟨fun c d => (c.extent_isExtent.inter d.extent_isExtent).concept⟩

instance : SemilatticeInf (Concept α β r) :=
  (extent_injective.semilatticeInf _) fun _ _ => min_extent _ _

instance : Lattice (Concept α β r) :=
  { Concept.instSemilatticeInf with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => by
      simp_rw [le_iff_intent_subset_intent, max_intent, inter_subset_left]
    le_sup_right := fun _ _ => by
      simp_rw [le_iff_intent_subset_intent, max_intent, inter_subset_right]
    sup_le := fun c d e => by
      simp_rw [le_iff_intent_subset_intent, max_intent, subset_inter_iff]
      exact And.intro }

@[simps!]
instance : BoundedOrder (Concept α β r) where
  top := isExtent_univ.concept
  le_top _ := by
    simp_rw [le_iff_extent_subset_extent, IsExtent.concept_extent, subset_univ]
  bot := isIntent_univ.concept
  bot_le _ := by
    simp_rw [le_iff_intent_subset_intent, IsIntent.concept_intent, subset_univ]

@[simps!]
instance : SupSet (Concept α β r) :=
    ⟨fun S => (isIntent_biInter S intent (fun c _ => c.intent_isIntent)).concept⟩

@[simps!]
instance : InfSet (Concept α β r) :=
    ⟨fun S => (isExtent_biInter S extent (fun c _ => c.extent_isExtent)).concept⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.instLattice,
    Concept.instBoundedOrder with
    sup := Concept.instMax.max
    le_sSup := fun S c hc => by
      simp_rw [le_iff_intent_subset_intent, sSup_intent]
      exact biInter_subset_of_mem hc
    sSup_le := fun S c => by
      simp_rw [le_iff_intent_subset_intent, sSup_intent, subset_iInter_iff, imp_self]
    inf := Concept.instMin.min
    sInf_le := fun S c hc => by
      simp_rw [le_iff_extent_subset_extent, sInf_extent]
      exact biInter_subset_of_mem hc
    le_sInf := fun _ _ => by
      simp_rw [le_iff_extent_subset_extent, sInf_extent, subset_iInter_iff, imp_self]}

instance : Inhabited (Concept α β r) := ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  extent_injective rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c := by
  simp_rw [le_iff_intent_subset_intent, swap_intent, intent_subset_intent_iff_extent_subset_extent]

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c := by
  simp_rw [lt_iff_intent_ssubset_intent, swap_intent,
  intent_ssubset_intent_iff_extent_ssubset_extent]

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
