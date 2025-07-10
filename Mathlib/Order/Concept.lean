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

variable {ι : Sort*} {α β : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Polars -/


/-- The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

/-- The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

variable {a b r}

@[simp] theorem mem_upperPolar_iff : b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b := Iff.rfl
@[simp] theorem mem_lowerPolar_iff : a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b := Iff.rfl

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

theorem upperPolar_anti : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l

theorem lowerPolar_anti : Antitone (lowerPolar r) := monotone_comp_ofDual_iff.mp <|
  (gc_upperPolar_lowerPolar r).monotone_u

theorem upperBounds_eq_upperPolar [LE α] : upperBounds s = upperPolar (· ≤ ·) s := rfl
theorem lowerBounds_eq_lowerPolar [LE β] : lowerBounds t = lowerPolar (· ≤ ·) t := rfl

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

theorem intent_eq_iff_extent_eq : c.intent = d.intent ↔ c.extent = d.extent := by
  simp [← lowerPolar_intent]
  simp_rw [Set.ext_iff]

@[ext]
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, h₁, _⟩ := c
  obtain ⟨s₂, t₂, h₂, _⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl

theorem ext' (h : c.intent = d.intent) : c = d := by
  obtain ⟨s₁, t₁, _, h₁⟩ := c
  obtain ⟨s₂, t₂, _, h₂⟩ := d
  dsimp at h₁ h₂ h
  substs h h₁ h₂
  rfl

theorem extent_injective : Injective fun c : Concept α β r => c.extent := fun _ _ => ext

theorem intent_injective : Injective fun c : Concept α β r => c.intent := fun _ _ => ext'

instance instSupConcept : Max (Concept α β r) :=
  ⟨fun c d =>
    { extent := lowerPolar r (c.intent ∩ d.intent)
      intent := c.intent ∩ d.intent
      upperPolar_extent := by
        rw [← c.upperPolar_extent, ← d.upperPolar_extent, ← upperPolar_union,
          upperPolar_lowerPolar_upperPolar]
      lowerPolar_intent := rfl }⟩

instance instInfConcept : Min (Concept α β r) :=
  ⟨fun c d =>
    { extent := c.extent ∩ d.extent
      intent := upperPolar r (c.extent ∩ d.extent)
      upperPolar_extent := rfl
      lowerPolar_intent := by
        rw [← c.lowerPolar_intent, ← d.lowerPolar_intent, ← lowerPolar_union,
          lowerPolar_upperPolar_lowerPolar] }⟩

instance instSemilatticeInfConcept : SemilatticeInf (Concept α β r) :=
  (extent_injective.semilatticeInf _) fun _ _ => rfl

@[simp]
theorem extent_subset_extent_iff : c.extent ⊆ d.extent ↔ c ≤ d :=
  Iff.rfl

@[simp]
theorem extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d :=
  Iff.rfl

@[simp]
theorem intent_subset_intent_iff : c.intent ⊆ d.intent ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]
theorem intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_ge,
    intent_subset_intent_iff, intent_subset_intent_iff]

theorem strictMono_extent : StrictMono (extent : Concept α β r → Set α) := fun _ _ =>
  extent_ssubset_extent_iff.2

theorem strictAnti_intent : StrictAnti (intent : Concept α β r → Set β) := fun _ _ =>
  intent_ssubset_intent_iff.2

instance instLatticeConcept : Lattice (Concept α β r) :=
  { Concept.instSemilatticeInfConcept with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ => intent_subset_intent_iff.1 inter_subset_left
    le_sup_right := fun _ _ => intent_subset_intent_iff.1 inter_subset_right
    sup_le := fun c d e => by
      simp_rw [← intent_subset_intent_iff]
      exact subset_inter }

instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ⟨univ, upperPolar r univ, rfl, eq_univ_of_forall fun _ _ hb => hb trivial⟩
  le_top _ := subset_univ _
  bot := ⟨lowerPolar r univ, univ, eq_univ_of_forall fun _ _ ha => ha trivial, rfl⟩
  bot_le _ := intent_subset_intent_iff.1 <| subset_univ _

instance : SupSet (Concept α β r) :=
  ⟨fun S =>
    { extent := lowerPolar r (⋂ c ∈ S, (c : Concept _ _ _).intent)
      intent := ⋂ c ∈ S, (c : Concept _ _ _).intent
      upperPolar_extent := by
        simp_rw [← upperPolar_extent, ← upperPolar_iUnion₂,
          upperPolar_lowerPolar_upperPolar]
      lowerPolar_intent := rfl }⟩

instance : InfSet (Concept α β r) :=
  ⟨fun S =>
    { extent := ⋂ c ∈ S, (c : Concept _ _ _).extent
      intent := upperPolar r (⋂ c ∈ S, (c : Concept _ _ _).extent)
      upperPolar_extent := rfl
      lowerPolar_intent := by
        simp_rw [← lowerPolar_intent, ← lowerPolar_iUnion₂,
          lowerPolar_upperPolar_lowerPolar] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.instLatticeConcept,
    Concept.instBoundedOrderConcept with
    sup := Concept.instSupConcept.max
    le_sSup := fun _ _ hc => intent_subset_intent_iff.1 <| biInter_subset_of_mem hc
    sSup_le := fun _ _ hc =>
      intent_subset_intent_iff.1 <| subset_iInter₂ fun d hd => intent_subset_intent_iff.2 <| hc d hd
    inf := Concept.instInfConcept.min
    sInf_le := fun _ _ => biInter_subset_of_mem
    le_sInf := fun _ _ => subset_iInter₂ }

@[simp]
theorem top_extent : (⊤ : Concept α β r).extent = univ :=
  rfl

@[simp]
theorem top_intent : (⊤ : Concept α β r).intent = upperPolar r univ :=
  rfl

@[simp]
theorem bot_extent : (⊥ : Concept α β r).extent = lowerPolar r univ :=
  rfl

@[simp]
theorem bot_intent : (⊥ : Concept α β r).intent = univ :=
  rfl

@[simp]
theorem sup_extent (c d : Concept α β r) : (c ⊔ d).extent = lowerPolar r (c.intent ∩ d.intent) :=
  rfl

@[simp]
theorem sup_intent (c d : Concept α β r) : (c ⊔ d).intent = c.intent ∩ d.intent :=
  rfl

@[simp]
theorem inf_extent (c d : Concept α β r) : (c ⊓ d).extent = c.extent ∩ d.extent :=
  rfl

@[simp]
theorem inf_intent (c d : Concept α β r) : (c ⊓ d).intent = upperPolar r (c.extent ∩ d.extent) :=
  rfl

@[simp]
theorem sSup_extent (S : Set (Concept α β r)) :
    (sSup S).extent = lowerPolar r (⋂ c ∈ S, (c : Concept _ _ _).intent) :=
  rfl

@[simp]
theorem sSup_intent (S : Set (Concept α β r)) :
    (sSup S).intent = ⋂ c ∈ S, (c : Concept _ _ _).intent := rfl

@[simp]
theorem sInf_extent (S : Set (Concept α β r)) :
    (sInf S).extent = ⋂ c ∈ S, (c : Concept _ _ _).extent := rfl

@[simp]
theorem sInf_intent (S : Set (Concept α β r)) :
    (sInf S).intent = upperPolar r (⋂ c ∈ S, (c : Concept _ _ _).extent) :=
  rfl

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  intent_subset_intent_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  intent_ssubset_intent_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
