/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Wrenna Robson
-/

import Mathlib.Logic.Equiv.Defs

/-!
# TBD

TBD

## Tags

TBD

-/

variable {α β γ : Sort*}

namespace Equiv

@[irreducible] def IsCompat (e : α ≃ β) (p : α → Prop) (q : β → Prop) := ∀ a, p a ↔ q (e a)

section IsCompat

variable {p p' : α → Prop} {q : β → Prop} {r : γ → Prop}
  {e : α ≃ β} {f : β ≃ γ} (a : α) (b : β)

unseal IsCompat in
theorem isCompat_iff : e.IsCompat p q ↔ ∀ a, p a ↔ q (e a) := Iff.rfl

theorem IsCompat.forall_iff (he : e.IsCompat p q) : ∀ a, p a ↔ q (e a) := isCompat_iff.mp he

theorem isCompat_of_forall_iff (he : ∀ a, p a ↔ q (e a)) : e.IsCompat p q := isCompat_iff.mpr he

@[simp]
theorem isCompat_refl (p) : (Equiv.refl α).IsCompat p p :=
  isCompat_of_forall_iff (fun _ => Iff.rfl)

theorem isCompat_rfl : (Equiv.refl α).IsCompat p p := isCompat_refl p

@[grind]
theorem eq_of_refl_isCompat (h : (Equiv.refl _).IsCompat p p') : p = p' :=
  funext fun _ => propext <| by simp_rw [h.forall_iff, refl_apply]

@[grind]
theorem refl_isCompat_iff : (Equiv.refl _).IsCompat p p' ↔ p = p' :=
  ⟨eq_of_refl_isCompat, fun h => h ▸ isCompat_rfl⟩

@[simp]
theorem isCompat_comm : e.symm.IsCompat q p ↔ e.IsCompat p q := by
  simp_rw [isCompat_iff, e.forall_congr_left, apply_symm_apply, Iff.comm]

@[grind]
theorem IsCompat.symm (he : e.IsCompat p q) : e.symm.IsCompat q p := isCompat_comm.mpr he

@[grind]
theorem IsCompat.of_symm (he : e.symm.IsCompat q p) : e.IsCompat p q := isCompat_comm.mp he

@[grind]
theorem IsCompat.of_left_pos (he : e.IsCompat p q) (ha : p a) : q (e a) := (he.forall_iff _).mp ha

@[grind]
theorem IsCompat.of_right_apply_pos (he : e.IsCompat p q) (ha : q (e a)) : p a :=
  (he.forall_iff _).mpr ha

@[grind]
theorem IsCompat.of_right_pos (he : e.IsCompat p q) (hb : q b) : p (e.symm b) :=
  (he.symm.forall_iff _).mp hb

@[grind]
theorem IsCompat.of_left_apply_pos (he : e.IsCompat p q) (hb : p (e.symm b)) : q b :=
  (he.symm.forall_iff _).mpr hb

@[grind]
theorem IsCompat.trans (hpq : e.IsCompat p q) (hqr : f.IsCompat q r) :
    (e.trans f).IsCompat p r := by
  simp_rw [isCompat_iff, trans_apply, hpq.forall_iff, hqr.forall_iff, implies_true]

@[simp]
theorem isCompat_comp_left : e.IsCompat (q ∘ e) q := isCompat_of_forall_iff (fun _ => Iff.rfl)

@[simp]
theorem isCompat_comp_right : e.IsCompat p (p ∘ e.symm) := isCompat_comp_left.of_symm

theorem isCompat_compl_iff : e.IsCompat (¬ p ·) (¬ q ·) ↔ e.IsCompat p q := by
  simp_rw [isCompat_iff, not_iff_not]

theorem IsCompat.compl (he : e.IsCompat p q) : e.IsCompat (¬ p ·) (¬ q ·) :=
  isCompat_compl_iff.mpr he
theorem IsCompat.of_compl (he : e.IsCompat (¬ p ·) (¬ q ·)) : e.IsCompat p q :=
  isCompat_compl_iff.mp he
end IsCompat

@[irreducible] def MatchesOn {p : α → Prop} {q : β → Prop} (e : α ≃ β)
    (e₀ : { x // p x } ≃ { x // q x }) := ∀ a, (ha : p a) → e a = e₀ ⟨a, ha⟩

section MatchesOn

variable {p : α → Prop} {q : β → Prop} {r : γ → Prop} {e : α ≃ β} {f : β ≃ γ}
  {e₀ : { x // p x } ≃ { x // q x }} {f₀ : { x // q x } ≃ { x // r x }}
  {e₀' : { x // q x } ≃ { x // p x }} {a : α}

unseal MatchesOn in
theorem matchesOn_iff : e.MatchesOn e₀ ↔ ∀ a, (ha : p a) → e a = e₀ ⟨a, ha⟩ := Iff.rfl

theorem MatchesOn.forall_of_pos (he : e.MatchesOn e₀) : ∀ a, (ha : p a) → e a = e₀ ⟨a, ha⟩ :=
  matchesOn_iff.mp he

theorem matchesOn_of_forall_of_pos (he : ∀ a, (ha : p a) → e a = e₀ ⟨a, ha⟩) :
    e.MatchesOn e₀ := matchesOn_iff.mpr he

@[simp]
theorem matchesOn_symm_iff : e.symm.MatchesOn e₀.symm ↔ e.MatchesOn e₀ := by
  simp_rw [matchesOn_iff, symm_apply_eq, eq_comm (b := e _)]
  refine ⟨fun h a ha => ?_, fun h b hb => ?_⟩
  · simpa using h (e₀ ⟨a, ha⟩) (Subtype.prop _)
  · simpa using h (e₀.symm ⟨b, hb⟩) (Subtype.prop _)

theorem matchesOn_symm_left_iff : e.symm.MatchesOn e₀' ↔ e.MatchesOn e₀'.symm :=
  matchesOn_symm_iff (e₀ := e₀'.symm)

theorem matchesOn_symm_right_iff : e.MatchesOn e₀'.symm ↔ e.symm.MatchesOn e₀' :=
  matchesOn_symm_left_iff.symm

@[grind]
theorem MatchesOn.symm (he : e.MatchesOn e₀) : e.symm.MatchesOn e₀.symm := matchesOn_symm_iff.mpr he

@[grind]
theorem MatchesOn.of_symm (he : e.symm.MatchesOn e₀.symm) : e.MatchesOn e₀ :=
  matchesOn_symm_iff.mp he

@[simp]
theorem MatchesOn.isCompat (he : e.MatchesOn e₀) :
    e.IsCompat p q := isCompat_of_forall_iff fun a =>
  ⟨fun ha => he.forall_of_pos a ha ▸ Subtype.prop _,
    fun hb => e.symm_apply_apply a ▸ (he.symm.forall_of_pos (e a) hb) ▸ Subtype.prop _⟩

@[simp, grind]
theorem MatchesOn.of_pos (he : e.MatchesOn e₀) (ha : p a) : e a = e₀ ⟨a, ha⟩ :=
  he.forall_of_pos _ ha

@[grind]
theorem IsFixedOn.of_apply_pos (he : e.MatchesOn e₀) (ha : q (e a)) :
    e a = e₀ ⟨a, he.isCompat.of_right_apply_pos _ ha⟩ := he.forall_of_pos _ _

@[simp, grind]
theorem MatchesOn.trans (he : e.MatchesOn e₀) (hf : f.MatchesOn f₀) :
    (e.trans f).MatchesOn (e₀.trans f₀) := matchesOn_of_forall_of_pos <| fun a ha => by
  simp_rw [trans_apply, he.of_pos ha, hf.of_pos (Subtype.prop _)]

end MatchesOn

namespace Perm

@[irreducible] def IsCompat (e : Perm α) (p : α → Prop) := Equiv.IsCompat e p p

section IsCompat

variable {p : α → Prop} {e f : Perm α} {a : α}

unseal IsCompat in
theorem isCompat_iff : e.IsCompat p ↔ ∀ a, p a ↔ p (e a) := Equiv.isCompat_iff

theorem IsCompat.forall_iff (he : e.IsCompat p) : ∀ a, p a ↔ p (e a) := isCompat_iff.mp he

theorem isCompat_of_forall_iff (he : ∀ a, p a ↔ p (e a)) : e.IsCompat p := isCompat_iff.mpr he

@[grind]
theorem isCompat_iff_equiv_isCompat : e.IsCompat p ↔ Equiv.IsCompat e p p :=
  ⟨fun h => Equiv.isCompat_of_forall_iff h.forall_iff, fun h => isCompat_of_forall_iff h.forall_iff⟩

@[simp]
theorem isCompat_refl (p) : IsCompat (Equiv.refl α) p  :=
  isCompat_of_forall_iff (fun _ => Iff.rfl)

theorem isCompat_rfl : IsCompat (Equiv.refl α) p := isCompat_refl p

@[simp]
theorem isCompat_symm_iff : IsCompat e.symm p ↔ e.IsCompat p := by
  simp_rw [isCompat_iff_equiv_isCompat, Equiv.isCompat_comm]

@[grind]
theorem IsCompat.symm (he : e.IsCompat p) : IsCompat e.symm p := isCompat_symm_iff.mpr he

@[grind]
theorem IsCompat.of_symm (he : IsCompat e.symm p) : e.IsCompat p := isCompat_symm_iff.mp he

@[grind]
theorem IsCompat.of_pos (he : e.IsCompat p) (ha : p a) : p (e a) := (he.forall_iff _).mp ha

@[grind]
theorem IsCompat.of_apply_pos (he : e.IsCompat p) (ha : p (e a)) : p a :=
  (he.forall_iff _).mpr ha

@[simp, grind]
theorem IsCompat.trans (he : e.IsCompat p) (hf : f.IsCompat p) :
    IsCompat (e.trans f) p := by
  simp_rw [isCompat_iff_equiv_isCompat] at he hf ⊢
  exact he.trans hf

theorem isCompat_comp_left (p) : e.IsCompat (p ∘ e) ↔ e.IsCompat p :=
  ⟨fun h => isCompat_of_forall_iff (by simpa [Iff.comm] using h.symm.forall_iff),
  fun h => isCompat_of_forall_iff (fun _ => h.forall_iff _)⟩

theorem isCompat_comp_right (p) : e.IsCompat (p ∘ e.symm) ↔ e.IsCompat p := by
  simpa using  isCompat_comp_left (e := e.symm) p

theorem isCompat_compl_iff : e.IsCompat (¬ p ·) ↔ e.IsCompat p := by
  simp_rw [isCompat_iff, not_iff_not]

theorem IsCompat.compl (he : e.IsCompat p) : e.IsCompat (¬ p ·):= isCompat_compl_iff.mpr he
theorem IsCompat.of_compl (he : e.IsCompat (¬ p ·)) : e.IsCompat p := isCompat_compl_iff.mp he

end IsCompat

@[irreducible] def IsFixedOn (e : Perm α) (p : α → Prop) := ∀ a, p a → e a = a

section IsFixedOn

variable {p : α → Prop} {e f : Perm α} {a : α}

unseal IsFixedOn in
theorem isFixedOn_iff : e.IsFixedOn p ↔ ∀ a, p a → e a = a := Iff.rfl

theorem IsFixedOn.forall_of_pos (he : e.IsFixedOn p) : ∀ a, p a → e a = a := isFixedOn_iff.mp he

theorem isFixedOn_of_forall_of_pos (he : ∀ a, p a → e a = a) : e.IsFixedOn p := isFixedOn_iff.mpr he

@[simp]
theorem isFixedOn_refl (p) : IsFixedOn (Equiv.refl α) p  :=
  isFixedOn_of_forall_of_pos (fun _ _ => rfl)

theorem isFixedOn_rfl : IsFixedOn (Equiv.refl α) p := isFixedOn_refl p

@[simp]
theorem isFixedOn_symm_iff : IsFixedOn e.symm p ↔ e.IsFixedOn p := by
  simp_rw [isFixedOn_iff, symm_apply_eq, eq_comm]

@[grind]
theorem IsFixedOn.symm (he : e.IsFixedOn p) : IsFixedOn e.symm p := isFixedOn_symm_iff.mpr he

@[grind]
theorem IsFixedOn.of_symm (he : IsFixedOn e.symm p) : e.IsFixedOn p := isFixedOn_symm_iff.mp he

@[simp]
theorem IsFixedOn.isCompat (he : e.IsFixedOn p) :
    e.IsCompat p := isCompat_of_forall_iff fun _ =>
  ⟨(fun h => (he.forall_of_pos _ h).symm ▸ h), (fun h => e.injective (he.forall_of_pos _ h) ▸ h)⟩

@[simp, grind]
theorem IsFixedOn.of_pos (he : e.IsFixedOn p) (ha : p a) : e a = a := he.forall_of_pos _ ha

@[grind]
theorem IsFixedOn.of_apply_pos (he : e.IsFixedOn p) (ha : p (e a)) : e a = a :=
  he.forall_of_pos _ (he.isCompat.of_apply_pos ha)

@[simp, grind]
theorem IsFixedOn.trans (he : e.IsFixedOn p) (hf : f.IsFixedOn p) :
    IsFixedOn (e.trans f) p := isFixedOn_of_forall_of_pos <| fun _ ha =>
  (hf.of_apply_pos (hf.isCompat.of_pos (he.isCompat.of_pos ha))).trans
    (he.of_apply_pos (he.isCompat.of_pos ha))

theorem IsFixedOn.trans_comm {e f : Perm α}
    (he : e.IsFixedOn (¬ p ·)) (hf : f.IsFixedOn p) :
    e.trans f = f.trans e := Equiv.ext <| fun x => by
      by_cases hx : p x <;> simp only [trans_apply]
      · simp_rw [hf.of_pos hx, hf.of_pos (he.isCompat.of_compl.of_pos hx)]
      · simp_rw [he.of_pos hx, he.of_pos (hf.isCompat.compl.of_pos hx)]

theorem isFixedOn_comp_left (p) : e.IsFixedOn (p ∘ e) ↔ e.IsFixedOn p :=
  ⟨fun h => isFixedOn_of_forall_of_pos
    fun _ ha => h.forall_of_pos _ (((isCompat_comp_left p).mp h.isCompat).of_pos ha),
  fun h => isFixedOn_of_forall_of_pos fun _ ha => h.of_apply_pos ha⟩

theorem isFixedOn_comp_right (p) : e.IsFixedOn (p ∘ e.symm) ↔ e.IsFixedOn p := by
  simpa using isFixedOn_comp_left (e := e.symm) p

end IsFixedOn

end Perm

/-- Combines an `Equiv` between two subtypes with an `Equiv` between their complements to form a
  permutation. -/
def subtypeCongr {α β : Sort*} {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x }) : α ≃ β where
  toFun a := if h : p a then (e ⟨a, h⟩ : β) else f ⟨a, h⟩
  invFun b := if h : q b then (e.symm ⟨b, h⟩ : α) else f.symm ⟨b, h⟩
  left_inv a := if h : p a then ?_ else ?_
  right_inv b := if h : q b then ?_ else ?_
  where finally all_goals simp [h, Subtype.prop, Subtype.complProp]

section SubtypeCongr

variable {α β γ : Sort*} {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    [DecidablePred p] [DecidablePred q] [DecidablePred r]

variable (e : { x // p x } ≃ { x // q x }) (f : { x // ¬p x } ≃ { x // ¬q x })
  (e' : { x // q x } ≃ { x // r x }) (f' : { x // ¬q x } ≃ { x // ¬r x })

theorem subtypeCongr_apply (a : α) : e.subtypeCongr f a =
    if h : p a then (e ⟨a, h⟩ : β) else f ⟨a, h⟩ := rfl

@[simp]
theorem subtypeCongr_apply_of_pos {a : α} (h : p a) : e.subtypeCongr f a = e ⟨a, h⟩ := by
  simp only [subtypeCongr_apply, h, dite_true]

@[simp]
theorem subtypeCongr_apply_of_neg {a : α} (h : ¬ p a) : e.subtypeCongr f a = f ⟨a, h⟩ := by
  simp only [subtypeCongr_apply, h, dite_false]

@[simp]
theorem subtypeCongr_apply_subtype (a : { a // p a }) : e.subtypeCongr f a = e a :=
  subtypeCongr_apply_of_pos e f a.prop

@[simp]
theorem subtypeCongr_apply_subtype_compl (a : { a // ¬p a }) : e.subtypeCongr f a = f a :=
  subtypeCongr_apply_of_neg e f a.prop

@[simp]
theorem subtypeCongr_symm : (e.subtypeCongr f).symm = subtypeCongr e.symm f.symm := rfl

@[simp]
theorem subtypeCongr_refl :
    subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl α :=
  Equiv.ext (fun _ => ite_self _)

@[simp]
theorem subtypeCongr_trans :
    (e.subtypeCongr f).trans (e'.subtypeCongr f')
    = (e.trans e').subtypeCongr (f.trans f') := by
  ext a; by_cases h : p a <;> simp [h]

@[simp]
theorem subtypeCongr_inj {e e' : { x // p x } ≃ { x // q x }} {f f'} :
  e.subtypeCongr f = e'.subtypeCongr f' → e = e' ∧ f = f' := fun h =>
  ⟨Equiv.ext <| fun x => Subtype.ext <|
    e'.subtypeCongr_apply_of_pos f' x.prop ▸ e.subtypeCongr_apply_of_pos f x.prop ▸ h ▸ rfl,
  Equiv.ext <| fun x => Subtype.ext <|
    e'.subtypeCongr_apply_of_neg f' x.prop ▸ e.subtypeCongr_apply_of_neg f x.prop ▸ h ▸ rfl⟩

theorem subtypeCongr_inj_iff {e e' : { x // p x } ≃ { x // q x }} {f f'} :
    e.subtypeCongr f = e'.subtypeCongr f' ↔ e = e' ∧ f = f' :=
  ⟨subtypeCongr_inj, fun h => h.1 ▸ h.2 ▸ rfl⟩

theorem subtypeCongr_comm {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    {e e' : { x // ¬ p x } ≃ { x // ¬ q x }} {f f'} : subtypeCongr e f = subtypeCongr f' e' ↔
    e = e' ∧ ∀ (a : α) (ha : p a), (f ⟨a, not_not_intro ha⟩ : β) = f' ⟨a, ha⟩ := by
  simp_rw [Equiv.ext_iff, Subtype.ext_iff, Subtype.forall, subtypeCongr_apply,
    dite_not, dite_eq_iff', ← forall_and]
  exact ⟨fun h a => ⟨fun ha => ((h a).2 ha).trans (dif_neg ha),
    fun ha => ((h a).1 ha).trans (dif_pos ha)⟩, fun h a =>
    ⟨fun ha => dif_pos ha ▸ ((h _).2 _), fun ha => dif_neg ha ▸ ((h _).1 _)⟩⟩

theorem isCompat_subtypeCongr (e : { x // p x } ≃ { x // q x }) (f) :
    (e.subtypeCongr f).IsCompat p q :=
  isCompat_of_forall_iff <| fun _ => by
  simp_rw [subtypeCongr_apply, apply_dite q, Subtype.prop, Subtype.complProp, dite_eq_ite,
    ite_prop_iff_or, and_true, and_false, or_false]

end SubtypeCongr

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `Perm.subtypePerm`. -/
@[simps apply_coe]
def subtypeEquiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : e.IsCompat p q) :
    { a : α // p a } ≃ { b : β // q b } where
  toFun a := ⟨e a, h.of_left_pos a.val a.prop⟩
  invFun b := ⟨e.symm b, h.symm.of_left_pos b.val b.prop⟩
  left_inv a := Subtype.ext <| by simp
  right_inv b := Subtype.ext <| by simp

section SubtypeEquiv

variable {p : α → Prop} {q : β → Prop}

lemma coe_subtypeEquiv_eq_map (e : α ≃ β)
    (h : e.IsCompat p q) : ⇑(e.subtypeEquiv h) = Subtype.map e (h.forall_iff · |>.mp) :=
  rfl

@[simp]
theorem subtypeEquiv_refl :
    (Equiv.refl α).subtypeEquiv (isCompat_refl p) = Equiv.refl { a : α // p a } := rfl

@[simp]
theorem subtypeEquiv_symm (e : α ≃ β) (h : e.IsCompat p q) :
    (e.subtypeEquiv h).symm = e.symm.subtypeEquiv h.symm := rfl

@[simp]
theorem subtypeEquiv_trans {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
    (h : e.IsCompat p q) (h' : f.IsCompat q r) :
    (e.subtypeEquiv h).trans (f.subtypeEquiv h')
    = (e.trans f).subtypeEquiv (h.trans h') := rfl

@[simp]
theorem subtypeCongr_subtypeEquiv_subtypeEquivCompl {q : β → Prop}
    [DecidablePred p] [DecidablePred q] (e : α ≃ β) (h : e.IsCompat p q) :
    (e.subtypeEquiv h).subtypeCongr (e.subtypeEquiv h.compl) = e := Equiv.ext fun a => by
  by_cases h : p a <;> simp [h]

@[simp]
theorem subtypeEquiv_subtypeCongr {q : β → Prop}
    [DecidablePred p] [DecidablePred q] (e : { x // p x } ≃ { x // q x })
    (f : { x // ¬p x } ≃ { x // ¬q x }) :
    (e.subtypeCongr f).subtypeEquiv (e.isCompat_subtypeCongr f) = e :=
  Equiv.ext fun _ => Subtype.ext <| by simp

@[simp]
theorem subtypeEquivCompl_subtypeCongr {q : β → Prop}
    [DecidablePred p] [DecidablePred q] (e : { x // p x } ≃ { x // q x })
    (f : { x // ¬p x } ≃ { x // ¬q x }) :
    (e.subtypeCongr f).subtypeEquiv (e.isCompat_subtypeCongr f).compl = f :=
  Equiv.ext fun _ => Subtype.ext <| by simp

end SubtypeEquiv

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps!]
def subtypeEquivRight {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtypeEquiv (Equiv.refl _) (isCompat_of_forall_iff e)

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
@[simps!]
def subtypeEquivOfSubtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtypeEquiv e e.isCompat_comp_left

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
@[simps!]
def subtypeEquivOfSubtype' {p : α → Prop} (e : α ≃ β) :
    { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtypeEquivOfSubtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
@[simps!]
def subtypeEquivProp {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtypeEquiv (Equiv.refl α) (h ▸ isCompat_rfl)

@[simps!]
def subtypeNotNotEquiv {p : α → Prop} : Subtype (¬ ¬ p ·) ≃ Subtype p :=
  subtypeEquivProp (funext fun _ => propext <| not_not)

@[simps! apply symm_apply_coe]
def subtypeEquivProdEquiv {α β : Type*} (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] : {e : α ≃ β // e.IsCompat p q} ≃
    (({ a : α // p a } ≃ { b : β // q b }) ×
    ({ a : α // ¬ p a } ≃ { b : β // ¬ q b})) where
  toFun := fun e => ⟨subtypeEquiv e.1 e.2, subtypeEquiv e.1 e.2.compl⟩
  invFun := fun ef => ⟨ef.1.subtypeCongr ef.2, ef.1.isCompat_subtypeCongr ef.2⟩
  left_inv e := Subtype.ext <| subtypeCongr_subtypeEquiv_subtypeEquivCompl e.1 e.2
  right_inv ef := Prod.ext (subtypeEquiv_subtypeCongr ef.1 ef.2)
    (subtypeEquivCompl_subtypeCongr ef.1 ef.2)

protected def compl {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (e₀ : { x // p x } ≃ { x // q x }) :
    { e : α ≃ β // e.MatchesOn e₀} ≃ ({ x // ¬ p x } ≃ { x // ¬ q x }) where
  toFun e := subtypeEquiv e.1 e.2.isCompat.compl
  invFun e := ⟨subtypeCongr e₀ e, _⟩
  left_inv e := Subtype.ext <| by
    simp

  right_inv e := by simp only [subtypeEquivCompl_subtypeCongr]


namespace Perm

/-- Combining permutations on `α` that permute only inside or outside the subtype
split induced by `p : α → Prop` constructs a permutation on `α`. -/
def subtypeCongr {p : α → Prop} [DecidablePred p] (e : Perm (Subtype p))
    (f : Perm (Subtype (¬ p ·))) : Equiv.Perm α := Equiv.subtypeCongr e f

section SubtypeCongr

variable {p : α → Prop} [DecidablePred p] (e e' : Perm { a // p a }) (f f' : Perm { a // ¬p a })

theorem subtypeCongr_apply (a : α) : e.subtypeCongr f a =
    if h : p a then (e ⟨a, h⟩ : α) else f ⟨a, h⟩ := rfl

@[deprecated subtypeCongr_apply (since := "2025-07-22")]
theorem subtypeCongr.apply (a : α) : e.subtypeCongr f a =
    if h : p a then (e ⟨a, h⟩ : α) else f ⟨a, h⟩ := e.subtypeCongr_apply f a

@[simp]
theorem subtypeCongr_apply_of_pos {a : α} (h : p a) : e.subtypeCongr f a = e ⟨a, h⟩ := by
  simp only [subtypeCongr_apply, h, dite_true]

@[simp]
theorem subtypeCongr_apply_of_neg {a : α} (h : ¬ p a) : e.subtypeCongr f a = f ⟨a, h⟩ := by
  simp only [subtypeCongr_apply, h, dite_false]

@[simp]
theorem subtypeCongr_apply_subtype (a : { a // p a }) : e.subtypeCongr f a = e a :=
  subtypeCongr_apply_of_pos e f a.prop

@[simp]
theorem subtypeCongr_apply_subtype_compl (a : { a // ¬p a }) : e.subtypeCongr f a = f a :=
  subtypeCongr_apply_of_neg e f a.prop

theorem subtypeCongr_refl :
    subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl α :=
  Equiv.subtypeCongr_refl

theorem subtypeCongr_symm : (e.subtypeCongr f).symm = subtypeCongr e.symm f.symm :=
  Equiv.subtypeCongr_symm _ _

@[deprecated subtypeCongr_symm (since := "2025-07-22")]
alias subtypeCongr.symm := subtypeCongr_symm

theorem subtypeCongr_trans :
    (e.subtypeCongr f).trans (e'.subtypeCongr f')
    = subtypeCongr (e.trans e') (f.trans f') := Equiv.subtypeCongr_trans _ _ _ _

theorem subtypeCongr_inj {e e' : Perm { a // p a }} {f f'} :
  e.subtypeCongr f = e'.subtypeCongr f' → e = e' ∧ f = f' := Equiv.subtypeCongr_inj

theorem subtypeCongr_inj_iff {e e' : Perm { a // p a }} {f f'} :
    e.subtypeCongr f = e'.subtypeCongr f' ↔ e = e' ∧ f = f' := Equiv.subtypeCongr_inj_iff

theorem isCompat_subtypeCongr (e : Perm (Subtype p)) (f) :
    (e.subtypeCongr f).IsCompat p := by
  simp_rw [isCompat_iff_equiv_isCompat]
  exact Equiv.isCompat_subtypeCongr _ _

@[deprecated subtypeCongr_apply_of_pos (since := "2025-07-22")]
alias subtypeCongr.left_apply := subtypeCongr_apply_of_pos

@[deprecated subtypeCongr_apply_subtype (since := "2025-07-22")]
alias subtypeCongr.left_apply_subtype := subtypeCongr_apply_subtype

@[deprecated subtypeCongr_apply_of_neg (since := "2025-07-22")]
alias subtypeCongr.right_apply := subtypeCongr_apply_of_neg

@[deprecated subtypeCongr_apply_subtype_compl (since := "2025-07-22")]
alias subtypeCongr.right_apply_subtype := subtypeCongr_apply_subtype_compl

@[deprecated subtypeCongr_refl (since := "2025-07-22")]
alias subtypeCongr.refl := subtypeCongr_refl

@[deprecated subtypeCongr_trans (since := "2025-07-22")]
alias subtypeCongr.trans := subtypeCongr_trans

end SubtypeCongr

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def ofSubtype {p : α → Prop} [DecidablePred p] (f : Perm (Subtype p)) : Perm α :=
  f.subtypeCongr (Equiv.refl _)

section ofSubtype

variable {p : α → Prop} [DecidablePred p]

theorem ofSubtype_def (f : Perm (Subtype p)) :
    ofSubtype f = f.subtypeCongr (Equiv.refl _) := rfl

theorem ofSubtype_compl_def (f : Perm (Subtype (¬ p ·))) :
    ofSubtype f = subtypeCongr (Equiv.refl _) f := Equiv.ext <| fun _ => dite_not _ _

@[simp]
theorem ofSubtype_apply_of_pos (f : Perm (Subtype p)) {a : α} (ha : p a) :
    ofSubtype f a = f ⟨a, ha⟩ := f.subtypeCongr_apply_of_pos _ ha

@[simp]
theorem ofSubtype_apply_of_neg (f : Perm (Subtype p)) {a : α} (ha : ¬p a) :
    ofSubtype f a = a := f.subtypeCongr_apply_of_neg _ ha

@[simp]
theorem ofSubtype_apply_subtype (f : Perm (Subtype p)) (a : Subtype p) : ofSubtype f a = f a :=
  f.subtypeCongr_apply_subtype _ _

@[simp]
theorem ofSubtype_apply_subtypeCompl (f : Perm (Subtype p)) (a : Subtype (¬ p ·)) :
    ofSubtype f a = a := f.subtypeCongr_apply_subtype_compl _ _

@[simp]
theorem ofSubtypeCompl_apply_subtype (f : Perm (Subtype (¬ p ·))) (a : Subtype p) :
    ofSubtype f a = a := f.subtypeCongr_apply_of_neg _ (not_not_intro a.prop)

theorem ofSubtype_apply (f : Perm (Subtype p)) (a : α) :
    ofSubtype f a = if ha : p a then (f ⟨a, ha⟩ : α) else a := by by_cases ha : p a <;> simp [ha]

@[simp]
theorem ofSubtype_refl : ofSubtype (p := p) (Equiv.refl _) = (Equiv.refl _) := subtypeCongr_refl

@[simp]
theorem ofSubtype_symm (f : Perm (Subtype p)) : (ofSubtype f).symm = ofSubtype f.symm :=
  subtypeCongr_symm _ _

@[simp]
theorem ofSubtype_trans (f g : Perm (Subtype p)) :
    (ofSubtype f).trans (ofSubtype g) = ofSubtype (f.trans g) := subtypeCongr_trans _ _ _ _

@[simp]
theorem ofSubtype_trans_compl (f : Perm (Subtype p)) (g : Perm (Subtype (¬ p ·))) :
    (ofSubtype f).trans (ofSubtype g) = f.subtypeCongr g := by
  rw [ofSubtype_compl_def, ofSubtype_def, subtypeCongr_trans, trans_refl, refl_trans]

@[simp]
theorem ofSubtype_compl_trans (f : Perm (Subtype p)) (g : Perm (Subtype (¬ p ·))) :
    (ofSubtype g).trans (ofSubtype f) = f.subtypeCongr g := by
  rw [ofSubtype_compl_def, ofSubtype_def, subtypeCongr_trans, trans_refl, refl_trans]

theorem ofSubtype_trans_comm (f : Perm (Subtype p)) (g : Perm (Subtype (¬ p ·))) :
    (ofSubtype f).trans (ofSubtype g) = (ofSubtype g).trans (ofSubtype f) := by simp

theorem ofSubtype_injective : Function.Injective (ofSubtype : Perm (Subtype p) → Perm α) :=
    fun _ _ h => Equiv.ext fun a => Subtype.ext <| by simpa using Equiv.congr_fun h a

theorem isCompat_ofSubtype (f : Perm (Subtype p)) :
    (ofSubtype f).IsCompat p := isCompat_of_forall_iff <| fun a => by
  by_cases ha : p a <;> simp [ha, Subtype.prop]

end ofSubtype

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
@[simps!]
def subtypePerm (f : Perm α) {p : α → Prop} (h : f.IsCompat p) : Perm (Subtype p) :=
  f.subtypeEquiv (isCompat_iff_equiv_isCompat.mp h)

section SubtypePerm

variable {p : α → Prop}

lemma coe_subtypePerm_eq_map (e : Perm α)
    (h : e.IsCompat p) : ⇑(e.subtypePerm h) = Subtype.map e (h.forall_iff · |>.mp) := rfl

theorem subtypePerm_refl :
    subtypePerm (Equiv.refl α) isCompat_rfl = Equiv.refl { a : α // p a } := subtypeEquiv_refl

theorem subtypePerm_symm (e : Perm α) (h : e.IsCompat p) :
    (e.subtypePerm h).symm = subtypePerm e.symm h.symm := rfl

theorem subtypePerm_trans (e f : Perm α)
    (h : e.IsCompat p) (h' : f.IsCompat p) :
    (e.subtypePerm h).trans (f.subtypePerm h')
    = subtypePerm (e.trans f) (h.trans h') := rfl

@[simp]
theorem subtypePerm_subtypeCongr [DecidablePred p] (e : Perm (Subtype p))
    (f : Perm (Subtype (¬ p ·))) :
    (e.subtypeCongr f).subtypePerm (e.isCompat_subtypeCongr f) = e :=
  Equiv.ext fun _ => Subtype.ext <| by simp

@[simp]
theorem subtypePermCompl_subtypeCongr {p : α → Prop}
    [DecidablePred p] (e : Perm (Subtype p))
    (f : Perm (Subtype (¬ p ·))) :
    (e.subtypeCongr f).subtypePerm (e.isCompat_subtypeCongr f).compl = f :=
  Equiv.ext fun _ => Subtype.ext <| by simp

@[simp]
theorem subtypePerm_subtypeEquiv_subtypePermCompl {p : α → Prop}
    [DecidablePred p] (e : Perm α) (h : e.IsCompat p) :
    (e.subtypePerm h).subtypeCongr (e.subtypePerm h.compl) = e := Equiv.ext fun a => by
  by_cases h : p a <;> simp [h]

@[simp]
theorem ofSubtype_subtypePerm_apply [DecidablePred p] {f : Perm α} (h : f.IsCompat p) {a : α} :
    ofSubtype (subtypePerm f h) a = if p a then f a else a := by
  by_cases hx : p a <;> simp [hx]

@[simp]
theorem subtypePerm_ofSubtype [DecidablePred p] (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (isCompat_ofSubtype f) = f :=
  Equiv.ext fun x => Subtype.ext <| ofSubtype_apply_subtype f x

@[simps! apply symm_apply_coe]
def subtypePermProdEquiv {α : Type*} (p : α → Prop)
    [DecidablePred p] : {e : Perm α // e.IsCompat p} ≃
    (Perm { a : α // p a } × (Perm { a : α // ¬ p a })) where
  toFun := fun e => ⟨subtypePerm e.1 e.2, subtypePerm e.1 e.2.compl⟩
  invFun := fun ef => ⟨ef.1.subtypeCongr ef.2, ef.1.isCompat_subtypeCongr ef.2⟩
  left_inv e := Subtype.ext <| subtypePerm_subtypeEquiv_subtypePermCompl e.1 e.2
  right_inv ef := Prod.ext (subtypePerm_subtypeCongr ef.1 ef.2)
    (subtypePermCompl_subtypeCongr ef.1 ef.2)

end SubtypePerm

section

variable {p : α → Prop} [DecidablePred p]

theorem isFixedOn_ofSubtype (f : Perm (Subtype p)) : (ofSubtype f).IsFixedOn (¬ p ·) :=
   isFixedOn_of_forall_of_pos fun _ => f.ofSubtype_apply_of_neg

theorem isFixedOn_ofSubtypeCompl (f : Perm (Subtype (¬ p ·))) : (ofSubtype f).IsFixedOn p :=
   isFixedOn_of_forall_of_pos fun _ => fun h => f.ofSubtype_apply_of_neg (not_not_intro h)

theorem ofSubtype_subtypePerm_eq_iff {e f : Perm α} {h : f.IsCompat p} :
    ofSubtype (subtypePerm f h) = e ↔ (∀ x, p x → f x = e x) ∧ e.IsFixedOn (¬ p ·) := by
  simp_rw [Equiv.ext_iff, ofSubtype_subtypePerm_apply,
    ite_eq_iff', isFixedOn_iff, eq_comm, forall_and]

@[simp]
theorem ofSubtype_subtypePerm_iff_isFixedOnCompl {f : Perm α} {h : f.IsCompat p} :
    ofSubtype (subtypePerm f h) = f ↔ f.IsFixedOn (¬ p ·) := by
  simp_rw [ofSubtype_subtypePerm_eq_iff, implies_true, true_and]

theorem ofSubtype_subtypePerm_iff_isFixedOn {f : Perm α} {h : f.IsCompat (¬ p ·)} :
    ofSubtype (subtypePerm f h) = f ↔ f.IsFixedOn p := by simp

@[simp]
theorem IsFixedOn.ofSubtype_subtypePerm {f : Perm α} (h : f.IsFixedOn (¬ p ·)) :
    ofSubtype (subtypePerm f h.isCompat.of_compl) = f :=
  ofSubtype_subtypePerm_iff_isFixedOnCompl.mpr h

@[simp]
theorem IsFixedOn.ofSubtypeCompl_subtypePerm {f : Perm α} (h : f.IsFixedOn p) :
    ofSubtype (subtypePerm f h.isCompat.compl) = f :=
  ofSubtype_subtypePerm_iff_isFixedOn.mpr h

theorem IsFixedOn.exists_ofSubtypeCompl {f : Perm α} (h : f.IsFixedOn p) :
    ∃ e : Perm (Subtype (¬ p ·)), ofSubtype e = f := ⟨_, h.ofSubtypeCompl_subtypePerm⟩

theorem IsFixedOn.exists_ofSubtype {f : Perm α} (h : f.IsFixedOn (¬ p ·)) :
    ∃ e : Perm (Subtype p), ofSubtype e = f := ⟨_, h.ofSubtype_subtypePerm⟩

end

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
def subtypeEquivIsFixedOnCompl (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // f.IsFixedOn (¬ p ·) } where
  toFun f := ⟨ofSubtype f, f.isFixedOn_ofSubtype⟩
  invFun f := f.1.subtypePerm f.2.isCompat.of_compl
  left_inv := subtypePerm_ofSubtype
  right_inv f := Subtype.ext <| ofSubtype_subtypePerm_iff_isFixedOnCompl.mpr f.2

@[simps]
def subtypeEquivIsFixedOn (p : α → Prop) [DecidablePred p] :
    Perm (Subtype (¬ p ·)) ≃ { f : Perm α // f.IsFixedOn p} where
  toFun f := ⟨ofSubtype f, f.isFixedOn_ofSubtypeCompl⟩
  invFun f := f.1.subtypePerm f.2.isCompat.compl
  left_inv := subtypePerm_ofSubtype
  right_inv f := Subtype.ext <| ofSubtype_subtypePerm_iff_isFixedOn.mpr f.2

@[simps]
def isCompatEquivProdIsFixedOn {α : Type*} (p : α → Prop)
    [DecidablePred p] : {e : Perm α // e.IsCompat p} ≃
    ({ f : Perm α // f.IsFixedOn (¬ p ·) } × { f : Perm α // f.IsFixedOn p}) where
  toFun e := (⟨ofSubtype (subtypePerm e.1 e.2), isFixedOn_ofSubtype _⟩,
    ⟨ofSubtype (subtypePerm e.1 e.2.compl), isFixedOn_ofSubtypeCompl _⟩)
  invFun ef := ⟨subtypeCongr (subtypePerm ef.1.1 ef.1.2.isCompat.of_compl)
      (subtypePerm ef.2.1 ef.2.2.isCompat.compl), isCompat_subtypeCongr _ _⟩
  left_inv e := by simp
  right_inv ef := by simp [ef.1.2, ef.2.2]

section

variable {α' β' : Type*} (e : Perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/-- Extend the domain of `e : Equiv.Perm α` to one that is over `β` via `f : α → Subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `Set.range f` fixed. For this use-case `Equiv` given by `f` can
be constructed by `Equiv.of_leftInverse'` or `Equiv.of_leftInverse` when there is a known
inverse, or `Equiv.ofInjective` in the general case.
-/
def extendDomain : Perm β' := (f.permCongr e).ofSubtype

@[simp]
theorem extendDomain_apply_image (a : α') : e.extendDomain f (f a) = f (e a) := by
  simp [extendDomain]

theorem extendDomain_apply_subtype {b : β'} (h : p b) :
    e.extendDomain f b = f (e (f.symm ⟨b, h⟩)) := by
  simp [extendDomain, h]

theorem extendDomain_apply_not_subtype {b : β'} (h : ¬p b) : e.extendDomain f b = b := by
  simp [extendDomain, h]

@[simp]
theorem extendDomain_refl : Perm.extendDomain (Equiv.refl _) f = Equiv.refl _ := by
  simp [extendDomain]

@[simp]
theorem extendDomain_symm : (e.extendDomain f).symm = Perm.extendDomain e.symm f :=
  rfl

theorem extendDomain_trans (e e' : Perm α') :
    (e.extendDomain f).trans (e'.extendDomain f) = Perm.extendDomain (e.trans e') f := by
  simp [extendDomain, permCongr_trans]

end

end Perm

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtypePreimage (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β) :
    { x : α → β // x ∘ Subtype.val = x₀ } ≃ ({ a // ¬p a } → β) where
  toFun x a := x.val a
  invFun x := ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext fun ⟨_, h⟩ => dif_pos h⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.val_injective <|
      funext fun a => by
        dsimp only
        split_ifs
        · rw [← hx]; rfl
        · rfl
  right_inv x :=
    funext fun ⟨a, h⟩ =>
      show dite (p a) _ _ = _ by
        dsimp only
        rw [dif_neg h]

section SubtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

theorem subtypePreimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h

theorem subtypePreimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
    ((subtypePreimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h

end SubtypePreimage

section

open Subtype

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtypeSubtypeEquivSubtypeExists (p : α → Prop) (q : Subtype p → Prop) :
    Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun a =>
    ⟨a.1, a.1.2, by
      rcases a with ⟨⟨a, hap⟩, haq⟩
      exact haq⟩,
    fun a => ⟨⟨a, a.2.fst⟩, a.2.snd⟩, fun ⟨⟨_, _⟩, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps!]
def subtypeSubtypeEquivSubtypeInter {α : Type*} (p q : α → Prop) :
    { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtypeSubtypeEquivSubtypeExists p _).trans <|
    subtypeEquivRight fun x => @exists_prop (q x) (p x)

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps!]
def subtypeSubtypeEquivSubtype {α} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
    { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtypeSubtypeEquivSubtypeInter p _).trans <| subtypeEquivRight fun _ => and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
def subtypeUnivEquiv {α} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun _ => Subtype.eq rfl, fun _ => rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtypeSigmaEquiv {α} (p : α → Type*) (q : α → Prop) : { y : Sigma p // q y.1 } ≃ Σ x :
    Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun _ => rfl,
    fun _ => rfl⟩

/-- A subtype of a sigma which pins down the base of the sigma is equivalent to
the respective fiber. -/
@[simps]
def sigmaSubtype {α : Type*} {β : α → Type*} (a : α) :
    {s : Sigma β // s.1 = a} ≃ β a where
  toFun := fun ⟨⟨_, b⟩, h⟩ => h ▸ b
  invFun b := ⟨⟨a, b⟩, rfl⟩
  left_inv := fun ⟨a, h⟩ ↦ by cases h; simp
  right_inv b := by simp

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigmaSubtypeEquivOfSubset {α} (p : α → Type*) (q : α → Prop) (h : ∀ x, p x → q x) :
    (Σ x : Subtype q, p x) ≃ Σ x : α, p x :=
  (subtypeSigmaEquiv p q).symm.trans <| subtypeUnivEquiv fun x => h x.1 x.2

/-- `sigmaFiberEquiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigmaFiberEquiv {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α :=
  ⟨fun x => ↑x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨_, _, rfl⟩ => rfl, fun _ => rfl⟩

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigmaSubtypeFiberEquiv {α β : Type*} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
    (Σ y : Subtype p, { x : α // f x = y }) ≃ α :=
  calc
    _ ≃ Σ y : β, { x : α // f x = y } := sigmaSubtypeEquivOfSubset _ p fun _ ⟨x, h'⟩ => h' ▸ h x
    _ ≃ α := sigmaFiberEquiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigmaSubtypeFiberEquivSubtype {α β : Type*} (f : α → β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (f x)) : (Σ y : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σ y : Subtype q, { x : α // f x = y }) ≃ Σ y :
        Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } := by {
          apply sigmaCongrRight
          intro y
          apply Equiv.symm
          refine (subtypeSubtypeEquivSubtypeExists _ _).trans (subtypeEquivRight ?_)
          intro x
          exact ⟨fun ⟨hp, h'⟩ => congr_arg Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2),
            Subtype.eq h'⟩⟩ }
    _ ≃ Subtype p := sigmaFiberEquiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)

/-- The set of `x : Option α` such that `isSome x` is equivalent to `α`. -/
@[simps]
def optionIsSomeEquiv (α) : { x : Option α // x.isSome } ≃ α where
  toFun o := Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
  left_inv _ := Subtype.eq <| Option.some_get _
  right_inv _ := Option.get_some _ _

/-- A sigma type over an `Option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigmaOptionEquivOfSome {α} (p : Option α → Type) (h : p none → False) :
    (Σ x : Option α, p x) ≃ Σ x : α, p (some x) :=
  haveI h' : ∀ x, p x → x.isSome := fun x => x.recOn (fun hx => (h hx).elim) (fun _ _ => rfl)
  (sigmaSubtypeEquivOfSubset _ _ h').symm.trans (sigmaCongrLeft' (optionIsSomeEquiv α))

/-- The `Pi`-type `∀ i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`Sigma` type such that for all `i` we have `(f i).fst = i`. -/
def piEquivSubtypeSigma (ι) (π : ι → Type*) :
    (∀ i, π i) ≃ { f : ι → Σ i, π i // ∀ i, (f i).1 = i } where
  toFun := fun f => ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
  invFun := fun f i => by rw [← f.2 i]; exact (f.1 i).2
  right_inv := fun ⟨f, hf⟩ =>
    Subtype.eq <| funext fun i => Sigma.ext (hf i).symm <| by simp

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the type of functions `∀ a, {b : β a // p a b}`. -/
def subtypePiEquivPi {β : α → Sort*} {p : ∀ a, β a → Prop} :
    { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } where
  toFun := fun f a => ⟨f.1 a, f.2 a⟩
  invFun := fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩
  left_inv := by
    rintro ⟨f, h⟩
    rfl
  right_inv := by
    rintro f
    funext a
    exact Subtype.ext_val rfl

/-- Any `Unique` type is a left identity for type sigma up to equivalence. Compare with `uniqueProd`
which is non-dependent. -/
@[simps! apply symm_apply]
def uniqueSigma {α} (β : α → Type*) [Unique α] : (i:α) × β i ≃ β default :=
  ⟨fun p ↦ (Unique.eq_default _).rec p.2,
   fun b ↦ ⟨default, b⟩,
   fun _ ↦ Sigma.ext (Unique.default_eq _) (eqRec_heq _ _),
   fun _ ↦ rfl⟩

section
attribute [local simp] Trans.trans sigmaAssoc subtypeSigmaEquiv uniqueSigma eqRec_eq_cast

/-- A subtype of a dependent triple which pins down both bases is equivalent to the
respective fiber. -/
@[simps! +simpRhs apply]
def sigmaSigmaSubtype {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}] {a : α} {b : β a} (h : p ⟨a, b⟩) :
    {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩} ≃ γ a b :=
  calc {s : (a : α) × (b : β a) × γ a b // p ⟨s.1, s.2.1⟩}
  _ ≃ _ := subtypeEquiv (p := fun ⟨a, b, c⟩ ↦ p ⟨a, b⟩) (q := (p ·.1))
    (sigmaAssoc γ).symm (isCompat_of_forall_iff fun s ↦ by simp [sigmaAssoc])
  _ ≃ _ := subtypeSigmaEquiv _ _
  _ ≃ _ := uniqueSigma (fun ab ↦ γ (Sigma.fst <| Subtype.val ab) (Sigma.snd <| Subtype.val ab))
  _ ≃ γ a b := Equiv.cast <| by rw [← show ⟨⟨a, b⟩, h⟩ = uniq.default from uniq.uniq _]

@[simp]
lemma sigmaSigmaSubtype_symm_apply {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    (p : (a : α) × β a → Prop) [uniq : Unique {ab // p ab}]
    {a : α} {b : β a} (c : γ a b) (h : p ⟨a, b⟩) :
    (sigmaSigmaSubtype p h).symm c = ⟨⟨a, ⟨b, c⟩⟩, h⟩ := by
  rw [Equiv.symm_apply_eq]; simp

/-- A specialization of `sigmaSigmaSubtype` to the case where the second base
does not depend on the first, and the property being checked for is simple
equality. Useful e.g. when `γ` is `Hom` inside a category. -/
def sigmaSigmaSubtypeEq {α β : Type*} {γ : α → β → Type*} (a : α) (b : β) :
    {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b} ≃ γ a b :=
  have : Unique (@Subtype ((_ : α) × β) (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b)) := {
    default := ⟨⟨a, b⟩, ⟨rfl, rfl⟩⟩
    uniq := by rintro ⟨⟨a', b'⟩, ⟨rfl, rfl⟩⟩; rfl }
  sigmaSigmaSubtype (fun ⟨a', b'⟩ ↦ a' = a ∧ b' = b) ⟨rfl, rfl⟩

@[simp]
lemma sigmaSigmaSubtypeEq_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β}
    (s : {s : (a : α) × (b : β) × γ a b // s.1 = a ∧ s.2.1 = b}) :
    sigmaSigmaSubtypeEq a b s = cast (congrArg₂ γ s.2.1 s.2.2) s.1.2.2 := by
  simp [sigmaSigmaSubtypeEq]

@[simp]
lemma sigmaSigmaSubtypeEq_symm_apply {α β : Type*} {γ : α → β → Type*} {a : α} {b : β} (c : γ a b) :
    (sigmaSigmaSubtypeEq a b).symm c = ⟨⟨a, ⟨b, c⟩⟩, ⟨rfl, rfl⟩⟩ := by
  simp [sigmaSigmaSubtypeEq]

end

end

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtypeEquivCodomain {X Y : Sort*} [DecidableEq X] {x : X} (f : { x' // x' ≠ x } → Y) :
    { g : X → Y // g ∘ Subtype.val = f } ≃ Y :=
  (subtypePreimage _ f).trans <|
    @funUnique { x' // ¬x' ≠ x } _ <|
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from {
            default := ⟨x, rfl⟩, uniq := fun ⟨_, h⟩ => Subtype.val_injective h })
          (subtypeEquivRight fun _ => not_not)

section SubtypeEquivCodomain

variable {X Y : Sort*} [DecidableEq X] {x : X}
open Subtype

@[simp]
theorem coe_subtypeEquivCodomain (f : { x' // x' ≠ x } → Y) :
    (subtypeEquivCodomain f : _ → Y) =
      fun g : { g : X → Y // g ∘ Subtype.val = f } => (g : X → Y) x :=
  rfl

@[simp]
theorem subtypeEquivCodomain_apply (f : { x' // x' ≠ x } → Y) (g) :
    subtypeEquivCodomain f g = (g : X → Y) x :=
  rfl

theorem coe_subtypeEquivCodomain_symm (f : { x' // x' ≠ x } → Y) :
    ((subtypeEquivCodomain f).symm : Y → _) = fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y, by grind⟩ :=
  rfl

@[simp]
theorem subtypeEquivCodomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl

theorem subtypeEquivCodomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
    ((subtypeEquivCodomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)

theorem subtypeEquivCodomain_symm_apply_ne
    (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
    ((subtypeEquivCodomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end SubtypeEquivCodomain

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtypeQuotientEquivQuotientSubtype (p₁ : α → Prop) {s₁ : Setoid α} {s₂ : Setoid (Subtype p₁)}
    (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂.r x y ↔ s₁.r x y) : {x // p₂ x} ≃ Quotient s₂ where
  toFun a :=
    Quotient.hrecOn a.1 (fun a h => ⟦⟨a, (hp₂ _).2 h⟩⟧)
      (fun a b hab => Function.hfunext (by rw [Quotient.sound hab]) fun _ _ _ =>
        heq_of_eq (Quotient.sound ((h _ _).2 hab)))
      a.2
  invFun a :=
    Quotient.liftOn a (fun a => (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : { x // p₂ x })) fun _ _ hab =>
      Subtype.ext_val (Quotient.sound ((h _ _).1 hab))
  left_inv := by exact fun ⟨a, ha⟩ => Quotient.inductionOn a (fun b hb => rfl) ha
  right_inv a := by exact Quotient.inductionOn a fun ⟨a, ha⟩ => rfl

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y)
    (x hx) : subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ :=
  rfl

@[simp]
theorem subtypeQuotientEquivQuotientSubtype_symm_mk (p₁ : α → Prop)
    [s₁ : Setoid α] [s₂ : Setoid (Subtype p₁)] (p₂ : Quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
    (h : ∀ x y : Subtype p₁, s₂ x y ↔ (x : α) ≈ y) (x) :
    (subtypeQuotientEquivQuotientSubtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.property⟩ :=
  rfl

-- See also `Equiv.ofPreimageEquiv`.
/-- A family of equivalences between fibers gives an equivalence between domains. -/
@[simps!]
def ofFiberEquiv {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) : α ≃ β :=
  (sigmaFiberEquiv f).symm.trans <| (Equiv.sigmaCongrRight e).trans (sigmaFiberEquiv g)

section ofFiberEquiv

theorem ofFiberEquiv_map {α β γ} {f : α → γ} {g : β → γ}
    (e : ∀ c, { a // f a = c } ≃ { b // g b = c }) (a : α) : g (ofFiberEquiv e a) = f a :=
  (_ : { b // g b = _ }).property

end ofFiberEquiv

end Equiv
