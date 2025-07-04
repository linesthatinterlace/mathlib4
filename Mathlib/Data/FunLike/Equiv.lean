/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.FunLike.Embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of isomorphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B] extends Equiv A B where
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variable (A B : Type*) [MyClass A] [MyClass B]

instance instEquivLike : EquivLike (MyIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

end MyIso
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `EquivLike`

The `EquivLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EquivLike` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
/-- `MyIsoClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyIso`. -/
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- This goes after `MyIsoClass.instEquivLike`:
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'

-- [Insert `ext` and `copy` here]

end MyIso
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _

namespace CoolerIso

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]

end CoolerIso
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/


/-- The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

Note that this does not directly extend `FunLike`, nor take `FunLike` as a parameter,
so we can state `coe_injective'` in a nicer way.

This typeclass is used in the definition of the isomorphism (or equivalence) typeclasses,
such as `ZeroEquivClass`, `MulEquivClass`, `MonoidEquivClass`, ....
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E → α → β
  /-- The coercion to a function in the backwards direction. -/
  inv : E → β → α
  /-- The coercions are left inverses. -/
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  /-- The two coercions to functions are jointly injective. -/
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`

namespace EquivLike

variable {E F α β γ : Sort*} [EquivLike E α β] [EquivLike F β γ]

theorem inv_apply_coe_apply (e : E) (a : α) : inv e (coe e a) = a := left_inv _ _

theorem coe_apply_inv_apply (e : E) (b : β) : coe e (inv e b) = b := right_inv _ _

theorem coe_injective : Function.Injective (EquivLike.coe : E → α → β) := fun e g h ↦
  coe_injective' e g h ((left_inv e).eq_rightInverse (h ▸ right_inv g))

theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h ▸ left_inv g)) h

theorem inv_eq_iff_coe_eq {e e' : E} : inv e = inv e' ↔ coe e = coe e' := by
  rw [coe_injective.eq_iff, inv_injective.eq_iff]

theorem bijective_coe (e : E) : Function.Bijective (coe e) :=
  ⟨(left_inv e).injective, (right_inv e).surjective⟩

theorem bijective_inv (e : E) : Function.Bijective (inv e) :=
  ⟨(right_inv e).injective, (left_inv e).surjective⟩

theorem injective_coe (e : E) : Function.Injective (coe e) := (bijective_coe e).injective
theorem surjective_coe (e : E) : Function.Surjective (coe e) := (bijective_coe e).surjective
theorem injective_inv (e : E) : Function.Injective (inv e) := (bijective_inv e).injective
theorem surjective_inv (e : E) : Function.Surjective (inv e) := (bijective_inv e).surjective

theorem coe_apply_eq_iff_eq (f : E) {x y : α} : coe f x = coe f y ↔ x = y :=
  (injective_coe f).eq_iff

theorem inv_apply_eq_iff_eq (f : E) {x y : β} : inv f x = inv f y ↔ x = y :=
  (injective_inv f).eq_iff

theorem inv_apply_eq_iff_eq_coe_apply {e : E} {b : β} {a : α} : inv e b = a ↔ b = coe e a := by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]

theorem eq_inv_apply_iff_coe_apply_eq {e : E} {b : β} {a : α} : a = inv e b ↔ coe e a = b := by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [right_inv e b, (left_inv e a).symm]

/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
lemma subsingleton_dom {F β γ} [EquivLike F β γ] [Subsingleton β] : Subsingleton F :=
  ⟨fun _ _ ↦ inv_injective (funext fun _ => Subsingleton.elim _ _)⟩

/-- A class that represents `EquivLike` types equipped with a symmetry operation. -/
class Symm (E : Sort*) (F : outParam Sort*) {α β : outParam Sort*}
  [EquivLike E α β] [EquivLike F β α] where
  /-- Symmetry operation. -/
  symm : E → F
  protected coe_comp_symm' : coe ∘ symm = inv := by rfl

/-- Symmetry operation. -/
def symm [EquivLike E α β] [EquivLike F β α] [Symm E F] : E → F := Symm.symm

section Symm

instance [EquivLike E α β] [EquivLike F β α] : Subsingleton (Symm E F) where
  allEq a b := by
    cases a with | mk symm ha; cases b with | mk symm' hb
    rw [← ha] at hb
    cases (coe_injective).comp_left hb
    rfl

variable {F : Sort*} [EquivLike F β α] [Symm E F] {e : E} {f : F} {a : α} {b : β}

theorem coe_comp_symm : coe ∘ symm = inv (E := E) := Symm.coe_comp_symm'
theorem coe_symm : coe (symm e) = inv e := congrFun coe_comp_symm _
theorem coe_symm_apply : coe (symm e) b = inv e b := congrFun coe_symm _
theorem inv_comp_symm : inv ∘ symm = coe (E := E) := funext₂ <| fun _ _ => by
  simp only [Function.comp_apply, inv_apply_eq_iff_eq_coe_apply, coe_symm, inv_apply_coe_apply]
theorem inv_symm : inv (symm e) = coe e := congrFun inv_comp_symm _
theorem inv_symm_apply : inv (symm e) a = coe e a := congrFun inv_symm _

theorem symm_injective : Function.Injective (symm : E → F) :=
  fun _ _ h => inv_injective <| by simpa [coe_symm] using congrArg coe h

theorem symm_symm [Symm F E] (e : E) : symm (symm e) = e :=
  coe_injective <| by rw [coe_symm, inv_symm]

theorem symm_bijective [Symm F E] : Function.Bijective (symm : E → F) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem symm_surjective [Symm F E] : Function.Surjective (symm : E → F) :=
  symm_bijective.surjective

end Symm

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)
  coe_injective' _ _ h := coe_injective h

@[simp] theorem coe_eq_coeFn {e : E} : coe e = ⇑e := rfl

instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := injective_coe e

protected theorem bijective (e : E) : Function.Bijective e := bijective_coe e
protected theorem injective (e : E) : Function.Injective e := injective_coe e
protected theorem surjective (e : E) : Function.Surjective e := surjective_coe e

theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y := coe_apply_eq_iff_eq f

@[simp]
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f

@[simp]
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f

theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  (EquivLike.injective e).of_comp_iff _

@[simp]
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f


/-- These lemmas are only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply_apply`
or its equivalent. -/

@[simp]
theorem inv_apply_apply (e : E) (a : α) : inv e (e a) = a := inv_apply_coe_apply e a
@[simp]
theorem apply_inv_apply (e : E) (b : β) : e (inv e b) = b := coe_apply_inv_apply e b

section
variable {p : α → Prop} {q : β → Prop} (e : E)

lemma forall_congr_right : (∀ a, q (e a)) ↔ ∀ b, q b :=
  ⟨fun h a ↦ by simpa using h (inv e a), fun h _ ↦ h _⟩

lemma forall_congr_left : (∀ a, p a) ↔ ∀ b, p (inv e b) :=
  ⟨fun h _ ↦ h _, fun h a ↦ by simpa using h (e a)⟩

lemma forall_congr (h : ∀ a, p a ↔ q (e a)) : (∀ a, p a) ↔ ∀ b, q b :=
  (forall_congr_left e).trans (by simp [h])

lemma forall_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  (forall_congr_left e).trans (by simp [h])

lemma exists_congr_right : (∃ a, q (e a)) ↔ ∃ b, q b :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨a, h⟩ ↦ ⟨inv e a, by simpa using h⟩⟩

lemma exists_congr_left : (∃ a, p a) ↔ ∃ b, p (inv e b) :=
  ⟨fun ⟨a, h⟩ ↦ ⟨e a, by simpa using h⟩, fun ⟨_, h⟩ ↦ ⟨_, h⟩⟩

lemma exists_congr (h : ∀ a, p a ↔ q (e a)) : (∃ a, p a) ↔ ∃ b, q b :=
  (exists_congr_left e).trans <| by simp [h]

lemma exists_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  (exists_congr_left e).trans <| by simp only [h]

lemma existsUnique_congr_right : (∃! a, q (e a)) ↔ ∃! b, q b :=
  exists_congr e <| by simpa using fun _ _ ↦ forall_congr e (by simp)

lemma existsUnique_congr_left : (∃! a, p a) ↔ ∃! b, p (inv e b) :=
  exists_congr e <| by simpa using fun _ _ ↦ forall_congr e (by simp)

lemma existsUnique_congr (h : ∀ a, p a ↔ q (e a)) : (∃! a, p a) ↔ ∃! b, q b :=
  (existsUnique_congr_left e).trans <| by simp [h]

lemma existsUnique_congr' (h : ∀ b, p (inv e b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  (existsUnique_congr_left e).trans <| by simp [h]

end

@[deprecated inv_apply_eq_iff_eq_coe_apply (since := "2025-06-20")]
lemma inv_apply_eq_iff_eq_apply {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a :=
  inv_apply_eq_iff_eq_coe_apply

section Symm
variable {F : Sort*} [EquivLike F β α] [Symm E F] {e : E} {f : F} {a : α} {b : β}

@[simp] theorem inv_eq_coeFn_symm : inv e = symm e := coe_symm.symm

section

variable {p : α → Prop} {q : β → Prop} (e : E)

lemma forall_congr_left_symm : (∀ a, p a) ↔ ∀ b, p (symm e b) :=
  (forall_congr_left e).trans <| by simp

lemma forall_congr'_symm (h : ∀ b, p (symm e b) ↔ q b) : (∀ a, p a) ↔ ∀ b, q b :=
  forall_congr' e <| by simp [h]

lemma exists_congr_left_symm : (∃ a, p a) ↔ ∃ b, p (symm e b) :=
  (exists_congr_left e).trans <| by simp

lemma exists_congr'_symm (h : ∀ b, p (symm e b) ↔ q b) : (∃ a, p a) ↔ ∃ b, q b :=
  exists_congr' e <| by simp [h]

lemma existsUnique_congr_left_symm : (∃! a, p a) ↔ ∃! b, p (symm e b) :=
  (existsUnique_congr_left e).trans <| by simp

lemma existsUnique_congr'_symm (h : ∀ b, p (symm e b) ↔ q b) : (∃! a, p a) ↔ ∃! b, q b :=
  existsUnique_congr' e <| by simp [h]

end

end Symm


end EquivLike
#lint
