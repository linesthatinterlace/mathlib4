/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Subtype
import Mathlib.Logic.Function.Conjugate
import Mathlib.Tactic.Lift

/-!
# Equivalence between types

In this file we continue the work on equivalences begun in `Mathlib/Logic/Equiv/Defs.lean`, defining
a lot of equivalences between various types and operations on these equivalences.

More definitions of this kind can be found in other files.
E.g., `Mathlib/Algebra/Equiv/TransferInstance.lean` does it for many algebraic type classes like
`Group`, `Module`, etc.

## Tags

equivalence, congruence, bijective map
-/

universe u v w z

open Function

-- Unless required to be `Type*`, all variables in this file are `Sort*`
variable {α α₁ α₂ β β₁ β₂ γ δ : Sort*}

namespace Equiv


/-- The product over `Option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def piOptionEquivProd {α} {β : Option α → Type*} :
    (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) where
  toFun f := (f none, fun a => f (some a))
  invFun x a := Option.casesOn a x.fst x.snd
  left_inv f := funext fun a => by cases a <;> rfl

section

/-- A family of equivalences `∀ a, β₁ a ≃ β₂ a` generates an equivalence between `∀ a, β₁ a` and
`∀ a, β₂ a`. -/
@[simps]
def piCongrRight {β₁ β₂ : α → Sort*} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ (∀ a, β₂ a) :=
  ⟨Pi.map fun a ↦ F a, Pi.map fun a ↦ (F a).symm, fun H => funext <| by simp,
    fun H => funext <| by simp⟩

@[simp]
lemma piCongrRight_refl {β : α → Sort*} : piCongrRight (fun a ↦ .refl (β a)) = .refl (∀ a, β a) :=
  rfl

/-- Given `φ : α → β → Sort*`, we have an equivalence between `∀ a b, φ a b` and `∀ b a, φ a b`.
This is `Function.swap` as an `Equiv`. -/
@[simps apply]
def piComm (φ : α → β → Sort*) : (∀ a b, φ a b) ≃ ∀ b a, φ a b :=
  ⟨swap, swap, fun _ => rfl, fun _ => rfl⟩

@[simp]
theorem piComm_symm {φ : α → β → Sort*} : (piComm φ).symm = (piComm <| swap φ) :=
  rfl

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `Sigma.curry` and `Sigma.uncurry` together as an equiv. -/
def piCurry {α} {β : α → Type*} (γ : ∀ a, β a → Type*) :
    (∀ x : Σ i, β i, γ x.1 x.2) ≃ ∀ a b, γ a b where
  toFun := Sigma.curry
  invFun := Sigma.uncurry
  left_inv := Sigma.uncurry_curry
  right_inv := Sigma.curry_uncurry

-- `simps` overapplies these but `simps -fullyApplied` under-applies them
@[simp] theorem piCurry_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*)
    (f : ∀ x : Σ i, β i, γ x.1 x.2) :
    piCurry γ f = Sigma.curry f :=
  rfl

@[simp] theorem piCurry_symm_apply {α} {β : α → Type*} (γ : ∀ a, β a → Type*) (f : ∀ a b, γ a b) :
    (piCurry γ).symm f = Sigma.uncurry f :=
  rfl

end

section

open Sum

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigmaNatSucc (f : ℕ → Type u) : (Σ n, f n) ≃ f 0 ⊕ Σ n, f (n + 1) :=
  ⟨fun x =>
    @Sigma.casesOn ℕ f (fun _ => f 0 ⊕ Σ n, f (n + 1)) x fun n =>
      @Nat.casesOn (fun i => f i → f 0 ⊕ Σ n : ℕ, f (n + 1)) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩

end

section

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ PUnit`. -/
def natEquivNatSumPUnit : ℕ ≃ ℕ ⊕ PUnit where
  toFun n := Nat.casesOn n (inr PUnit.unit) inl
  invFun := Sum.elim Nat.succ fun _ => 0
  left_inv n := by cases n <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- `ℕ ⊕ PUnit` is equivalent to `ℕ`. -/
def natSumPUnitEquivNat : ℕ ⊕ PUnit ≃ ℕ :=
  natEquivNatSumPUnit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ where
  toFun z := Int.casesOn z inl inr
  invFun := Sum.elim Int.ofNat Int.negSucc
  left_inv := by rintro (m | n) <;> rfl
  right_inv := by rintro (m | n) <;> rfl

end

/-- If `α` is equivalent to `β`, then `Unique α` is equivalent to `Unique β`. -/
def uniqueCongr (e : α ≃ β) : Unique α ≃ Unique β where
  toFun h := @Equiv.unique _ _ h e.symm
  invFun h := @Equiv.unique _ _ h e
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- If `α` is equivalent to `β`, then `IsEmpty α` is equivalent to `IsEmpty β`. -/
theorem isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.isEmpty _ _ h e.symm, fun h => @Function.isEmpty _ _ h e⟩

protected theorem isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.isEmpty_congr.mpr ‹_›

instance : CanLift (α → β) (α ≃ β) (↑) Bijective where prf f hf := ⟨ofBijective f hf, rfl⟩

section Swap

variable [DecidableEq α]

/-- A helper function for `Equiv.swap`. -/
def swapCore (a b r : α) : α :=
  if r = a then b else if r = b then a else r

theorem swapCore_self (r a : α) : swapCore a a r = r := by
  unfold swapCore
  split_ifs <;> simp [*]

theorem swapCore_swapCore (r a b : α) : swapCore a b (swapCore a b r) = r := by
  unfold swapCore; split_ifs <;> grind

theorem swapCore_comm (r a b : α) : swapCore a b r = swapCore b a r := by
  unfold swapCore; split_ifs <;> grind

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : Perm α :=
  ⟨swapCore a b, swapCore a b, fun r => swapCore_swapCore r a b,
    fun r => swapCore_swapCore r a b⟩

@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext fun r => swapCore_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext fun r => swapCore_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a := by
  by_cases h : b = a <;> simp [swap_apply_def, h]

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x := by
  simp +contextual [swap_apply_def]

theorem eq_or_eq_of_swap_apply_ne_self {a b x : α} (h : swap a b x ≠ x) : x = a ∨ x = b := by
  contrapose! h
  exact swap_apply_of_ne_of_ne h.1 h.2

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext fun _ => swapCore_swapCore _ _ _

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y := by
  refine ⟨fun h => (Equiv.refl _).injective ?_, fun h => h ▸ swap_self _⟩
  rw [← h, swap_apply_left, h, refl_apply]

theorem swap_comp_apply {a b x : α} (π : Perm α) :
    π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x := by
  cases π
  rfl

theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j :=
  funext fun x => by rw [update_apply _ i j, update_apply _ j i, Equiv.swap_apply_def, id]

theorem comp_swap_eq_update (i j : α) (f : α → β) :
    f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) := by
  rw [swap_eq_update, comp_update, comp_update, comp_id]

@[simp]
theorem symm_trans_swap_trans [DecidableEq β] (a b : α) (e : α ≃ β) :
    (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
  Equiv.ext fun x => by
    have : ∀ a, e.symm x = a ↔ x = e a := fun a => by grind
    simp only [trans_apply, swap_apply_def, this]
    split_ifs <;> simp

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
    (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a := by
  rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) :
    v (swap i j k) = v k := by
  by_cases hi : k = i
  · rw [hi, swap_apply_left, hv]
  by_cases hj : k = j
  · rw [hj, swap_apply_right, hv]
  rw [swap_apply_of_ne_of_ne hi hj]

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w := by
  rw [apply_eq_iff_eq_symm_apply, symm_swap]

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  by_cases hab : a = b
  · simp [hab]
  by_cases hax : x = a
  · simp [hax, eq_comm]
  by_cases hbx : x = b
  · simp [hbx]
  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]

namespace Perm

@[simp]
theorem sumCongr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
    Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  ext x
  cases x
  · simp only [Equiv.sumCongr_apply, Sum.map, coe_refl, comp_id, Sum.elim_inl, comp_apply,
      swap_apply_def, Sum.inl.injEq]
    split_ifs <;> rfl
  · simp [Sum.map, swap_apply_of_ne_of_ne]

@[simp]
theorem sumCongr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
    Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  ext x
  cases x
  · simp [Sum.map, swap_apply_of_ne_of_ne]
  · simp only [Equiv.sumCongr_apply, Sum.map, coe_refl, comp_id, Sum.elim_inr, comp_apply,
      swap_apply_def, Sum.inr.injEq]
    split_ifs <;> rfl

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def setValue (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
theorem setValue_eq (f : α ≃ β) (a : α) (b : β) : setValue f a b a = b := by
  simp [setValue, swap_apply_left]

end Swap

end Equiv

namespace Function.Involutive

/-- Convert an involutive function `f` to a permutation with `toFun = invFun = f`. -/
def toPerm (f : α → α) (h : Involutive f) : Equiv.Perm α :=
  ⟨f, f, h.leftInverse, h.rightInverse⟩

@[simp]
theorem coe_toPerm {f : α → α} (h : Involutive f) : (h.toPerm f : α → α) = f :=
  rfl

@[simp]
theorem toPerm_symm {f : α → α} (h : Involutive f) : (h.toPerm f).symm = h.toPerm f :=
  rfl

theorem toPerm_involutive {f : α → α} (h : Involutive f) : Involutive (h.toPerm f) :=
  h

theorem symm_eq_self_of_involutive (f : Equiv.Perm α) (h : Involutive f) : f.symm = f :=
  DFunLike.coe_injective (h.leftInverse_iff.mp f.left_inv)

end Function.Involutive

theorem PLift.eq_up_iff_down_eq {x : PLift α} {y : α} : x = PLift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply

theorem Function.Injective.map_swap [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x y z : α) :
    f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) := by
  conv_rhs => rw [Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · rw [hf h₁, Equiv.swap_apply_left]
  · rw [hf h₂, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)]

namespace Equiv

section

/-- Transport dependent functions through an equivalence of the base space.
-/
@[simps apply, simps -isSimp symm_apply]
def piCongrLeft' (P : α → Sort*) (e : α ≃ β) : (∀ a, P a) ≃ ∀ b, P (e.symm b) where
  toFun f x := f (e.symm x)
  invFun f x := (e.symm_apply_apply x).ndrec (f (e x))
  left_inv f := funext fun x =>
    (by rintro _ rfl; rfl : ∀ {y} (h : y = x), h.ndrec (f y) = f x) (e.symm_apply_apply x)
  right_inv f := funext fun x =>
    (by rintro _ rfl; rfl : ∀ {y} (h : y = x), (congr_arg e.symm h).ndrec (f y) = f x)
      (e.apply_symm_apply x)

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. For that reason,
we have to explicitly substitute along `e.symm (e a) = a` in the statement of this lemma. -/
add_decl_doc Equiv.piCongrLeft'_symm_apply

/-- This lemma is impractical to state in the dependent case. -/
@[simp]
theorem piCongrLeft'_symm (P : Sort*) (e : α ≃ β) :
    (piCongrLeft' (fun _ => P) e).symm = piCongrLeft' _ e.symm := by ext; simp [piCongrLeft']

/-- Note: the "obvious" statement `(piCongrLeft' P e).symm g a = g (e a)` doesn't typecheck: the
LHS would have type `P a` while the RHS would have type `P (e.symm (e a))`. This lemma is a way
around it in the case where `a` is of the form `e.symm b`, so we can use `g b` instead of
`g (e (e.symm b))`. -/
@[simp]
lemma piCongrLeft'_symm_apply_apply (P : α → Sort*) (e : α ≃ β) (g : ∀ b, P (e.symm b)) (b : β) :
    (piCongrLeft' P e).symm g (e.symm b) = g b := by
  rw [piCongrLeft'_symm_apply, ← heq_iff_eq, rec_heq_iff_heq]
  exact congr_arg_heq _ (e.apply_symm_apply _)

@[simp]
lemma piCongrLeft'_refl (P : α → Sort*) : piCongrLeft' P (.refl α) = .refl (∀ a, P a) := rfl

end

section

variable (P : β → Sort w) (e : α ≃ β)

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def piCongrLeft : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (piCongrLeft' P e.symm).symm

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. For that reason,
we have to explicitly substitute along `e (e.symm b) = b` in the statement of this lemma. -/
lemma piCongrLeft_apply (f : ∀ a, P (e a)) (b : β) :
    (piCongrLeft P e) f b = e.apply_symm_apply b ▸ f (e.symm b) :=
  rfl

@[simp]
lemma piCongrLeft_symm_apply (g : ∀ b, P b) (a : α) :
    (piCongrLeft P e).symm g a = g (e a) :=
  piCongrLeft'_apply P e.symm g a

@[simp]
lemma piCongrLeft_refl (P : α → Sort*) : piCongrLeft P (.refl α) = .refl (∀ a, P a) :=
  rfl

/-- Note: the "obvious" statement `(piCongrLeft P e) f b = f (e.symm b)` doesn't typecheck: the
LHS would have type `P b` while the RHS would have type `P (e (e.symm b))`. This lemma is a way
around it in the case where `b` is of the form `e a`, so we can use `f a` instead of
`f (e.symm (e a))`. -/
@[simp]
lemma piCongrLeft_apply_apply (f : ∀ a, P (e a)) (a : α) :
    (piCongrLeft P e) f (e a) = f a :=
  piCongrLeft'_symm_apply_apply P e.symm f a

open Sum

lemma piCongrLeft_apply_eq_cast {P : β → Sort v} {e : α ≃ β}
    (f : (a : α) → P (e a)) (b : β) :
    piCongrLeft P e f b = cast (congr_arg P (e.apply_symm_apply b)) (f (e.symm b)) :=
  Eq.rec_eq_cast _ _

theorem piCongrLeft_sumInl {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (i : ι) :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inl i)) = f i := by
  simp_rw [piCongrLeft_apply_eq_cast, sumPiEquivProdPi_symm_apply,
    sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)), cast_cast, cast_eq]

theorem piCongrLeft_sumInr {ι ι' ι''} (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'') (f : ∀ i, π (e (inl i)))
    (g : ∀ i, π (e (inr i))) (j : ι') :
    piCongrLeft π e (sumPiEquivProdPi (fun x => π (e x)) |>.symm (f, g)) (e (inr j)) = g j := by
  simp_rw [piCongrLeft_apply_eq_cast, sumPiEquivProdPi_symm_apply,
    sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)), cast_cast, cast_eq]

@[deprecated (since := "2025-02-21")] alias piCongrLeft_sum_inl := piCongrLeft_sumInl
@[deprecated (since := "2025-02-21")] alias piCongrLeft_sum_inr := piCongrLeft_sumInr

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def piCongr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]
theorem coe_piCongr_symm : ((h₁.piCongr h₂).symm :
    (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp]
theorem piCongr_symm_apply (f : ∀ b, Z b) :
    (h₁.piCongr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp]
theorem piCongr_apply_apply (f : ∀ a, W a) (a : α) : h₁.piCongr h₂ f (h₁ a) = h₂ a (f a) := by
  simp only [piCongr, piCongrRight, trans_apply, coe_fn_mk, piCongrLeft_apply_apply, Pi.map_apply]

end

section

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/-- Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def piCongr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (piCongr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
theorem coe_piCongr' :
    (h₁.piCongr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b <| f <| h₁.symm b :=
  rfl

theorem piCongr'_apply (f : ∀ a, W a) : h₁.piCongr' h₂ f = fun b => h₂ b <| f <| h₁.symm b :=
  rfl

@[simp]
theorem piCongr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
    (h₁.piCongr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) := by
  simp [piCongr', piCongr_apply_apply]

end

lemma eq_conj {α α' β β' : Sort*} (ε₁ : α ≃ α') (ε₂ : β' ≃ β)
    (f : α → β) (f' : α' → β') : ε₂.symm ∘ f ∘ ε₁.symm = f' ↔ f = ε₂ ∘ f' ∘ ε₁ := by
  rw [Equiv.symm_comp_eq, Equiv.comp_symm_eq, Function.comp_assoc]

section BinaryOp

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : Semiconj e f (e.conj f) := fun x => by simp

theorem semiconj₂_conj : Semiconj₂ e f (e.arrowCongr e.conj f) := fun x y => by simp [arrowCongr]

instance [Std.Associative f] : Std.Associative (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isAssociative_right e.surjective

instance [Std.IdempotentOp f] : Std.IdempotentOp (e.arrowCongr (e.arrowCongr e) f) :=
  (e.semiconj₂_conj f).isIdempotent_right e.surjective

end BinaryOp

section ULift

@[simp]
theorem ulift_symm_down {α} (x : α) : (Equiv.ulift.{u, v}.symm x).down = x :=
  rfl

end ULift

end Equiv

theorem Function.Injective.swap_apply
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y z : α) :
    Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  Eq.symm (map_swap hf x y z)

theorem Function.Injective.swap_comp
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
    Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext fun _ => hf.swap_apply _ _ _

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A nonempty subsingleton type is (noncomputably) equivalent to `PUnit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/-- `Unique (Unique α)` is equivalent to `Unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default) fun h =>
    { default := h, uniq := fun _ => Subsingleton.elim _ _ }

/-- If `Unique β`, then `Unique α` is equivalent to `α ≃ β`. -/
def uniqueEquivEquivUnique (α : Sort u) (β : Sort v) [Unique β] : Unique α ≃ (α ≃ β) :=
  equivOfSubsingletonOfSubsingleton (fun _ => Equiv.ofUnique _ _) Equiv.unique

namespace Function

variable {α' : Sort*}

theorem update_comp_equiv [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) :
    update f a v ∘ g = update (f ∘ g) (g.symm a) v := by
  rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

theorem update_apply_equiv_apply [DecidableEq α'] [DecidableEq α] (f : α → β)
    (g : α' ≃ α) (a : α) (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_fun (update_comp_equiv f g a v) a'

theorem piCongrLeft'_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ a, P a) (b : β) (x : P (e.symm b)) :
    e.piCongrLeft' P (update f (e.symm b) x) = update (e.piCongrLeft' P f) b x := by
  ext b'
  rcases eq_or_ne b' b with (rfl | h) <;> simp_all

theorem piCongrLeft'_symm_update [DecidableEq α] [DecidableEq β] (P : α → Sort*) (e : α ≃ β)
    (f : ∀ b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
    (e.piCongrLeft' P).symm (update f b x) = update ((e.piCongrLeft' P).symm f) (e.symm b) x := by
  simp [(e.piCongrLeft' P).symm_apply_eq, piCongrLeft'_update]

end Function
