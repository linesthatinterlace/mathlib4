import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Finite.Perm
import Mathlib.Algebra.Group.Subgroup.Map

@[simps!]
def Fin.valEquiv : Fin n ≃o Set.range (Fin.val (n := n)) where
  toFun i := ⟨i.1, ⟨i, rfl⟩⟩
  invFun i := ⟨i, i.2.casesOn (fun i h => h ▸ i.isLt)⟩
  map_rel_iff' {_ _} := by simp_rw [Equiv.coe_fn_mk, Subtype.mk_le_mk, Fin.val_fin_le]

section

variable {α : Type*} {p : α → Prop} {q : (i : α) → p i → Prop}

instance  [∀ i h, Decidable (q i h)] [Fintype { x // p x }] :
    Decidable (∀ i, (h : p i) → q i h) :=
  decidable_of_iff (∀ (i : Subtype p), q i i.2) Subtype.forall

instance [∀ i h, Decidable (q i h)] [Fintype { x // p x }] :
    Decidable (∃ i, ∃ (h : p i), q i h) :=
  decidable_of_iff (∃ (i : Subtype p), q i i.2) Subtype.exists

instance {q : α → Prop} [DecidablePred q] [Fintype { x // p x }] :
    Decidable (∀ i, p i → q i) := inferInstance

instance {q : α → Prop} [DecidablePred q] [Fintype { x // p x }] :
    Decidable (∃ i, p i ∧ q i) :=
  decidable_of_iff (∃ i, ∃ _ : p i, q i) (exists_congr fun _ => exists_prop)

instance {q : α → Prop} [DecidablePred q] [Fintype { x // ¬p x }] :
    Decidable (∀ i, q i → p i) := decidable_of_iff (∀ i, ¬ p i → ¬ q i) <| by simp_rw [not_imp_not]

end

instance {n : ℕ} : Fintype { i // i < n } := Fintype.ofEquiv _ Fin.equivSubtype
instance {n : ℕ} : Fintype { i // ¬ n ≤ i } := Fintype.ofEquiv _
  (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (fun _ => Nat.not_le.symm)))

instance {n : ℕ} : Finite { i // i < n } := ⟨Fin.equivSubtype.symm⟩

instance {n : ℕ} : Finite { i // ¬ n ≤ i } :=
  ⟨(Equiv.subtypeEquivRight (fun _ => Nat.not_le)).trans Fin.equivSubtype.symm⟩

namespace Equiv.Perm

section

variable {α : Type*} {e : Perm α} {p : α → Prop}

@[simp] theorem imp_perm_inv_iff_imp_perm [Finite { x // p x }] :
    (∀ i, p i → p (e⁻¹ i)) ↔ (∀ i, p i → p (e i)) := by
  constructor <;> intro h i hi <;>
  have h_surj := Finite.surjective_of_injective (Subtype.map_injective h (Equiv.injective _)) <;>
  rcases h_surj ⟨_, hi⟩ with ⟨⟨j, hj⟩, hej⟩ <;> cases Subtype.mk_eq_mk.mp hej <;> simpa

@[simp] theorem perm_imp_iff_imp_perm [Finite { x // p x }] :
    (∀ i, p (e i) → p i) ↔ (∀ i, p i → p (e i)) := by
  simp_rw [← e⁻¹.forall_congr_right (q := fun i => p _ → p i),
    apply_inv_self, imp_perm_inv_iff_imp_perm]

@[simp] theorem imp_perm_iff_perm_iff [Finite { x // p x }] :
    (∀ i, p i → p (e i)) ↔ (∀ i, p (e i) ↔ p i) := by
  simp only [iff_def, forall_and, perm_imp_iff_imp_perm, and_self]

instance [DecidablePred p] [Fintype { x // p x }] :
    Decidable (∀ i, p (e i) → p i) := decidable_of_decidable_of_iff perm_imp_iff_imp_perm.symm

instance [DecidablePred p] [Fintype { x // p x }] :
    Decidable (∀ i, p (e i) ↔ p i) := decidable_of_decidable_of_iff imp_perm_iff_perm_iff

theorem imp_perm_inv_iff_imp_perm' [Finite { x // ¬p x }] :
    (∀ i, p i → p (e⁻¹ i)) ↔ (∀ i, p i → p (e i)) := by
  simp_rw [← not_imp_not (a := p _), perm_imp_iff_imp_perm (p := fun i => ¬ p i),
    imp_perm_inv_iff_imp_perm]

theorem perm_imp_iff_imp_perm' [Finite { x // ¬p x }] :
    (∀ i, p (e i) → p i) ↔ (∀ i, p i → p (e i)) := by
  simp_rw [← e⁻¹.forall_congr_right (q := fun i => p _ → p i),
    apply_inv_self, imp_perm_inv_iff_imp_perm']

theorem imp_perm_iff_perm_iff' [Finite { x // ¬p x }] :
    (∀ i, p i → p (e i)) ↔ (∀ i, p (e i) ↔ p i) := by
  simp only [iff_def, forall_and, perm_imp_iff_imp_perm', and_self]

instance [DecidablePred p] [Fintype { x // ¬ p x }] :
    Decidable (∀ i, p (e i) ↔ p i) := decidable_of_iff (∀ i, ¬ p i → ¬ p (e⁻¹ i)) <| by
  simp_rw [imp_perm_inv_iff_imp_perm, imp_perm_iff_perm_iff, not_iff_not]

end

@[irreducible] def SplitsAt (e : Perm ℕ) (n : ℕ) := ∀ i, i < n → e i < n

section SplitsAt

variable {e f : Perm ℕ}

theorem splitsAt_iff_apply_lt_of_lt : e.SplitsAt n ↔ ∀ i, i < n → e i < n := by
  simp only [SplitsAt]

instance : Decidable (e.SplitsAt n) :=
  decidable_of_iff (∀ i, i < n → e i < n) splitsAt_iff_apply_lt_of_lt.symm

theorem splitsAt_iff_apply_lt_iff_lt : e.SplitsAt n ↔ ∀ i, e i < n ↔ i < n := by
  rw [splitsAt_iff_apply_lt_of_lt, imp_perm_iff_perm_iff]

theorem splitsAt_iff_apply_ge_iff_ge : e.SplitsAt n ↔ ∀ i, n ≤ e i ↔ n ≤ i := by
  simp_rw [← Nat.not_lt, not_iff_not, splitsAt_iff_apply_lt_iff_lt]

theorem splitsAt_iff_apply_ge_of_ge : e.SplitsAt n ↔ ∀ i, n ≤ i → n ≤ e i := by
  simp_rw [splitsAt_iff_apply_ge_iff_ge, imp_perm_iff_perm_iff']

theorem splitsAt_of_apply_lt_of_lt (h : ∀ i, i < n → e i < n) : e.SplitsAt n :=
  splitsAt_iff_apply_lt_of_lt.mpr h

theorem splitsAt_of_apply_ge_of_ge (h : ∀ i, n ≤ i → n ≤ e i) : e.SplitsAt n :=
  splitsAt_iff_apply_ge_of_ge.mpr h

@[simp]
theorem SplitsAt.apply_lt_iff_lt (he : e.SplitsAt n) : ∀ i, e i < n ↔ i < n :=
  splitsAt_iff_apply_lt_iff_lt.mp he

@[simp]
theorem SplitsAt.apply_ge_iff_ge (he : e.SplitsAt n) : ∀ i, n ≤ e i ↔ n ≤ i :=
  splitsAt_iff_apply_ge_iff_ge.mp he

theorem SplitsAt.apply_lt_of_lt (he : e.SplitsAt n) : ∀ i, i < n → e i < n := fun _ => by
  simp_rw [he.apply_lt_iff_lt, imp_self]

theorem SplitsAt.apply_ge_of_ge (he : e.SplitsAt n) : ∀ i, n ≤ i → n ≤ e i := fun _ => by
  simp_rw [he.apply_ge_iff_ge, imp_self]

theorem SplitsAt.lt_of_apply_lt (he : e.SplitsAt n) : ∀ i, e i < n → i < n := fun _ => by
  simp_rw [he.apply_lt_iff_lt, imp_self]

theorem SplitsAt.ge_of_apply_ge (he : e.SplitsAt n) : ∀ i, n ≤ e i → n ≤ i := fun _ => by
  simp_rw [he.apply_ge_iff_ge, imp_self]

theorem splitsAt_one : SplitsAt 1 n := splitsAt_of_apply_lt_of_lt (fun _  => id)

theorem SplitsAt.inv (he : e.SplitsAt n) : e⁻¹.SplitsAt n := by
  apply splitsAt_of_apply_lt_of_lt
  rw [imp_perm_inv_iff_imp_perm]
  exact he.apply_lt_of_lt

@[simp] theorem inv_splitsAt : e⁻¹.SplitsAt n ↔ e.SplitsAt n := ⟨SplitsAt.inv, SplitsAt.inv⟩

theorem SplitsAt.mul (he : e.SplitsAt n) (hf : f.SplitsAt n) : (e * f).SplitsAt n := by
  refine splitsAt_of_apply_lt_of_lt <| fun _ _ => ?_
  simpa only [mul_apply, he.apply_lt_iff_lt, hf.apply_lt_iff_lt]

theorem splitsAt_zero : e.SplitsAt 0 :=
  splitsAt_of_apply_lt_of_lt (fun _ h => (Nat.not_lt_zero _ h).elim)

end SplitsAt

def SplitsAt.piecewise {e : Perm ℕ} {f : Perm ℕ} (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    Perm ℕ where
  toFun i := if i < n then e i else f i
  invFun i := if i < n then e⁻¹ i else f⁻¹ i
  left_inv i := by
    simp_rw [apply_ite ⇑e⁻¹, apply_ite ⇑f⁻¹, apply_ite (· < n), inv_apply_self,
      he.apply_lt_iff_lt, hf.apply_lt_iff_lt, ite_self]
    split_ifs <;> rfl
  right_inv i := by
    simp_rw [apply_ite ⇑e, apply_ite ⇑f, apply_ite (· < n), apply_inv_self,
      he.inv.apply_lt_iff_lt, hf.inv.apply_lt_iff_lt, ite_self]
    split_ifs <;> rfl

section Piecewise

variable {e f e' f' : Perm ℕ} {he : e.SplitsAt n} {hf : f.SplitsAt n}
    {he' : e'.SplitsAt n} {hf' : f'.SplitsAt n}

theorem piecewise_apply : he.piecewise hf i = if i < n then e i else f i := rfl
theorem piecewise_symm_apply : (he.piecewise hf).symm i = if i < n then e⁻¹ i else f⁻¹ i := rfl

@[simp] theorem piecewise_apply_of_lt : ∀ i, i < n → he.piecewise hf i = e i :=
  fun _ hi => if_pos hi

@[simp] theorem piecewise_apply_of_ge : ∀ i, n ≤ i → he.piecewise hf i = f i :=
  fun _ hi => if_neg hi.not_gt

@[simp] theorem splitsAt_piecewise (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    (he.piecewise hf).SplitsAt n := splitsAt_of_apply_lt_of_lt <|
  fun _ hi => piecewise_apply_of_lt (he := he) (hf := hf) _ hi ▸ he.apply_lt_of_lt _ hi

theorem piecewise_apply_fin {i : Fin n} : he.piecewise hf i = e i :=
  piecewise_apply_of_lt _ i.isLt

theorem piecewise_apply_add : he.piecewise hf (i + n) = f (i + n) :=
  piecewise_apply_of_ge _ (Nat.le_add_left  _ _)

@[simp]
theorem piecewise_self : he.piecewise he = e := Equiv.ext fun _ => ite_self _

theorem piecewise_one : splitsAt_one.piecewise splitsAt_one (n := n) = 1 := piecewise_self

@[simp] theorem piecewise_inv (he : e⁻¹.SplitsAt n) (hf : f⁻¹.SplitsAt n) :
    he.piecewise hf = (he.inv.piecewise hf.inv)⁻¹ := rfl

theorem inv_piecewise : (he.piecewise hf)⁻¹ = he.inv.piecewise hf.inv := rfl

@[simp] theorem piecewise_mul_piecewise : he.piecewise hf * he'.piecewise hf' =
    (he.mul he').piecewise (hf.mul hf') := Equiv.ext <| fun _ => by
  simp only [mul_apply, piecewise_apply, apply_ite (· < n), he'.apply_lt_iff_lt,
    hf'.apply_lt_iff_lt]; split_ifs <;> rfl

theorem piecewise_one_mul_piecewise_one :
    he.piecewise splitsAt_one * he'.piecewise splitsAt_one =
    (he.mul he').piecewise splitsAt_one := piecewise_mul_piecewise

theorem one_piecewise_mul_one_piecewise :
    splitsAt_one.piecewise he * splitsAt_one.piecewise he' =
    splitsAt_one.piecewise (he.mul he') := piecewise_mul_piecewise

@[simp] theorem piecewise_piecewise_left :
    (splitsAt_piecewise he he').piecewise hf = he.piecewise hf :=
  Equiv.ext <| fun _ => by simp_rw [piecewise_apply]; split_ifs <;> rfl

@[simp] theorem piecewise_piecewise_right :
    he.piecewise (splitsAt_piecewise he' hf)  = he.piecewise hf :=
  Equiv.ext <| fun _ => by simp_rw [piecewise_apply]; split_ifs <;> rfl

theorem piecewise_piecewise_piecewise :
    (splitsAt_piecewise he hf').piecewise
    (splitsAt_piecewise he' hf) = he.piecewise hf := by
  simp only [piecewise_piecewise_left, piecewise_piecewise_right]

theorem piecewise_piecewise_piecewise_self :
    (splitsAt_piecewise he hf').piecewise (splitsAt_piecewise he' he) = e := by
  simp only [piecewise_piecewise_piecewise, piecewise_self]

@[simps! apply_fst_coe_apply apply_snd_coe_apply symm_apply_fst_coe_apply symm_apply_snd_coe_apply]
def equivPiecewise (n : ℕ) : {e : Perm ℕ // e.SplitsAt n} × {e : Perm ℕ // e.SplitsAt n} ≃
    {e : Perm ℕ // e.SplitsAt n} × {e : Perm ℕ // e.SplitsAt n} where
  toFun := fun ⟨e, f⟩ => ⟨⟨_, splitsAt_piecewise e.2 f.2⟩, ⟨_, splitsAt_piecewise f.2 e.2⟩⟩
  invFun := fun ⟨e, f⟩ => ⟨⟨_, splitsAt_piecewise e.2 f.2⟩, ⟨_, splitsAt_piecewise f.2 e.2⟩⟩
  left_inv _ := by simp_rw [piecewise_piecewise_piecewise_self]
  right_inv _ := by simp_rw [piecewise_piecewise_piecewise_self]

end Piecewise

abbrev SplitsAt.permBelow {e : Perm ℕ} (he : e.SplitsAt n) : Perm ℕ := he.piecewise splitsAt_one
abbrev SplitsAt.permAbove {e : Perm ℕ} (he : e.SplitsAt n) : Perm ℕ := splitsAt_one.piecewise he

@[irreducible] def FixedLT (e : Perm ℕ) (n : ℕ) := ∀ i, i < n → e i = i

section FixedLT

variable {e : Perm ℕ}

theorem fixedLT_iff_apply_eq_self_of_lt : e.FixedLT n ↔ ∀ i, i < n → e i = i := by
  simp only [FixedLT]

instance : Decidable (e.FixedLT n) :=
  decidable_of_decidable_of_iff fixedLT_iff_apply_eq_self_of_lt.symm

@[simp] theorem FixedLT.apply_eq_self_of_lt (he : e.FixedLT n) : ∀ i, i < n → e i = i :=
  fixedLT_iff_apply_eq_self_of_lt.mp he

theorem fixedLT_of_apply_eq_self_of_lt (he : ∀ i, i < n → e i = i) : e.FixedLT n :=
  fixedLT_iff_apply_eq_self_of_lt.mpr he

theorem FixedLT.apply (h : e.FixedLT n) : e i = if i < n then i else e i := by
  rw [right_eq_ite_iff]
  exact h.apply_eq_self_of_lt _

@[simp] theorem FixedLT.splitsAt (h : e.FixedLT n) : e.SplitsAt n := by
  rw [fixedLT_iff_apply_eq_self_of_lt] at h
  apply splitsAt_of_apply_lt_of_lt
  exact fun i hi => Nat.lt_of_le_of_lt (Nat.le_of_eq (h _ hi)) hi

theorem fixedLT_one : FixedLT 1 n := fixedLT_of_apply_eq_self_of_lt (fun _ _ => rfl)

theorem FixedLT.inv (he : e.FixedLT n) : e⁻¹.FixedLT n := by
  simpa only [inv_eq_iff_eq, eq_comm (b := e _), fixedLT_iff_apply_eq_self_of_lt] using he

@[simp] theorem inv_fixedLT : e⁻¹.FixedLT n ↔ e.FixedLT n := ⟨FixedLT.inv, FixedLT.inv⟩

theorem FixedLT.mul (he : e.FixedLT n) (hf : f.FixedLT n) : (e * f).FixedLT n := by
  refine fixedLT_of_apply_eq_self_of_lt <| fun _ hi => ?_
  simp only [hi, mul_apply, he.apply_eq_self_of_lt, hf.apply_eq_self_of_lt]

@[simp] theorem fixedLT_zero : e.FixedLT 0 :=
  fixedLT_of_apply_eq_self_of_lt (fun _ h => (Nat.not_lt_zero _ h).elim)

theorem FixedLT.conj_fixedLT_of_splitsAt (he : e.FixedLT n) (hf : f.SplitsAt n) :
    (f * e * f⁻¹).FixedLT n := by
  simp_rw [fixedLT_iff_apply_eq_self_of_lt, mul_apply]
  intro i hi
  rw [he.apply_eq_self_of_lt _ (hf.inv.apply_lt_of_lt _ hi), apply_inv_self]

theorem SplitsAt.conj_fixedLT_of_fixedLT (he : e.FixedLT n) (hf : f.SplitsAt n) :
    (f * e * f⁻¹).FixedLT n := he.conj_fixedLT_of_splitsAt hf

@[simp] theorem fixedLT_one_piecewise {he : e.SplitsAt n} :
    (splitsAt_one.piecewise he).FixedLT n :=
  fixedLT_of_apply_eq_self_of_lt piecewise_apply_of_lt

@[simp] theorem FixedLT.piecewise_one (h : e.FixedLT n) :
    h.splitsAt.piecewise splitsAt_one = 1 := Equiv.ext <| fun _ => by
  rw [piecewise_apply, one_apply, h.apply]
  split_ifs <;> rfl

@[simp] theorem FixedLT.one_piecewise (h : e.FixedLT n) :
    splitsAt_one.piecewise h.splitsAt = e := Equiv.ext <| fun _ => by
  rw [piecewise_apply, one_apply, h.apply]
  split_ifs <;> rfl

end FixedLT

@[irreducible] def FixedGE (e : Perm ℕ) (n : ℕ) := ∀ i, n ≤ i → e i = i

section FixedGE

variable {e e' f f' : Perm ℕ}

theorem fixedGE_iff_apply_eq_self_of_ge : e.FixedGE n ↔ ∀ i, n ≤ i → e i = i := by
  simp only [FixedGE]

@[simp] theorem FixedGE.apply_eq_self_of_ge (he : e.FixedGE n) : ∀ i, n ≤ i → e i = i :=
  fixedGE_iff_apply_eq_self_of_ge.mp he

theorem fixedGE_of_apply_eq_self_of_ge (he : ∀ i, n ≤ i → e i = i) : e.FixedGE n :=
  fixedGE_iff_apply_eq_self_of_ge.mpr he

theorem FixedGE.apply (h : e.FixedGE n) : e i = if i < n then e i else i := by
  rw [left_eq_ite_iff]
  exact fun hi => h.apply_eq_self_of_ge _ (Nat.le_of_not_lt hi)

theorem FixedGE.splitsAt (h : e.FixedGE n) : e.SplitsAt n := by
  rw [fixedGE_iff_apply_eq_self_of_ge] at h
  apply splitsAt_of_apply_ge_of_ge
  exact fun i hi => Nat.le_trans hi (Nat.le_of_eq (h _ hi).symm)

theorem fixedGE_one : FixedGE 1 n := fixedGE_of_apply_eq_self_of_ge (fun _ _ => rfl)

theorem FixedGE.inv (he : e.FixedGE n) : e⁻¹.FixedGE n := by
  simpa only [inv_eq_iff_eq, eq_comm (b := e _), fixedGE_iff_apply_eq_self_of_ge] using he

@[simp] theorem inv_fixedGE : e⁻¹.FixedGE n ↔ e.FixedGE n := ⟨FixedGE.inv, FixedGE.inv⟩

theorem FixedGE.mul (he : e.FixedGE n) (hf : f.FixedGE n) : (e * f).FixedGE n := by
  refine fixedGE_of_apply_eq_self_of_ge <| fun _ hi => ?_
  simp only [hi, mul_apply, he.apply_eq_self_of_ge, hf.apply_eq_self_of_ge]

@[simp] theorem fixedGE_zero : e.FixedGE 0 ↔ e = 1 := by
  simp_rw [Equiv.ext_iff, one_apply, fixedGE_iff_apply_eq_self_of_ge, zero_le, true_implies]

theorem eq_one_of_fixedLT_of_fixedGE (he₁ : e.FixedLT n) (he₂ : e.FixedGE n) : e = 1 := by
  simp_rw [fixedLT_iff_apply_eq_self_of_lt] at he₁
  simp_rw [fixedGE_iff_apply_eq_self_of_ge] at he₂
  simp_rw [Equiv.ext_iff, one_apply]
  exact fun i => (Nat.lt_or_ge i n).by_cases (he₁ i) (he₂ i)

theorem FixedLT.eq_one_of_fixedGE (he₁ : e.FixedLT n) (he₂ : e.FixedGE n) : e = 1 :=
  eq_one_of_fixedLT_of_fixedGE he₁ he₂

theorem FixedGE.eq_one_of_fixedLT (he₁ : e.FixedLT n) (he₂ : e.FixedGE n) : e = 1 :=
  eq_one_of_fixedLT_of_fixedGE he₁ he₂

theorem fixedGE_fixedLT_iff_eq_one : e.FixedLT n ∧ e.FixedGE n ↔ e = 1 :=
  ⟨fun h => eq_one_of_fixedLT_of_fixedGE h.1 h.2, fun h => h ▸ ⟨fixedLT_one, fixedGE_one⟩⟩

theorem FixedGE.mul_fixedLT_apply (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f) i = if i < n then e i else f i := by
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [if_pos hi]
    exact congrArg e (hf.apply_eq_self_of_lt _ hi)
  · rw [if_neg hi.not_gt]
    exact he.apply_eq_self_of_ge _ (hf.splitsAt.apply_ge_of_ge _ hi)

theorem FixedGE.fixedLT_mul_apply (he : e.FixedGE n) (hf : f.FixedLT n) :
    (f * e) i = if i < n then e i else f i := by
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [if_pos hi]
    exact hf.apply_eq_self_of_lt _ (he.splitsAt.apply_lt_of_lt _ hi)
  · rw [if_neg hi.not_gt]
    exact congrArg f (he.apply_eq_self_of_ge _ hi)

theorem FixedLT.fixedGE_mul_apply (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f) i = if i < n then e i else f i := he.mul_fixedLT_apply hf

theorem FixedLT.mul_fixedGE_apply (he : e.FixedGE n) (hf : f.FixedLT n) :
    (f * e) i = if i < n then e i else f i := he.fixedLT_mul_apply hf

theorem FixedGE.commute_fixedLT (he : e.FixedGE n) (hf : f.FixedLT n) : Commute e f := by
  simp_rw [commute_iff_eq, Equiv.ext_iff, he.mul_fixedLT_apply hf,
    he.fixedLT_mul_apply hf, implies_true]

theorem FixedLT.commute_fixedGE (he : e.FixedGE n) (hf : f.FixedLT n) : Commute e f :=
  he.commute_fixedLT hf

theorem FixedGE.mul_mul_mul_comm (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e' * e) * (f * f') = (e' * f) * (e * f') :=
  Commute.mul_mul_mul_comm (he.commute_fixedLT hf) _ _

theorem FixedLT.mul_mul_mul_comm (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e' * e) * (f * f') = (e' * f) * (e * f') := he.mul_mul_mul_comm hf

theorem FixedGE.splitsAt_mul_of_fixedLT (he : e.FixedGE n) (hf : f.FixedLT n) :
  (e * f).SplitsAt n := he.splitsAt.mul hf.splitsAt

theorem FixedLT.splitsAt_mul_of_fixedLT (he : e.FixedGE n) (hf : f.FixedLT n) :
  (e * f).SplitsAt n := he.splitsAt_mul_of_fixedLT hf

theorem FixedGE.conj_fixedGE_of_splitsAt (he : e.FixedGE n) (hf : f.SplitsAt n) :
    (f * e * f⁻¹).FixedGE n := by
  simp_rw [fixedGE_iff_apply_eq_self_of_ge, mul_apply]
  intro i hi
  rw [he.apply_eq_self_of_ge _ (hf.inv.apply_ge_of_ge _ hi), apply_inv_self]

theorem SplitsAt.conj_fixedGE_of_fixedGE (he : e.FixedGE n) (hf : f.SplitsAt n) :
    (f * e * f⁻¹).FixedGE n := he.conj_fixedGE_of_splitsAt hf

@[simp] theorem fixedGE_piecewise_one {he : e.SplitsAt n} :
    (he.piecewise splitsAt_one).FixedGE n :=
  fixedGE_of_apply_eq_self_of_ge piecewise_apply_of_ge

@[simp] theorem FixedGE.piecewise_one (h : e.FixedGE n) :
    h.splitsAt.piecewise splitsAt_one = e := Equiv.ext <| fun _ => by
  rw [piecewise_apply, one_apply, h.apply]
  split_ifs <;> rfl

@[simp] theorem FixedGE.one_piecewise (h : e.FixedGE n) :
    splitsAt_one.piecewise h.splitsAt = 1 := Equiv.ext <| fun _ => by
  rw [piecewise_apply, one_apply, h.apply]
  split_ifs <;> rfl

theorem piecewise_fixedGE_fixedLT (e : Perm ℕ) (f : Perm ℕ) (he : e.FixedGE n) (hf : f.FixedLT n) :
    he.splitsAt.piecewise hf.splitsAt = e * f := Equiv.ext <| fun i => by
  rw [piecewise_apply, mul_apply, he.apply (i := f i)]
  simp_rw [hf.splitsAt.apply_lt_iff_lt]
  exact ite_congr rfl (fun hi => congrArg _ (hf.apply_eq_self_of_lt _ hi).symm) (fun _ => rfl)

end FixedGE

theorem SplitsAt.exists_fixedGE_fixed_LT_piecewise_eq {g : Perm ℕ} (hg : g.SplitsAt n) :
    ∃ (e : Perm ℕ) (f : Perm ℕ) (he : e.FixedGE n) (hf : f.FixedLT n),
    he.splitsAt.piecewise hf.splitsAt = g :=
  ⟨hg.piecewise splitsAt_one, splitsAt_one.piecewise hg,
    fixedGE_piecewise_one, fixedLT_one_piecewise, piecewise_piecewise_piecewise_self⟩

theorem SplitsAt.exists_fixedGE_fixed_LT_mul_eq {g : Perm ℕ} (hg : g.SplitsAt n) :
    ∃ e f, e.FixedGE n ∧ f.FixedLT n ∧ e * f = g :=
  ⟨hg.piecewise splitsAt_one, splitsAt_one.piecewise hg,
    fixedGE_piecewise_one, fixedLT_one_piecewise, by
      simp_rw [piecewise_mul_piecewise, mul_one, one_mul, piecewise_self]⟩

theorem splitsAt_iff_exists_fixedGE_fixed_LT_mul_eq {g : Perm ℕ} :
    g.SplitsAt n ↔ ∃ e f, e.FixedGE n ∧ f.FixedLT n ∧ e * f = g  :=
  ⟨fun he => he.exists_fixedGE_fixed_LT_mul_eq,
    fun ⟨_, _, he, hf, h_eq⟩ => h_eq ▸ he.splitsAt_mul_of_fixedLT hf⟩

def equivProdFixedSplitsAt (n : ℕ) : {e : Perm ℕ // e.SplitsAt n} ≃
    {e : Perm ℕ // e.FixedGE n} × {e : Perm ℕ // e.FixedLT n} where
  toFun e := ⟨⟨e.2.piecewise splitsAt_one, fixedGE_piecewise_one⟩,
    ⟨splitsAt_one.piecewise e.2, fixedLT_one_piecewise⟩⟩
  invFun := fun ⟨e, f⟩ => ⟨e.prop.splitsAt.piecewise f.prop.splitsAt,
    splitsAt_piecewise _ _⟩
  left_inv e := by simp_rw [piecewise_piecewise_piecewise_self]
  right_inv := fun ⟨e, f⟩ => by
    simp only [piecewise_piecewise_left, piecewise_piecewise_right,
      e.2, f.prop, FixedGE.piecewise_one, FixedLT.one_piecewise]

@[simps]
def natPerm (e : Perm (Fin n)) : Perm ℕ where
  toFun i := if hi : i < n then e ⟨i, hi⟩ else i
  invFun i := if hi : i < n then e⁻¹ ⟨i, hi⟩ else i
  left_inv i := by by_cases hi : i < n <;> simp [hi]
  right_inv i := by by_cases hi : i < n <;> simp [hi]

@[simps]
def finPerm (e : Perm ℕ) (he : e.SplitsAt n) : Perm (Fin n) where
  toFun := fun ⟨i, hi⟩ => ⟨e i, he.apply_lt_of_lt i hi⟩
  invFun := fun ⟨i, hi⟩ => ⟨e⁻¹ i, he.inv.apply_lt_of_lt i hi⟩
  left_inv := fun ⟨i, _⟩ => Fin.ext <| e.symm_apply_apply i
  right_inv := fun ⟨i, _⟩ => Fin.ext <| e.apply_symm_apply i

@[simps]
def equivFixedGE (n : ℕ) : {e : Perm ℕ // e.FixedGE n} ≃ Perm (Fin n) where
  toFun e := finPerm e.1 e.2.splitsAt
  invFun e := ⟨e.natPerm, fixedGE_of_apply_eq_self_of_ge
    fun _ hi => dif_neg (Nat.not_lt_of_ge hi)⟩
  left_inv e := Subtype.ext <| Equiv.ext fun i => by
    simp_rw [natPerm_apply, finPerm_apply_val, dite_eq_ite, ite_eq_left_iff, not_lt]
    exact fun hi => (e.2.apply_eq_self_of_ge _ hi).symm
  right_inv e := Equiv.ext fun i => Fin.ext <| by
    simp_rw [finPerm_apply_val, natPerm_apply, dif_pos i.is_lt]

@[simps]
def upperPerm (e : Perm ℕ) (h : e.SplitsAt n) : Perm ℕ where
  toFun i := e (i + n) - n
  invFun i := e⁻¹ (i + n) - n
  left_inv i := by
    have h := (h.apply_ge_iff_ge (i + n)).mpr (Nat.le_add_left _ _)
    rcases Nat.exists_eq_add_of_le' h with ⟨k, hk⟩
    simp_rw [hk, Nat.add_sub_cancel, ← hk, inv_apply_self, Nat.add_sub_cancel]
  right_inv i := by
    rw [← inv_splitsAt] at h
    have h := (h.apply_ge_iff_ge (i + n)).mpr (Nat.le_add_left _ _)
    rcases Nat.exists_eq_add_of_le' h with ⟨k, hk⟩
    simp_rw [hk, Nat.add_sub_cancel, ← hk, apply_inv_self, Nat.add_sub_cancel]

@[simps]
def permShift (e : Perm ℕ) (n : ℕ) : Perm ℕ where
  toFun i := if i < n then i else e (i - n) + n
  invFun i := if i < n then i else e⁻¹ (i - n) + n
  left_inv i := by by_cases hi : i < n <;> simp [hi, Nat.ge_of_not_lt]
  right_inv i := by by_cases hi : i < n <;> simp [hi, Nat.ge_of_not_lt]

@[simps]
def equivFixedLT (n : ℕ) : {e : Perm ℕ // e.FixedLT n} ≃ Perm ℕ where
  toFun e := upperPerm e.1 e.2.splitsAt
  invFun e := ⟨e.permShift n, fixedLT_of_apply_eq_self_of_lt
    fun _ hi => dif_pos hi⟩
  left_inv e := Subtype.ext <| Equiv.ext fun i => by
    rw [permShift_apply, upperPerm_apply, e.2.apply (i := i)]
    refine ite_congr rfl (fun _ => rfl) (fun hi => ?_)
    rw [Nat.sub_add_cancel (Nat.ge_of_not_lt hi),
      Nat.sub_add_cancel (e.2.splitsAt.apply_ge_of_ge _ (Nat.ge_of_not_lt hi))]
  right_inv e := Equiv.ext fun i => by
    simp_rw [upperPerm_apply, permShift_apply, Nat.add_sub_cancel, Nat.add_lt_iff_lt_sub_right,
      Nat.sub_self, Nat.not_lt_zero, if_false, Nat.add_sub_cancel]

/-


section PermBelow

variable {e f : Perm ℕ}

theorem finPerm_one : finPerm (n := n) 1 splitsAt_one = 1 := Equiv.ext <| fun _ => rfl

theorem SplitsAt.finPerm_inv (he : e⁻¹.SplitsAt n) :
    e⁻¹.finPerm he = (e.finPerm he.inv)⁻¹ := rfl

@[simp] theorem SplitsAt.inv_finPerm (he : e.SplitsAt n) :
    (e.finPerm he)⁻¹ = e⁻¹.finPerm he.inv := rfl

@[simp] theorem SplitsAt.finPerm_mul (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    finPerm (e * f) (he.mul hf) = finPerm e he * finPerm f hf := Equiv.ext <| fun _ => rfl

end PermBelow



section PermAbove

variable {e f : Perm ℕ}

theorem upperPerm_one : upperPerm (n := n) 1 splitsAt_one = 1 := Equiv.ext <| fun _ => by
  simp_rw [upperPerm_apply, one_apply, Nat.add_sub_cancel]

theorem SplitsAt.upperPerm_inv (he : e⁻¹.SplitsAt n) :
    e⁻¹.upperPerm he = (e.upperPerm he.inv)⁻¹ := rfl

@[simp] theorem SplitsAt.inv_upperPerm (he : e.SplitsAt n) :
      (e.upperPerm he)⁻¹ = e⁻¹.upperPerm he.inv := rfl

@[simp] theorem SplitsAt.upperPerm_mul (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    (e * f).upperPerm (he.mul hf) = e.upperPerm he * f.upperPerm hf := Equiv.ext <| fun _ => by
  simp only [mul_apply, upperPerm_apply,
    Nat.sub_add_cancel (hf.apply_ge_of_ge _ (Nat.le_add_left _ _))]

end PermAbove

def natPerm (e : Perm (Fin n)) : Perm ℕ where
  toFun i := if hi : i < n then e ⟨i, hi⟩ else i
  invFun i := if hi : i < n then e⁻¹ ⟨i, hi⟩ else i
  left_inv i := by by_cases hi : i < n <;> simp [hi]
  right_inv i := by by_cases hi : i < n <;> simp [hi]

section NatPerm

variable {e f : Perm (Fin n)}

theorem natPerm_apply : e.natPerm i = if hi : i < n then ↑(e ⟨i, hi⟩) else i := rfl

@[simp] theorem natPerm_apply_of_lt : ∀ i, (hi : i < n) → e.natPerm i = e ⟨i, hi⟩ :=
  fun _ hi => dif_pos hi

@[simp] theorem natPerm_apply_of_ge : ∀ i, n ≤ i → e.natPerm i = i :=
  fun _ hi => dif_neg (Nat.not_lt_of_ge hi)

theorem natPerm_apply_fin {i : Fin n} : e.natPerm i = e i := natPerm_apply_of_lt _ i.isLt

theorem natPerm_apply_add : e.natPerm (i + n) = i + n := natPerm_apply_of_ge _ (Nat.le_add_left _ _)

theorem natPerm_one : natPerm (n := n) 1 = 1 := Equiv.ext <| fun _ => ite_self _

@[simp] theorem inv_natPerm : e.natPerm⁻¹ = e⁻¹.natPerm := rfl

theorem natPerm_inv : e⁻¹.natPerm = e.natPerm⁻¹ := rfl

@[simp] theorem natPerm_mul : (e * f).natPerm = e.natPerm * f.natPerm := Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi <;>
  simp  [hi, natPerm_apply_of_lt, mul_apply]

theorem fixedGE_natPerm : e.natPerm.FixedGE n :=
  fixedGE_of_apply_eq_self_of_ge natPerm_apply_of_ge

theorem splitsAt_natPerm : e.natPerm.SplitsAt n := fixedGE_natPerm.splitsAt

@[simp] theorem finPerm_natPerm {e : Perm (Fin n)}  :
    e.natPerm.finPerm splitsAt_natPerm = e := Equiv.ext <|
  fun i => Fin.ext <| by simp_rw [finPerm_apply_val, natPerm_apply_fin]

@[simp] theorem upperPerm_natPerm :
    e.natPerm.upperPerm splitsAt_permShift (n := n) = 1 := Equiv.ext <|
  fun i => by simp_rw [upperPerm_apply, natPerm_apply_add, one_apply, Nat.add_sub_cancel]

end NatPerm

def permShift (e : Perm ℕ) (n : ℕ) : Perm ℕ where
  toFun i := if n ≤ i then e (i - n) + n else i
  invFun i := if n ≤ i then e⁻¹ (i - n) + n else i
  left_inv i := by by_cases hi : n ≤ i <;> simp [hi]
  right_inv i := by by_cases hi : n ≤ i <;> simp [hi]

section PermShift

variable {e f g : Perm ℕ}

theorem permShift_apply : e.permShift n i = if n ≤ i then e (i - n) + n else i := rfl

@[simp] theorem permShift_apply_of_lt : ∀ i, (hi : i < n) → e.permShift n i = i :=
  fun _ hi => dif_neg (Nat.not_le_of_gt hi)

@[simp] theorem permShift_apply_of_ge : ∀ i, n ≤ i → e.permShift n i = e (i - n) + n :=
  fun _ hi => dif_pos hi

theorem permShift_apply_fin {i : Fin n} : e.permShift n i = i := by
  simp_rw [permShift_apply_of_lt _ i.isLt]

theorem permShift_apply_add : e.permShift n (i + n) = e i + n := by
  simp_rw [permShift_apply_of_ge _ (Nat.le_add_left _ _), Nat.add_sub_cancel]

theorem permShift_one : permShift 1 n = 1 := Equiv.ext <| fun _ => by
  simp_rw [permShift_apply, one_apply, ite_eq_right_iff]
  exact Nat.sub_add_cancel

@[simp] theorem inv_permShift : (e.permShift n)⁻¹ = e⁻¹.permShift n := rfl

theorem permShift_inv : e⁻¹.permShift n = (e.permShift n)⁻¹ := rfl

@[simp] theorem permShift_mul : (e * f).permShift n = e.permShift n * f.permShift n :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi
  · simp only [hi, mul_apply, permShift_apply_of_lt]
  · simp only [hi, permShift_apply_of_ge, mul_apply, permShift_apply_add]

theorem fixedLT_permShift : (e.permShift n).FixedLT n :=
  fixedLT_of_apply_eq_self_of_lt permShift_apply_of_lt

theorem splitsAt_permShift : (e.permShift n).SplitsAt n := fixedLT_permShift.splitsAt

theorem commutes_natPerm_permShift {e : Perm (Fin n)} :
    e.natPerm * f.permShift n = f.permShift n * e.natPerm :=
  fixedGE_natPerm.commute_fixedLT fixedLT_permShift

@[simp] theorem finPerm_permShift :
    (e.permShift n).finPerm splitsAt_permShift = 1 := Equiv.ext <|
  fun i => Fin.ext <| by simp_rw [finPerm_apply_val, permShift_apply_fin, one_apply]

@[simp] theorem upperPerm_permShift :
    (e.permShift n).upperPerm splitsAt_permShift = e := Equiv.ext <|
  fun i => by simp_rw [upperPerm_apply, permShift_apply_add, Nat.add_sub_cancel]

end PermShift

def permPieces (e : Perm (Fin n)) (f : Perm ℕ) : Perm ℕ where
  toFun i := if hi : i < n then e ⟨i, hi⟩ else f (i - n) + n
  invFun i := if hi : i < n then e⁻¹ ⟨i, hi⟩ else f⁻¹ (i - n) + n
  left_inv i := by
    by_cases hi : i < n <;> simp [hi]
    exact Nat.sub_add_cancel (Nat.le_of_not_lt hi)
  right_inv i := by
    by_cases hi : i < n <;> simp [hi]
    exact Nat.sub_add_cancel (Nat.le_of_not_lt hi)

section PermPieces

variable {e e' : Perm (Fin n)} {f f' : Perm ℕ}

theorem permPieces_apply : e.permPieces f i = if i < n then ↑(e ⟨i, hi⟩) else f (i - n) + n := rfl

@[simp] theorem permPieces_apply_of_lt : ∀ i, (hi : i < n) → e.permPieces f i = e ⟨i, hi⟩ :=
  fun _ hi => dif_pos hi

@[simp] theorem permPieces_apply_of_ge : ∀ i, n ≤ i → e.permPieces f i = f (i - n) + n :=
  fun _ hi => dif_neg (Nat.not_lt_of_le hi)

theorem permPieces_apply_add : e.permPieces f (i + n) = f i + n := by
  simp_rw [permPieces_apply_of_ge _ (Nat.le_add_left _ _), Nat.add_sub_cancel]

theorem permPieces_apply_fin {i : Fin n} : e.permPieces f i = e i := by
  simp_rw [permPieces_apply_of_lt _ i.isLt]

theorem permPieces_eq_natPerm_mul_permShift : e.permPieces f = e.natPerm * f.permShift n :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi
  · simp only [hi, permPieces_apply_of_lt, mul_apply, permShift_apply_of_lt,
    natPerm_apply_of_lt]
  · simp only [hi, permPieces_apply_of_ge, mul_apply, permShift_apply_of_ge,
      natPerm_apply_of_ge, Nat.le_add_left]

theorem permPieces_eq_permShift_mul_natPerm : e.permPieces f = f.permShift n * e.natPerm := by
  rw [permPieces_eq_natPerm_mul_permShift, commutes_natPerm_permShift]

theorem permPieces_one_left : permPieces (1 : Perm (Fin n)) f = f.permShift n := by
  simp_rw [permPieces_eq_natPerm_mul_permShift, natPerm_one, one_mul]

theorem permPieces_one_right : permPieces e 1 = e.natPerm := by
  simp_rw [permPieces_eq_natPerm_mul_permShift, permShift_one, mul_one]

theorem permPieces_one : permPieces (1 : Perm (Fin n)) 1 = 1 := by
  simp_rw [permPieces_one_left, permShift_one]

theorem permPieces_inv : e⁻¹.permPieces f⁻¹ = (e.permPieces f)⁻¹ := rfl
@[simp] theorem inv_permPieces : (e.permPieces f)⁻¹ = e⁻¹.permPieces f⁻¹ := rfl

theorem permPieces_mul : permPieces (e * e') (f  * f') = e.permPieces f * e'.permPieces f' := by
  simp_rw [permPieces_eq_natPerm_mul_permShift, natPerm_mul, permShift_mul]
  exact fixedGE_natPerm.mul_mul_mul_comm fixedLT_permShift

theorem permPieces_mul_left_right : permPieces (e * e') f = e.natPerm * e'.permPieces f := by
  simp_rw [← permPieces_one_right, ← permPieces_mul, one_mul]

theorem permPieces_mul_left_left : permPieces (e * e') f = e.permPieces f * e'.natPerm := by
  simp_rw [← permPieces_one_right, ← permPieces_mul, mul_one]

theorem permPieces_mul_right_left : permPieces e (f * f') = e.permPieces f * f'.permShift n := by
  simp_rw [← permPieces_one_left, ← permPieces_mul, mul_one]

theorem permPieces_mul_right_right : permPieces e (f * f') = f.permShift n * e.permPieces f' := by
  simp_rw [← permPieces_one_left, ← permPieces_mul, one_mul]

theorem splitsAt_permPieces : (e.permPieces f).SplitsAt n := by
  rw [permPieces_eq_natPerm_mul_permShift]
  exact splitsAt_natPerm.mul splitsAt_permShift

@[simp] theorem finPerm_permPieces :
    (e.permPieces f).finPerm splitsAt_permPieces = e := by
  simp_rw [permPieces_eq_natPerm_mul_permShift,
    splitsAt_natPerm.finPerm_mul splitsAt_permShift,
    finPerm_natPerm, finPerm_permShift, mul_one]

@[simp] theorem upperPerm_permPieces :
    (e.permPieces f).upperPerm splitsAt_permPieces = f := by
  simp_rw [permPieces_eq_natPerm_mul_permShift,
    splitsAt_natPerm.upperPerm_mul splitsAt_permShift,
    upperPerm_natPerm, upperPerm_permShift, one_mul]

end PermPieces

def permBelow (e : Perm ℕ) (he : e.SplitsAt n) := (e.finPerm he).natPerm

section PermBelow

variable {e f : Perm ℕ} {he : e.SplitsAt n} {hf : f.SplitsAt n}

namespace SplitsAt

@[simp] theorem natPerm_finPerm : (e.finPerm he).natPerm i = he.permBelow i := rfl

theorem permBelow_apply : he.permBelow i = if i < n then e i else i := rfl

@[simp] theorem permBelow_apply_of_lt : ∀ i, i < n → he.permBelow i = e i :=
  natPerm_apply_of_lt

@[simp] theorem permBelow_apply_of_ge : ∀ i, n ≤ i → he.permBelow i = i :=
  natPerm_apply_of_ge

theorem permBelow_apply_fin {i : Fin n} : he.permBelow i = e i := natPerm_apply_fin

theorem permBelow_apply_add : he.permBelow (i + n) = i + n := natPerm_apply_add

theorem permBelow_one : permBelow (n := n) 1 splitsAt_one = 1 := natPerm_one

@[simp] theorem inv_permBelow : (he.permBelow)⁻¹ = e⁻¹.permBelow he.inv := inv_natPerm

theorem permBelow_inv (he : e⁻¹.SplitsAt n) : e⁻¹.permBelow he = (he.permBelow.inv)⁻¹ := rfl

@[simp] theorem permBelow_mul (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    (e * f).permBelow (he.mul hf) = he.permBelow * f.permBelow hf := by
  unfold permBelow
  simp only [he, hf, finPerm_mul, natPerm_mul]

@[simp] theorem fixedGE_permBelow : (he.permBelow).FixedGE n := fixedGE_natPerm

@[simp] theorem splitsAt_permBelow : (he.permBelow).SplitsAt n := fixedGE_natPerm.splitsAt

@[simp] theorem finPerm_permBelow : (he.permBelow).finPerm he.splitsAt_permBelow = e.finPerm he :=
  finPerm_natPerm

@[simp] theorem upperPerm_permBelow : (he.permBelow).upperPerm he.splitsAt_permBelow = 1 :=
  upperPerm_natPerm

end SplitsAt

@[simp] theorem FixedGE.permBelow (he : e.FixedGE n) : he.permBelow.splitsAt = e :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi <;> simp [hi, he.apply_eq_self_of_ge]

@[simp] theorem SplitsAt.permBelow_permBelow (he : e.SplitsAt n) :
    (he.permBelow).permBelow he.splitsAt_permBelow = he.permBelow :=
  he.fixedGE_permBelow.permBelow

@[simp] theorem FixedLT.permBelow (he : e.FixedLT n) : he.permBelow.splitsAt = 1 :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi <;> simp [hi, he.apply_eq_self_of_lt]

@[simp] theorem FixedGE.permBelow_mul (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f).permBelow (he.splitsAt_mul_of_fixedLT hf) = e := by
  rw [he.splitsAt.permBelow_mul hf.splitsAt, hf.permBelow, he.permBelow, mul_one]

@[simp] theorem FixedLT.permBelow_mul (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f).permBelow (he.splitsAt_mul_of_fixedLT hf) = e := he.permBelow_mul hf

end PermBelow

def permAbove (e : Perm ℕ) (he : e.SplitsAt n) := (e.upperPerm he).permShift n

section PermAbove

variable {e f g : Perm ℕ}

namespace SplitsAt

variable {he : e.SplitsAt n} {hf : f.SplitsAt n}

@[simp] theorem permShift_upperPerm : (e.upperPerm he).permShift n i = e.permAbove he i := rfl

theorem permAbove_apply : e.permAbove he i = if n ≤ i then e i else i := by
  unfold permAbove
  rw [permShift_apply, upperPerm_apply]
  split_ifs with hi
  · simp [hi, he.apply_ge_of_ge]
  · rfl

@[simp] theorem permAbove_apply_of_lt : ∀ i, i < n → e.permAbove he i = i :=
  permShift_apply_of_lt

@[simp] theorem permAbove_apply_of_ge : ∀ i, n ≤ i → e.permAbove he i = e i := by
  simp_rw [permAbove_apply, ite_eq_left_iff]
  exact fun _ hi hi' => (hi' hi).elim

theorem permAbove_apply_fin {i : Fin n} : e.permAbove he i = i := permShift_apply_fin

theorem permAbove_apply_add : e.permAbove he (i + n) = e (i + n) :=
  he.permAbove_apply_of_ge (i + n) (Nat.le_add_left _ _)

theorem permAbove_one : permAbove (n := n) 1 splitsAt_one = 1 := Equiv.ext <| fun _ => by
  simp_rw [permAbove_apply, one_apply, ite_self]

@[simp] theorem inv_permAbove : (e.permAbove he)⁻¹ = e⁻¹.permAbove he.inv := rfl

theorem permAbove_inv (he : e⁻¹.SplitsAt n) : e⁻¹.permBelow he = (he.permBelow.inv)⁻¹ := rfl

@[simp] theorem permAbove_mul (he : e.SplitsAt n) (hf : f.SplitsAt n) :
    (e * f).permAbove (he.mul hf) = e.permAbove he * f.permAbove hf := by
  unfold permAbove
  simp only [he, hf, upperPerm_mul, permShift_mul]

@[simp] theorem fixedLT_permAbove : (e.permAbove he).FixedLT n := fixedLT_permShift

@[simp] theorem splitsAt_permAbove : (e.permAbove he).SplitsAt n := he.fixedLT_permAbove.splitsAt

@[simp] theorem finPerm_permAbove : (e.permAbove he).finPerm he.splitsAt_permAbove = 1 :=
  finPerm_permShift

@[simp] theorem upperPerm_permAbove : (e.permAbove he).upperPerm he.splitsAt_permAbove =
    e.upperPerm he := upperPerm_permShift

end SplitsAt


@[simp] theorem FixedLT.permAbove (he : e.FixedLT n) : e.permAbove he.splitsAt = e :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi <;> simp [hi, he.apply_eq_self_of_lt]

@[simp] theorem FixedGE.permAbove (he : e.FixedGE n) : e.permAbove he.splitsAt = 1 :=
    Equiv.ext <| fun i => by
  rcases Nat.lt_or_ge i n with hi | hi <;> simp [hi, he.apply_eq_self_of_ge]

@[simp] theorem FixedGE.permAbove_mul (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f).permAbove (he.splitsAt_mul_of_fixedLT hf) = f := by
  rw [he.splitsAt.permAbove_mul hf.splitsAt, hf.permAbove, he.permAbove, one_mul]

@[simp] theorem FixedLT.permAbove_mul (he : e.FixedGE n) (hf : f.FixedLT n) :
    (e * f).permAbove (he.splitsAt_mul_of_fixedLT hf) = f := he.permAbove_mul hf

@[simp] theorem SplitsAt.permAbove_permAbove {he : e.SplitsAt n} :
    (e.permAbove he).permAbove he.splitsAt_permAbove = e.permAbove he :=
  he.fixedLT_permAbove.permAbove

@[simp] theorem SplitsAt.permAbove_permBelow {he : e.SplitsAt n} :
    (he.permBelow).permAbove he.splitsAt_permBelow = 1 :=
  he.fixedGE_permBelow.permAbove

@[simp] theorem SplitsAt.permBelow_permAbove {he : e.SplitsAt n} :
    (e.permAbove he).permBelow he.splitsAt_permAbove = 1 :=
  he.fixedLT_permAbove.permBelow

theorem SplitsAt.permBelow_mul_permAbove {he : e.SplitsAt n} :
    he.permBelow * e.permAbove he = e := Equiv.ext <| fun i => by
  rw [mul_apply]
  rcases Nat.lt_or_ge i n with hi | hi
  · simp only [hi, permBelow_apply_of_lt, permAbove_apply_of_lt]
  · simp only [hi, permBelow_apply_of_ge, permAbove_apply_of_ge, he.apply_ge_of_ge]

theorem SplitsAt.permPieces_finPerm_upperPerm {e : Perm ℕ} {he : e.SplitsAt n} :
    (e.finPerm he).permPieces (e.upperPerm he) = e := by
  rw [permPieces_eq_natPerm_mul_permShift]
  exact he.permBelow_mul_permAbove

end PermAbove

section

@[simps! apply_coe symm_apply]
def equivFixedGE (n : ℕ) : Perm (Fin n) ≃ {e : Perm ℕ // e.FixedGE n} where
  toFun e := ⟨e.natPerm, fixedGE_natPerm⟩
  invFun e := finPerm e.1 e.2.splitsAt
  left_inv _ := finPerm_natPerm
  right_inv e := Subtype.ext e.2.permBelow

@[simps! apply_coe symm_apply]
def equivFixedLT (n : ℕ) : Perm ℕ ≃ {e : Perm ℕ // e.FixedLT n} where
  toFun e := ⟨e.permShift n, fixedLT_permShift⟩
  invFun e := upperPerm e.1 e.2.splitsAt
  left_inv _ := upperPerm_permShift
  right_inv e := Subtype.ext e.2.permAbove

@[simps! apply_coe symm_apply]
def equivSplitsAt (n : ℕ) : Perm (Fin n) × Perm ℕ ≃ {e : Perm ℕ // e.SplitsAt n} where
  toFun ef := ⟨ef.fst.permPieces ef.snd, splitsAt_permPieces⟩
  invFun e := (e.1.finPerm e.2, e.1.upperPerm e.2)
  left_inv _ := Prod.ext finPerm_permPieces upperPerm_permPieces
  right_inv e := Subtype.ext e.2.permPieces_finPerm_upperPerm

@[simps! apply_coe symm_apply]
def equivProdFixedSplitsAt (n : ℕ) : {e : Perm ℕ // e.FixedGE n} × {e : Perm ℕ // e.FixedLT n} ≃
    {e : Perm ℕ // e.SplitsAt n} where
  toFun ef := ⟨ef.1 * ef.2, ef.1.2.splitsAt_mul_of_fixedLT ef.2.2⟩
  invFun e :=
    ⟨⟨e.1.permBelow e.2, e.2.fixedGE_permBelow⟩, ⟨e.1.permAbove e.2, e.2.fixedLT_permAbove⟩⟩
  left_inv ef := Prod.ext
    (Subtype.ext <| ef.1.2.permBelow_mul ef.2.2) (Subtype.ext <| ef.1.2.permAbove_mul ef.2.2)
  right_inv e := Subtype.ext <| e.2.permBelow_mul_permAbove

theorem card_fixedGE : Nat.card {e : Perm ℕ // e.FixedGE n} = n.factorial :=
  (Nat.card_congr (equivFixedGE n).symm).trans <| by rw [Nat.card_perm, Nat.card_fin]

end
-/

end Equiv.Perm


namespace Subgroup

open Equiv Equiv.Perm

variable {e f g : Perm ℕ}

@[simps]
def splitsAt (n : ℕ) : Subgroup (Perm ℕ) where
  carrier := {e | e.SplitsAt n}
  mul_mem' he hf := he.mul hf
  one_mem' := splitsAt_one
  inv_mem' he := he.inv

@[simp] theorem mem_splitsAt_iff : e ∈ splitsAt n ↔ e.SplitsAt n := Iff.rfl

instance : Decidable (e ∈ splitsAt n) := decidable_of_decidable_of_iff mem_splitsAt_iff.symm

@[simps]
def fixedGE (n : ℕ) : Subgroup (Perm ℕ) where
  carrier := {e | e.FixedGE n}
  mul_mem' ha hb := ha.mul hb
  one_mem' := fixedGE_one
  inv_mem' he := he.inv

@[simp] theorem mem_fixedGE_iff : e ∈ fixedGE n ↔ e.FixedGE n := Iff.rfl

theorem card_fixedGE : Nat.card (fixedGE n) = n.factorial := Perm.card_fixedGE

@[simps]
def fixedLT (n : ℕ) : Subgroup (Perm ℕ) where
  carrier := {e | e.FixedLT n}
  mul_mem' ha hb := ha.mul hb
  one_mem' := fixedLT_one
  inv_mem' he := he.inv

@[simp] theorem mem_fixedLT_iff : e ∈ fixedLT n ↔ e.FixedLT n := Iff.rfl

instance : Decidable (e ∈ fixedLT n) := decidable_of_decidable_of_iff mem_fixedLT_iff.symm

theorem fixedGE_le_splitsAt : fixedGE n ≤ splitsAt n := by
  simp_rw [SetLike.le_def, mem_fixedGE_iff, mem_splitsAt_iff]
  exact fun _ he => he.splitsAt

theorem fixedLT_le_splitsAt : fixedLT n ≤ splitsAt n := by
  simp_rw [SetLike.le_def, mem_fixedLT_iff, mem_splitsAt_iff]
  exact fun _ he => he.splitsAt

theorem normal_subgroupOf_fixedGE_splitsAt :
    ((fixedGE n).subgroupOf (splitsAt n)).Normal := by
  simp_rw [normal_subgroupOf_iff fixedGE_le_splitsAt, mem_splitsAt_iff, mem_fixedGE_iff]
  exact fun _ _ => FixedGE.conj_fixedGE_of_splitsAt

theorem normal_subgroupOf_fixedLT_splitsAt :
    ((fixedLT n).subgroupOf (splitsAt n)).Normal := by
  simp_rw [normal_subgroupOf_iff fixedLT_le_splitsAt, mem_splitsAt_iff, mem_fixedLT_iff]
  exact fun _ _ => FixedLT.conj_fixedLT_of_splitsAt

theorem commute_fixedGE_fixedLT (he : e ∈ fixedGE n) (hf : f ∈ fixedLT n) : e * f = f * e := by
  rw [mem_fixedGE_iff] at he
  rw [mem_fixedLT_iff] at hf
  exact he.commute_fixedLT hf

theorem disjoint_fixedGE_fixedLT : Disjoint (fixedLT n) (fixedGE n) := by
  simp_rw [Subgroup.disjoint_def, mem_fixedGE_iff, mem_fixedLT_iff]
  exact fun {_} => eq_one_of_fixedLT_of_fixedGE

theorem mem_splitsAt_iff_exists_mem_fixedGE_mem_fixed_LT_mul_eq :
    g ∈ splitsAt n ↔ ∃ e f, e ∈ fixedGE n ∧ f ∈ fixedLT n ∧ e * f = g :=
  Perm.splitsAt_iff_exists_fixedGE_fixed_LT_mul_eq

theorem sup_fixedGE_fixedLT : fixedGE n ⊔ fixedLT n = splitsAt n := by
  refine le_antisymm (sup_le fixedGE_le_splitsAt fixedLT_le_splitsAt) fun x => ?_
  simp only [mem_splitsAt_iff_exists_mem_fixedGE_mem_fixed_LT_mul_eq,
    exists_and_left, forall_exists_index, and_imp]
  exact fun _ he _ hf h => h ▸ mul_mem_sup he hf

theorem fixedGE_zero : fixedGE 0 = ⊥ := by
  simp_rw [Subgroup.eq_bot_iff_forall, mem_fixedGE_iff, Perm.fixedGE_zero, imp_self, implies_true]

theorem fixedLT_zero : fixedLT 0 = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixedLT_iff, Perm.fixedLT_zero, implies_true]

theorem splitsAt_zero : splitsAt 0 = ⊤ := by
  rw [←  sup_fixedGE_fixedLT, fixedGE_zero, fixedLT_zero, bot_sup_eq]

/-
@[simps! apply_coe symm_apply]
def mulEquivFixedGE (n : ℕ) : Perm (Fin n) ≃* fixedGE n :=
  { equivFixedGE n with map_mul' _ _ := Subtype.ext <| natPerm_mul }

@[simps! apply_coe symm_apply]
def mulEquivFixedLT (n : ℕ) : Perm ℕ ≃* fixedLT n :=
  { equivFixedLT n with map_mul' _ _ := Subtype.ext <| permShift_mul }

-/

@[simps! apply symm_apply_coe]
def mulEquivProdFixedSplitsAt (n : ℕ) : splitsAt n ≃* fixedGE n × fixedLT n :=
  { equivProdFixedSplitsAt n with
    toFun e := ⟨⟨e.2.piecewise splitsAt_one, _⟩, ⟨splitsAt_one.piecewise e.2, _⟩⟩
    map_mul' e f := by
      simp only [Prod.ext_iff, Subtype.ext_iff, coe_mul, Prod.mk_mul_mk,
        piecewise_mul_piecewise, mul_one, and_self] }

section

end


end Subgroup
