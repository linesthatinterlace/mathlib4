import Mathlib

/-! # Definition and notation for nonempty lists -/

/-- The type of non-empty list of elements of type `α`. -/
@[irreducible] def PList (α : Type*) := { l : List α // l ≠ [] }

namespace PList

variable {α : Type*}

unseal PList in
/-- Non-empty lists can be constructed from a proof that a given list is not equal to `[]`. -/
def ofList (l : List α) (hl : l ≠ []) : PList α := Subtype.mk l hl

/-- Non-empty lists can be constructed from a head element and a tail list. -/
def consList (a : α) (l : List α) : PList α := ofList (a :: l) (List.cons_ne_nil a l)

@[inherit_doc] infixr:67 " :| " => PList.consList

/-- Non-empty lists can be constructed from an initial list and a last element. -/
def snocList (l : List α) (a : α) : PList α := ofList (l ++ [a]) (List.concat_ne_nil a l)

@[inherit_doc] infixl:67 " |: " => PList.snocList

end PList
