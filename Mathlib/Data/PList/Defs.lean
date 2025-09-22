import Mathlib.Data.PList.Notation

namespace PList

variable {α : Type*} {a b : α} {pl : PList α} {l : List α} {hl : l ≠ []}

unseal PList in
@[elab_as_elim, cases_eliminator]
def recOfList {motive : PList α → Sort*}
    (ofList : (l : List α) → (hl : l ≠ []) → motive (ofList l hl)) (pl : PList α) :
    motive pl := match pl with | ⟨l, hl⟩ => ofList l hl

@[simp]
theorem recOfList_ofList {motive : PList α → Sort*}
    (ofList : (l : List α) → (hl : l ≠ []) → motive (ofList l hl))
    (l : List α) (hl : l ≠ []) :
    recOfList ofList (PList.ofList l hl) = ofList l hl := rfl

@[elab_as_elim]
def recConsList {motive : PList α → Sort*} (consList : ∀ x l, motive (x :| l)) (pl : PList α) :
    motive pl := pl.recOfList (fun {l} =>
    l.recOn (fun h => (h rfl).elim) (fun _ _ _ _ => consList _ _))

@[simp]
theorem recConsList_consList {motive : PList α → Sort*}
    (consList : ∀ x l, motive (x :| l)) {x l} :
    recConsList consList (x :| l) = consList x l := rfl

@[elab_as_elim]
def recSnocList {motive : PList α → Sort*}
    (snocList : ∀ l y, motive (l |: y)) (pl : PList α) : motive pl := pl.recOfList (fun {l} =>
    l.reverseRecOn (fun h => (h rfl).elim) (fun _ _ _ _ => snocList _ _))

@[simp]
theorem recSnocList_snocList {motive : PList α → Sort*}
    (snocList : ∀ l y, motive (l |: y)) {l x} :
    recSnocList snocList (l |: x) = snocList l x := by
  unfold recSnocList PList.snocList
  rw [recOfList_ofList, List.reverseRecOn_concat]

def toList (pl : PList α) : List α := pl.recOfList (fun l _ => l)

instance [Repr α] : Repr (PList α) where
  reprPrec l := l.toList.repr

@[simp]
theorem toList_ne_nil : pl.toList ≠ [] := pl.recOfList (fun _ h => h)

@[simp]
theorem ofList_toList : ofList pl.toList toList_ne_nil = pl := pl.recOfList (fun _ _ => rfl)

@[simp]
theorem toList_ofList (hl) : (ofList l hl).toList = l := recOfList_ofList _ _ _

def equivSubtype : PList α ≃ Subtype (fun (l : List α) => l ≠ []) where
  toFun pl := Subtype.mk pl.toList toList_ne_nil
  invFun := fun ⟨l, hl⟩ => ofList l hl
  left_inv _ := ofList_toList
  right_inv l := Subtype.ext <| toList_ofList l.2

def head (pl : PList α) : α := pl.recConsList (fun a _ => a)
def tail (pl : PList α) : List α := pl.recConsList (fun _ l => l)

@[simp]
theorem head_ofHeadTail : (a :| l).head = a := rfl

@[simp]
theorem tail_ofHeadTail : (a :| l).tail = l := rfl

def init (pl : PList α) : List α := pl.recSnocList (fun l _ => l)
def last (pl : PList α) : α := pl.recSnocList (fun _ a => a)

/-- Non-empty lists can be made from a single element. -/
def uno (a : α) : PList α := ofList [a] (List.cons_ne_nil _ _)

theorem uno_eq_headNil : uno a = a :| [] := rfl

theorem uno_eq_nilLast : uno a = [] |: a := rfl

def cons (a : α) (pl : PList α) : PList α := pl.recOfList (fun l _ => a :| l)

@[simp]
theorem cons_ofList : cons a (ofList l hl) = a :| l := rfl

theorem cons_eq_consList : cons a pl = a :| pl.toList := by cases pl; simp

@[simp]
theorem cons_consList : cons a (b :| l) = a :| (b :: l) := rfl

def snoc (pl : PList α) (a : α) : PList α := pl.toList |: a

@[simp]
theorem snoc_ofList : snoc (ofList l hl) a  = l |: a := rfl

theorem snoc_eq_snocList : snoc pl a = pl.toList |: a := by cases pl; simp

@[simp]
theorem snoc_snocList : snoc (l |: b) a = (l ++ [b]) |: a := rfl

/-- A forward induction principle for `PList α`. -/
@[elab_as_elim, induction_eliminator]
def recOn {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
  (cons : ∀ x pl, motive pl → motive (cons x pl)) (pl : PList α) : motive pl :=
  pl.recConsList (Function.swap <| fun l => l.recOn (uno ·) (fun _ _ rec a => cons a _ (rec _)))

@[simp]
theorem recOn_uno {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
    (cons : ∀ x pl, motive pl → motive (cons x pl)) (a : α) :
    recOn uno cons (PList.uno a) = uno a := by
  simp_rw [recOn, uno_eq_headNil, recConsList_consList]

@[simp]
theorem recOn_cons {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
    (cons : ∀ x pl, motive pl → motive (cons x pl)) (a : α) (pl : PList α) :
    recOn uno cons (PList.cons a pl) = cons a pl (recOn uno cons pl) := by
  cases pl using recConsList
  simp_rw [recOn, cons_consList, recConsList_consList]

/-- A backward induction principle for `PList α`. -/
@[elab_as_elim, induction_eliminator]
def reverseRecOn {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
  (snoc : ∀ pl x, motive pl → motive (snoc pl x)) (pl : PList α) : motive pl :=
  pl.recSnocList (fun l => l.reverseRecOn (uno ·) (fun _ _ rec a => snoc _ a (rec _)))

@[simp]
theorem reverseRecOn_uno {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
    (snoc : ∀ pl x, motive pl → motive (snoc pl x)) (a : α) :
    reverseRecOn uno snoc (PList.uno a) = uno a := by
  simp_rw [reverseRecOn, uno_eq_nilLast, recSnocList_snocList, List.reverseRecOn_nil]

@[simp]
theorem reverseRecOn_snoc {motive : PList α → Sort*} (uno : ∀ x, motive (uno x))
    (snoc : ∀ pl x, motive pl → motive (snoc pl x)) (pl : PList α) (a : α) :
    reverseRecOn uno snoc (PList.snoc pl a) = snoc pl a (reverseRecOn uno snoc pl) := by
  cases pl using recSnocList
  simp_rw [reverseRecOn, snoc_snocList, recSnocList_snocList, List.reverseRecOn_concat]

#eval uno 0
#eval cons 1 (uno 0)
#eval cons 2 (cons 1 (uno 0))
#eval cons 3 (cons 2 (cons 1 (uno 0)))
#eval cons 4 (cons 3 (cons 1 (uno 0)))
#eval cons 5 (cons 4 (cons 3 (cons 1 (uno 0))))

#eval snoc (snoc (snoc (uno 0) 1) 2) 3

end PList
