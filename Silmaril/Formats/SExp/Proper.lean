module

public import Silmaril.Formats.SExp.Basic
public import Mathlib.Data.List.OfFn

/-!
# Proper S-expressions

The n-ary representation makes properness intrinsic. Its embedding into
`SExp2` uses a nil-terminated cons spine; the image is exactly the structural
`SExp2.Proper` predicate.
-/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats

universe u v

/-- Proper S-expressions: atoms and finite lists. -/
inductive SExp (Atom : Type u) where
  | atom (value : Atom)
  | list (n : Nat) (children : Fin n → SExp Atom)

instance : EmptyCollection (SExp α) := ⟨.list 0 Fin.elim0⟩
instance : Inhabited (SExp α) := ⟨∅⟩

namespace SExp

/-- The intrinsic proper empty list. -/
def nil : SExp α := ∅

def isNil : SExp α → Bool
  | .list 0 _ => true
  | _ => false

/-- Lisp spelling retained as an alias. -/
abbrev isnil := @isNil

def map (f : α → β) : SExp α → SExp β
  | .atom value => .atom (f value)
  | .list n children => .list n fun i => map f (children i)

def bind (expr : SExp α) (f : α → SExp β) : SExp β :=
  match expr with
  | .atom value => f value
  | .list n children => .list n fun i => bind (children i) f

@[simp] theorem bind_pure : ∀ expr : SExp α, bind expr .atom = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | list n children ih =>
      apply congrArg (SExp.list n)
      funext i
      exact ih i

theorem bind_assoc (expr : SExp α) (f : α → SExp β)
    (g : β → SExp γ) : bind (bind expr f) g = bind expr fun x => bind (f x) g := by
  induction expr with
  | atom => rfl
  | list n children ih =>
      apply congrArg (SExp.list n)
      funext i
      exact ih i

instance : Monad SExp where
  pure := .atom
  bind := bind

instance : LawfulMonad SExp := LawfulMonad.mk' _
  (fun expr => by change bind expr (fun x => .atom (id x)) = expr; simp)
  (fun _ _ => rfl)
  (fun expr f g => bind_assoc expr f g)

/-- Construct a list expression from an ordinary list of children. -/
def ofList (children : List (SExp α)) : SExp α :=
  .list children.length fun i => children[i]

/-- Extract children when the expression is a list. -/
def children? : SExp α → Option (List (SExp α))
  | .atom _ => none
  | .list _ children => some (List.ofFn children)

@[simp] theorem children?_ofList (children : List (SExp α)) :
    children? (ofList children) = some children := by
  simp [children?, ofList]

/-- Proper-list construction is an embedding, not an equivalence with all
proper expressions: atoms form the other summand. -/
theorem ofList_injective : Function.Injective (ofList : List (SExp α) → SExp α) := by
  intro a b h
  have := congrArg children? h
  simpa using this

/-- Lists of proper expressions embed as list nodes. -/
def ofListEmbedding (α : Type u) : List (SExp α) ↪ SExp α :=
  ⟨ofList, ofList_injective⟩

/-- Embed a list of atoms as a proper list of atom nodes. -/
def ofAtoms (values : List α) : SExp α := ofList (values.map .atom)

theorem ofAtoms_injective : Function.Injective (ofAtoms : List α → SExp α) := by
  intro xs ys h
  have hm := ofList_injective h
  exact ((List.map_injective_iff).2 fun _ _ h => SExp.atom.inj h) hm

def ofAtomsEmbedding (α : Type u) : List α ↪ SExp α :=
  ⟨ofAtoms, ofAtoms_injective⟩

/-- First child, or `nil` for atoms and the empty list. -/
def car : SExp α → SExp α
  | .atom _ => nil
  | .list 0 _ => nil
  | .list (_ + 1) children => children 0

/-- Remaining children as a list expression, or `nil` for atoms. -/
def cdr : SExp α → SExp α
  | .atom _ => nil
  | .list _ children => ofList (List.ofFn children).tail

@[simp] theorem car_nil : car (nil : SExp α) = nil := rfl
@[simp] theorem cdr_nil : cdr (nil : SExp α) = nil := by
  change SExp.list 0 _ = SExp.list 0 Fin.elim0
  apply congrArg (SExp.list 0)
  funext i
  exact Fin.elim0 i
@[simp] theorem isNil_eq_true (expr : SExp α) : isNil expr = true ↔ expr = nil := by
  cases expr with
  | atom => simp [isNil, nil]
  | list n children =>
      cases n with
      | zero =>
          constructor
          · intro _
            apply congrArg (SExp.list 0)
            funext i
            exact Fin.elim0 i
          · intro _; rfl
      | succ n =>
          constructor
          · intro h; cases h
          · intro h; injection h with hlen; omega

/-- The actual one-layer destructor equivalence. -/
def equivAtomOrList (α : Type u) : SExp α ≃ α ⊕ List (SExp α) where
  toFun
    | .atom value => .inl value
    | .list _ children => .inr (List.ofFn children)
  invFun
    | .inl value => .atom value
    | .inr children => ofList children
  left_inv expr := by
    cases expr with
    | atom => rfl
    | list n children =>
        change SExp.list (List.ofFn children).length
          (List.get (List.ofFn children)) = .list n children
        have hlen : (List.ofFn children).length = n := by simp
        have hchildren : List.get (List.ofFn children) ≍ children :=
          (Fin.heq_fun_iff hlen).2 (by intro i; simp)
        let a : Σ n, Fin n → SExp α := ⟨(List.ofFn children).length,
          List.get (List.ofFn children)⟩
        let b : Σ n, Fin n → SExp α := ⟨n, children⟩
        have hab : a = b := Sigma.ext hlen hchildren
        exact congrArg (fun p : Σ n, Fin n → SExp α => SExp.list p.1 p.2)
          hab
  right_inv value := by cases value <;> simp [ofList]

/-- Embed proper expressions into the dotted representation. -/
def toSExp2 : SExp α → SExp2 α
  | .atom value => .atom value
  | .list _ children => SExp2.ofList (List.ofFn fun i => toSExp2 (children i))

theorem ofList2_injective :
    Function.Injective (SExp2.ofList : List (SExp2 α) → SExp2 α) := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> cases h; rfl
  | cons head tail ih =>
      intro b h
      cases b with
      | nil => cases h
      | cons head' tail' =>
          injection h with hh ht
          exact congrArg₂ List.cons hh (ih ht)

/-- The proper-to-dotted embedding loses no information. -/
theorem toSExp2_injective : Function.Injective (toSExp2 : SExp α → SExp2 α) := by
  intro a
  induction a with
  | atom value =>
      intro b h
      cases b with
      | atom value' => injection h with hv; exact congrArg SExp.atom hv
      | list n children =>
          cases n with
          | zero => simp [toSExp2, SExp2.ofList] at h
          | succ n => simp [toSExp2, SExp2.ofList] at h
  | list n children ih =>
      intro b h
      cases b with
      | atom value =>
          cases n with
          | zero => simp [toSExp2, SExp2.ofList] at h
          | succ n => simp [toSExp2, SExp2.ofList] at h
      | list m children' =>
          have hl := ofList2_injective h
          have hlen : n = m := by simpa using congrArg List.length hl
          subst m
          apply congrArg (SExp.list n)
          funext i
          apply ih i
          simpa using congrArg (fun xs => xs[i.1]?) hl

theorem toSExp2_proper : ∀ expr : SExp α, SExp2.IsProper expr.toSExp2 := by
  intro expr
  induction expr with
  | atom value => exact Or.inl (.atom value)
  | list n children ih =>
      exact Or.inr (SExp2.properList_ofList fun child hchild => by
        obtain ⟨i, -, rfl⟩ := List.mem_ofFn.mp hchild
        exact ih i)

theorem proper_has_preimage_indexed {kind : SExp2.ProperKind}
    {value : SExp2 α} (h : SExp2.Proper kind value) :
    match kind with
    | .atom => ∃ expr : SExp α, toSExp2 expr = value
    | .list => ∃ xs : List (SExp α), SExp2.ofList (xs.map toSExp2) = value := by
  induction h with
  | atom value => exact ⟨.atom value, rfl⟩
  | nil => exact ⟨[], rfl⟩
  | @cons car cdr carKind hcar htail ihCar ihTail =>
      cases carKind with
      | atom =>
          obtain ⟨car, hcarEq⟩ := ihCar
          obtain ⟨tail, htailEq⟩ := ihTail
          exact ⟨car :: tail, by simp [SExp2.ofList, hcarEq, htailEq]⟩
      | list =>
          obtain ⟨carChildren, hcarEq⟩ := ihCar
          obtain ⟨tail, htailEq⟩ := ihTail
          let carExpr := ofList carChildren
          have hcar' : toSExp2 carExpr = car := by
            change SExp2.ofList (List.ofFn (toSExp2 ∘ List.get carChildren)) = _
            rw [← hcarEq]
            apply congrArg SExp2.ofList
            exact List.ofFn_getElem_eq_map carChildren toSExp2
          exact ⟨carExpr :: tail, by simp [SExp2.ofList, hcar', htailEq]⟩

theorem proper_has_preimage {value : SExp2 α}
    (h : SExp2.IsProper value) : ∃ expr, toSExp2 expr = value := by
  rcases h with hatom | hlist
  · exact proper_has_preimage_indexed hatom
  · obtain ⟨children, hchildren⟩ := proper_has_preimage_indexed hlist
    refine ⟨ofList children, ?_⟩
    change SExp2.ofList (List.ofFn (toSExp2 ∘ List.get children)) = _
    rw [← hchildren]
    apply congrArg SExp2.ofList
    exact List.ofFn_getElem_eq_map children toSExp2

/-- The structural properness predicate is precisely the image of `SExp`. -/
theorem proper_iff_exists (value : SExp2 α) :
    SExp2.IsProper value ↔ ∃ expr : SExp α, expr.toSExp2 = value := by
  constructor
  · exact proper_has_preimage
  · rintro ⟨expr, rfl⟩
    exact toSExp2_proper expr

/-- Proper dotted expressions are isomorphic to intrinsically proper ones. -/
noncomputable def equivProperSubtype (α : Type u) :
    SExp α ≃ {value : SExp2 α // SExp2.IsProper value} where
  toFun expr := ⟨expr.toSExp2, toSExp2_proper expr⟩
  invFun value := Classical.choose (proper_has_preimage value.property)
  left_inv expr := toSExp2_injective (Classical.choose_spec
    (proper_has_preimage (toSExp2_proper expr)))
  right_inv value := Subtype.ext (Classical.choose_spec (proper_has_preimage value.property))

/-- Embedding commutes with monadic substitution. -/
theorem toSExp2_bind (expr : SExp α) (f : α → SExp β) :
    toSExp2 (bind expr f) = SExp2.bind expr.toSExp2 (toSExp2 ∘ f) := by
  induction expr with
  | atom => rfl
  | list n children ih =>
      simp only [bind, toSExp2]
      rw [SExp2.bind_ofList]
      rw [List.map_ofFn]
      congr 2
      funext i
      exact ih i

end SExp
end Silmaril.Formats
