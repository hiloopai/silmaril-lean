module

public import Silmaril.Formats.SExp.Tagged

/-!
# SpecTec's S-expression trees

`spectec --ast` prints the elaborated internal language as a stream of
S-expressions in the shape fixed by `spectec/src/util/sexpr.ml:1`:

```ocaml
type sexpr = Atom of string | Node of string * sexpr list
```

A node's head is a *string*, not a nested expression, so these trees are
tagged rather than proper Lisp lists.  `Silmaril.Formats.TExpr` is exactly
that shape; `SExp` is the `List`-based presentation of `TExpr String String`,
and `SExp.equivTExpr` below makes that precise.  The `List` form is used
throughout because the import elaborator builds multi-megabyte terms and
`Fin n → _` children force a `List.ofFn` round trip at every node.

`Repr` and `Inhabited` are derived, but `DecidableEq` is written out by hand
as `SExp.decEq`: Lean's `DecidableEq` deriving handler does not apply to a
nested inductive such as this one, whose recursive occurrence sits under
`List`.
-/

@[expose] public section

namespace Silmaril.SpecTec

/-- A SpecTec S-expression (`spectec/src/util/sexpr.ml:1`).

`atom` is an uninterpreted token; `node` is `Node (tag, children)`, whose tag
is a bare identifier printed immediately after the opening parenthesis. -/
inductive SExp where
  /-- `Atom of string` (`spectec/src/util/sexpr.ml:1`). -/
  | atom (value : String)
  /-- `Node of string * sexpr list` (`spectec/src/util/sexpr.ml:1`). -/
  | node (tag : String) (children : List SExp)
  deriving Repr, Inhabited

namespace SExp

mutual

/-- Structural decision procedure for equality of S-expressions. -/
def decEq : (a b : SExp) → Decidable (a = b)
  | .atom x, .atom y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .atom _, .node _ _ => .isFalse (by simp)
  | .node _ _, .atom _ => .isFalse (by simp)
  | .node t cs, .node t' cs' =>
      if h : t = t' then
        match decEqList cs cs' with
        | .isTrue h' => .isTrue (by rw [h, h'])
        | .isFalse h' => .isFalse (by simp [h'])
      else .isFalse (by simp [h])

/-- Structural decision procedure for equality of S-expression lists. -/
def decEqList : (a b : List SExp) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | x :: xs, y :: ys =>
      match decEq x y with
      | .isTrue h =>
        match decEqList xs ys with
        | .isTrue h' => .isTrue (by rw [h, h'])
        | .isFalse h' => .isFalse (by simp [h'])
      | .isFalse h => .isFalse (by simp [h])

end

instance : DecidableEq SExp := decEq
instance : DecidableEq (List SExp) := decEqList

mutual

/-- Number of nodes and atoms. -/
def size : SExp → Nat
  | .atom _ => 1
  | .node _ cs => 1 + sizes cs

/-- Total `size` of a list of children. -/
def sizes : List SExp → Nat
  | [] => 0
  | c :: cs => size c + sizes cs

end

@[simp] theorem size_atom (s : String) : size (.atom s) = 1 := rfl
@[simp] theorem size_node (t : String) (cs : List SExp) : size (.node t cs) = 1 + sizes cs := rfl
@[simp] theorem sizes_nil : sizes [] = 0 := rfl
@[simp] theorem sizes_cons (c : SExp) (cs : List SExp) :
    sizes (c :: cs) = size c + sizes cs := rfl

theorem size_pos : ∀ e : SExp, 0 < size e
  | .atom _ => Nat.zero_lt_one
  | .node _ _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right _ _)

theorem sizes_eq_sum (cs : List SExp) : sizes cs = (cs.map size).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

theorem size_lt_of_mem {c : SExp} {cs : List SExp} (h : c ∈ cs) (t : String) :
    size c < size (.node t cs) := by
  have : size c ≤ sizes cs := by
    induction cs with
    | nil => cases h
    | cons d ds ih =>
        rcases List.mem_cons.mp h with rfl | hmem
        · exact Nat.le_add_right _ _
        · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)
  simpa [Nat.add_comm] using Nat.lt_succ_of_le this

/-! ## Relation to `Silmaril.Formats.TExpr` -/

open Silmaril.Formats in
mutual

/-- The `Fin`-indexed presentation of the same tree. -/
def toTExpr : SExp → TExpr String String
  | .atom v => .atom v
  | .node t cs => TExpr.ofList t (toTExprs cs)

/-- `toTExpr` on a list of children. -/
def toTExprs : List SExp → List (TExpr String String)
  | [] => []
  | c :: cs => toTExpr c :: toTExprs cs

end

open Silmaril.Formats in
/-- The inverse of `toTExpr`.  Defined by recursion on the `Fin`-indexed tree,
using `List.ofFn` to collect the children. -/
def ofTExpr : TExpr String String → SExp
  | .atom v => .atom v
  | .tag t _ cs => .node t (List.ofFn fun i => ofTExpr (cs i))

theorem toTExprs_eq_map : ∀ cs : List SExp, toTExprs cs = cs.map toTExpr
  | [] => rfl
  | c :: cs => by simp [toTExprs, toTExprs_eq_map cs]

mutual

theorem ofTExpr_toTExpr : ∀ e : SExp, ofTExpr (toTExpr e) = e
  | .atom _ => rfl
  | .node t cs => by
      simp only [toTExpr, ofTExpr, Silmaril.Formats.TExpr.ofList, List.get_eq_getElem,
        List.ofFn_getElem_eq_map]
      exact congrArg (SExp.node t) (ofTExpr_toTExprs cs)

theorem ofTExpr_toTExprs : ∀ cs : List SExp, (toTExprs cs).map ofTExpr = cs
  | [] => rfl
  | c :: cs => by
      simp only [toTExprs, List.map_cons, ofTExpr_toTExpr c, ofTExpr_toTExprs cs]

end

theorem toTExpr_injective : Function.Injective toTExpr :=
  Function.LeftInverse.injective ofTExpr_toTExpr

open Silmaril.Formats in
/-- `ofTExpr` is a left inverse of `toTExpr` too: rebuilding the `List`-based
tree and re-indexing it recovers the original `Fin`-indexed one. -/
theorem toTExpr_ofTExpr : ∀ t : TExpr String String, toTExpr (ofTExpr t) = t := by
  intro t
  induction t with
  | atom _ => rfl
  | tag v n cs ih =>
      show TExpr.ofList v (toTExprs (List.ofFn fun i => ofTExpr (cs i))) = _
      rw [toTExprs_eq_map, List.map_ofFn]
      have hcs : (fun i => toTExpr (ofTExpr (cs i))) = cs := funext ih
      show TExpr.ofNode (.inr ⟨v, List.ofFn (fun i => toTExpr (ofTExpr (cs i)))⟩) = _
      rw [hcs]
      exact TExpr.ofNode_node (TExpr.tag v n cs)

open Silmaril.Formats in
/-- `SExp` and `TExpr String String` are the same type: the `List`-based and
the `Fin`-indexed presentations of a string-tagged tree with string atoms.
The analogue of `Silmaril.Formats.TExpr.equivNode`. -/
def equivTExpr : SExp ≃ TExpr String String where
  toFun := toTExpr
  invFun := ofTExpr
  left_inv := ofTExpr_toTExpr
  right_inv := toTExpr_ofTExpr

end SExp

end Silmaril.SpecTec
