module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Atom

/-!
# SpecTec's mixfix operators

A transcription of `spectec/src/xl/mixop.ml` at
`608711107b7f1edb13efd57b7d79b49477462d36`.  A `mixop` is the shape of a
constructor or a relation symbol: a tree of atoms with holes for arguments,
e.g. `Seq [Arg; Atom "->"; Arg]` for the arrow of a function type.

`--ast` prints a mixfix operator with `Mixop.to_string`
(`spectec/src/xl/mixop.ml:91`, from `spectec/src/backend-ast/print.ml:13`),
which erases almost all of that structure, which is why the AST in
`Silmaril/SpecTec/IL/Ast.lean` stores the rendering itself (`IL.MixopS`).
`Mixop.ofString` is the canonical section of `Mixop.toString`:
`Mixop.toString_ofString` says that *every* string is the rendering of a
mixfix operator, and `Mixop.Normal` picks out the operators that `ofString`
returns, on which `toString` is injective.

`ofString` splits its argument at the `%` characters that `to_string` prints
for argument positions: each maximal nonempty run of other characters becomes
an `Atom` and each `%` becomes an `Arg`.  There is one wrinkle, forced by the
special case at `spectec/src/xl/mixop.ml:92`: a `Seq` whose head is an atom
and whose remaining elements are all arguments prints as that atom *alone*,
so the pieces of a string like `"a%"` cannot be assembled into a plain `Seq`
without losing the arguments.  `ofPieces` therefore wraps the leading atom of
such a sequence in a singleton `Seq`, which renders identically but is not
matched by `to_string`'s pattern; see `Mixop.ofPieces`.  This is not a corner
case: the relation `NotationReduct` of `specs/spectec/wasm-3.0.ast` has the
mixfix operator `"~>%"`.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

universe u v

/-- `type 'a mixop` (`spectec/src/xl/mixop.ml:5`): a mixfix operator, i.e. a
tree of atoms with holes for `α`-valued arguments. -/
inductive Mixop (α : Type u) where
  /-- `Arg of 'a` (`spectec/src/xl/mixop.ml:6`): an argument position. -/
  | arg (value : α)
  /-- `Atom of atom` (`spectec/src/xl/mixop.ml:7`). -/
  | atom (a : Atom)
  /-- `Brack of atom * 'a mixop * atom` (`spectec/src/xl/mixop.ml:8`): an
  operator enclosed in a pair of bracket atoms. -/
  | brack (left : Atom) (inner : Mixop α) (right : Atom)
  /-- `Infix of 'a mixop * atom * 'a mixop` (`spectec/src/xl/mixop.ml:9`). -/
  | infix (lhs : Mixop α) (a : Atom) (rhs : Mixop α)
  /-- `Seq of 'a mixop list` (`spectec/src/xl/mixop.ml:10`). -/
  | seq (items : List (Mixop α))
  deriving Repr

namespace Mixop

variable {α : Type u} {β : Type v}

/-- The empty sequence is a mixfix operator over any argument type. -/
instance : Inhabited (Mixop α) := ⟨.seq []⟩

mutual

/-- Structural decision procedure for equality of mixfix operators. -/
def decEq [DecidableEq α] : (a b : Mixop α) → Decidable (a = b)
  | .arg x, .arg y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .atom a, .atom b => if h : a = b then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .brack l m r, .brack l' m' r' =>
      if h : l = l' then
        match decEq m m' with
        | .isTrue h' =>
            if h'' : r = r' then .isTrue (by rw [h, h', h'']) else .isFalse (by simp [h''])
        | .isFalse h' => .isFalse (by simp [h'])
      else .isFalse (by simp [h])
  | .infix m₁ a m₂, .infix m₁' a' m₂' =>
      match decEq m₁ m₁' with
      | .isTrue h =>
          if h' : a = a' then
            match decEq m₂ m₂' with
            | .isTrue h'' => .isTrue (by rw [h, h', h''])
            | .isFalse h'' => .isFalse (by simp [h''])
          else .isFalse (by simp [h'])
      | .isFalse h => .isFalse (by simp [h])
  | .seq ms, .seq ms' =>
      match decEqList ms ms' with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
  | .arg _, .atom _ | .arg _, .brack .. | .arg _, .infix .. | .arg _, .seq _
  | .atom _, .arg _ | .atom _, .brack .. | .atom _, .infix .. | .atom _, .seq _
  | .brack .., .arg _ | .brack .., .atom _ | .brack .., .infix .. | .brack .., .seq _
  | .infix .., .arg _ | .infix .., .atom _ | .infix .., .brack .. | .infix .., .seq _
  | .seq _, .arg _ | .seq _, .atom _ | .seq _, .brack .. | .seq _, .infix .. =>
      .isFalse (by simp)

/-- Structural decision procedure for equality of lists of mixfix operators. -/
def decEqList [DecidableEq α] : (a b : List (Mixop α)) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | m :: ms, m' :: ms' =>
      match decEq m m' with
      | .isTrue h =>
        match decEqList ms ms' with
        | .isTrue h' => .isTrue (by rw [h, h'])
        | .isFalse h' => .isFalse (by simp [h'])
      | .isFalse h => .isFalse (by simp [h])

end

/-- Equality of mixfix operators is decidable. -/
instance [DecidableEq α] : DecidableEq (Mixop α) := decEq

/-- Equality of lists of mixfix operators is decidable. -/
instance [DecidableEq α] : DecidableEq (List (Mixop α)) := decEqList

/-! ## Traversals -/

mutual

/-- `map` (`spectec/src/xl/mixop.ml:13`): rename the argument positions. -/
def map (f : α → β) : Mixop α → Mixop β
  | .arg x => .arg (f x)
  | .atom a => .atom a
  | .brack l m r => .brack l (map f m) r
  | .infix m₁ a m₂ => .infix (map f m₁) a (map f m₂)
  | .seq ms => .seq (maps f ms)

/-- `List.map (map f)` (`spectec/src/xl/mixop.ml:22`). -/
def maps (f : α → β) : List (Mixop α) → List (Mixop β)
  | [] => []
  | m :: ms => map f m :: maps f ms

end

/-- `maps` is `List.map` of `map`. -/
theorem maps_eq_map (f : α → β) : ∀ ms : List (Mixop α), maps f ms = ms.map (map f)
  | [] => rfl
  | m :: ms => by simp [maps, maps_eq_map f ms]

mutual

/-- `fold` (`spectec/src/xl/mixop.ml:24`): fold `f` over the argument
positions, left to right. -/
def fold (f : β → α → β) : β → Mixop α → β
  | x, .arg y => f x y
  | x, .atom _ => x
  | x, .brack _ m _ => fold f x m
  | x, .infix m₁ _ m₂ => fold f (fold f x m₁) m₂
  | x, .seq ms => folds f x ms

/-- `List.fold_left (fold f)` (`spectec/src/xl/mixop.ml:30`). -/
def folds (f : β → α → β) : β → List (Mixop α) → β
  | x, [] => x
  | x, m :: ms => folds f (fold f x m) ms

end

/-- `folds` is `List.foldl` of `fold`. -/
theorem folds_eq_foldl (f : β → α → β) :
    ∀ (x : β) (ms : List (Mixop α)), folds f x ms = ms.foldl (fold f) x
  | _, [] => rfl
  | x, m :: ms => by simp [folds, folds_eq_foldl f (fold f x m) ms]

mutual

/-- `map_atoms` (`spectec/src/xl/mixop.ml:32`): rename every atom. -/
def mapAtoms (f : Atom → Atom) : Mixop α → Mixop α
  | .arg x => .arg x
  | .atom a => .atom (f a)
  | .brack l m r => .brack (f l) (mapAtoms f m) (f r)
  | .infix m₁ a m₂ => .infix (mapAtoms f m₁) (f a) (mapAtoms f m₂)
  | .seq ms => .seq (mapAtomss f ms)

/-- `List.map (map_atoms f)` (`spectec/src/xl/mixop.ml:39`). -/
def mapAtomss (f : Atom → Atom) : List (Mixop α) → List (Mixop α)
  | [] => []
  | m :: ms => mapAtoms f m :: mapAtomss f ms

end

/-- `mapAtomss` is `List.map` of `mapAtoms`. -/
theorem mapAtomss_eq_map (f : Atom → Atom) :
    ∀ ms : List (Mixop α), mapAtomss (α := α) f ms = ms.map (mapAtoms f)
  | [] => rfl
  | m :: ms => by simp [mapAtomss, mapAtomss_eq_map f ms]

/-- `arity` (`spectec/src/xl/mixop.ml:44`): the number of argument positions. -/
def arity (m : Mixop α) : Nat := fold (fun n _ => n + 1) 0 m

mutual

/-- `head` (`spectec/src/xl/mixop.ml:59`): the leftmost atom, if any. -/
def head : Mixop α → Option Atom
  | .arg _ => none
  | .atom a => some a
  | .brack a _ _ => some a
  | .infix _ a _ => some a
  | .seq ms => heads ms

/-- `head` on the elements of a `Seq` (`spectec/src/xl/mixop.ml:62`). -/
def heads : List (Mixop α) → Option Atom
  | [] => none
  | m :: ms =>
      match head m with
      | none => heads ms
      | some a => some a

end

/-- `(++)` on lists of atom groups (`spectec/src/xl/mixop.ml:54`): append the
two lists, merging the last group of the first with the first group of the
second.  OCaml raises on an empty argument (`Lib.List.split_last`,
`Lib.List.split_hd`, `spectec/src/util/lib.ml:28,37`); here an empty argument
is the unit of the operation. -/
def joinAtomss : List (List Atom) → List (List Atom) → List (List Atom)
  | [], bss => bss
  | [as], [] => [as]
  | [as], bs :: bss => (as ++ bs) :: bss
  | as :: as' :: ass, bss => as :: joinAtomss (as' :: ass) bss

mutual

/-- `flatten` (`spectec/src/xl/mixop.ml:67`): the atoms of a mixfix operator,
grouped by the argument position they precede; the result has
`arity m + 1` groups. -/
def flatten : Mixop α → List (List Atom)
  | .arg _ => [[], []]
  | .atom a => [[a]]
  | .brack l m r => joinAtomss (joinAtomss [[l]] (flatten m)) [[r]]
  | .infix m₁ a m₂ => joinAtomss (joinAtomss (flatten m₁) [[a]]) (flatten m₂)
  | .seq ms => (flattens ms).foldl joinAtomss [[]]

/-- `List.map flatten` (`spectec/src/xl/mixop.ml:72`). -/
def flattens : List (Mixop α) → List (List (List Atom))
  | [] => []
  | m :: ms => flatten m :: flattens ms

end

/-- `flattens` is `List.map` of `flatten`. -/
theorem flattens_eq_map : ∀ ms : List (Mixop α), flattens ms = ms.map flatten
  | [] => rfl
  | m :: ms => by simp [flattens, flattens_eq_map ms]

/-! ## Rendering -/

mutual

/-- `to_string_with` (`spectec/src/xl/mixop.ml:81`): render the operator,
printing an argument position `x` as `f x` and separating the elements of a
`Seq` by `sep`. -/
def toStringWith (f : α → String) (sep : String) : Mixop α → String
  | .arg x => f x
  | .atom a => a.toString
  | .brack l m r => l.toString ++ toStringWith f sep m ++ r.toString
  | .infix m₁ a m₂ => toStringWith f sep m₁ ++ a.toString ++ toStringWith f sep m₂
  | .seq ms => sep.intercalate (toStringWiths f sep ms)

/-- `List.map (to_string_with f s)` (`spectec/src/xl/mixop.ml:83`). -/
def toStringWiths (f : α → String) (sep : String) : List (Mixop α) → List String
  | [] => []
  | m :: ms => toStringWith f sep m :: toStringWiths f sep ms

end

/-- `toStringWiths` is `List.map` of `toStringWith`. -/
theorem toStringWiths_eq_map (f : α → String) (sep : String) :
    ∀ ms : List (Mixop α), toStringWiths f sep ms = ms.map (toStringWith f sep)
  | [] => rfl
  | m :: ms => by simp [toStringWiths, toStringWiths_eq_map f sep ms]

/-- `is_arg` (`spectec/src/xl/mixop.ml:90`). -/
def isArg : Mixop α → Bool
  | .arg _ => true
  | _ => false

/-- `to_string_with (Fun.const "%") ""` (`spectec/src/xl/mixop.ml:93`): every
argument position becomes `%` and nothing separates the elements of a `Seq`. -/
def render (m : Mixop Unit) : String := toStringWith (fun _ => "%") "" m

/-- `render` of a list of operators, concatenated. -/
def renders (ms : List (Mixop Unit)) : String := String.join (ms.map render)

/-- `String.concat ""` is `String.join`. -/
theorem intercalate_empty_eq_join : ∀ l : List String, String.intercalate "" l = String.join l
  | [] => by simp
  | [_] => by simp
  | x :: y :: l => by
      rw [String.intercalate_cons_cons, String.join_cons, intercalate_empty_eq_join (y :: l)]
      simp

@[simp] theorem render_arg (x : Unit) : render (.arg x) = "%" := rfl

@[simp] theorem render_atom (a : Atom) : render (.atom a) = a.toString := rfl

@[simp] theorem render_seq (ms : List (Mixop Unit)) : render (.seq ms) = renders ms := by
  rw [render, toStringWith, toStringWiths_eq_map, intercalate_empty_eq_join, renders]
  rfl

@[simp] theorem renders_nil : renders [] = "" := by simp [renders]

@[simp] theorem renders_cons (m : Mixop Unit) (ms : List (Mixop Unit)) :
    renders (m :: ms) = render m ++ renders ms := by simp [renders]

/-- `to_string` (`spectec/src/xl/mixop.ml:91`), the rendering that
`spectec/src/backend-ast/print.ml:13` prints for every mixfix operator in the
`--ast` stream.

It is heavily lossy.  A `Seq` whose first element is an atom and all of whose
remaining elements are argument positions prints as that atom alone
(`spectec/src/xl/mixop.ml:92`), so the arity is erased; in every other case
the bracketing structure is erased and each argument position prints as a
bare `%`. -/
def toString (m : Mixop Unit) : String :=
  match m with
  | .seq (.atom a :: tail) => if tail.all isArg then a.toString else render m
  | _ => render m

/-! ## The canonical section of `toString` -/

/-- Emit the accumulated run `run` of non-`%` characters, in reverse, as an
atom piece in front of `rest`; an empty run contributes nothing. -/
def flushRun (run : List Char) (rest : List (Mixop Unit)) : List (Mixop Unit) :=
  match run with
  | [] => rest
  | _ :: _ => .atom (Atom.ofString (String.ofList run.reverse)) :: rest

/-- The pieces of a rendered mixfix operator, with `run` accumulating the
current run of non-`%` characters in reverse. -/
def piecesAux : List Char → List Char → List (Mixop Unit)
  | run, [] => flushRun run []
  | run, c :: cs =>
      if c = '%' then flushRun run (.arg () :: piecesAux [] cs)
      else piecesAux (c :: run) cs

/-- The pieces of a rendered mixfix operator: each maximal nonempty run of
non-`%` characters becomes an atom, and each `%` becomes an argument
position. -/
def pieces (cs : List Char) : List (Mixop Unit) := piecesAux [] cs

/-- Assemble pieces into a mixfix operator.

The pieces are a `Seq`, except that a single piece stands for itself, so that
a rendering without any `%` comes back as a bare `Atom`.  The one subtlety is
the special case of `to_string` (`spectec/src/xl/mixop.ml:92`): pieces of the
shape `Atom a :: args` with at least one argument would print as `a` alone,
losing the arguments, so the leading atom is wrapped in a singleton `Seq`,
which `to_string`'s pattern does not match and which renders identically. -/
def ofPieces : List (Mixop Unit) → Mixop Unit
  | [] => .seq []
  | [.atom a] => .atom a
  | [.arg x] => .arg x
  | .atom a :: ms => if ms.all isArg then .seq (.seq [.atom a] :: ms) else .seq (.atom a :: ms)
  | ms => .seq ms

/-- The canonical section of `toString`: split `s` at its `%` characters,
turning each maximal nonempty run of other characters into an atom and each
`%` into an argument position.  `toString_ofString` is the round trip. -/
def ofString (s : String) : Mixop Unit := ofPieces (pieces s.toList)

/-- Rendering a flushed run prepends the run. -/
theorem renders_flushRun (run : List Char) (rest : List (Mixop Unit)) :
    renders (flushRun run rest) = String.ofList run.reverse ++ renders rest := by
  cases run with
  | nil => simp [flushRun]
  | cons c cs => simp [flushRun]

/-- `piecesAux` renders back to the characters it consumed. -/
theorem renders_piecesAux : ∀ run cs : List Char,
    renders (piecesAux run cs) = String.ofList (run.reverse ++ cs)
  | run, [] => by simp [piecesAux, renders_flushRun]
  | run, c :: cs => by
      rw [piecesAux]
      split
      · next h =>
          subst h
          rw [renders_flushRun, renders_cons, render_arg, renders_piecesAux [] cs]
          simp [String.ofList_append]
      · next h =>
          rw [renders_piecesAux (c :: run) cs]
          simp

/-- Assembling pieces and rendering gives back the rendering of the pieces. -/
theorem toString_ofPieces : ∀ ms : List (Mixop Unit), toString (ofPieces ms) = renders ms
  | [] => by simp [ofPieces, toString]
  | [.atom a] => by simp [ofPieces, toString]
  | [.arg x] => by simp [ofPieces, toString]
  | .atom a :: m :: ms => by
      simp only [ofPieces]
      split
      · next _ => simp [toString]
      · next h => simp [toString, h]
  | .arg x :: m :: ms => by simp [ofPieces, toString]
  | .brack l mm r :: ms => by simp [ofPieces, toString]
  | .infix m₁ a m₂ :: ms => by simp [ofPieces, toString]
  | .seq xs :: ms => by simp [ofPieces, toString]

/-- `ofString` is a section of `toString`: every string is the rendering of a
mixfix operator. -/
@[simp] theorem toString_ofString (s : String) : (ofString s).toString = s := by
  rw [ofString, toString_ofPieces, pieces, renders_piecesAux]
  simp

/-- A mixfix operator is *normal* when it is the one `ofString` builds from
its own rendering.  `--ast` only determines a mixfix operator up to
`toString`, so the normal operators are the ones an imported script may
contain. -/
def Normal (m : Mixop Unit) : Prop := ofString m.toString = m

/-- Normality is decidable: it is an equation between concrete operators. -/
instance (m : Mixop Unit) : Decidable (Normal m) :=
  inferInstanceAs (Decidable (ofString m.toString = m))

/-- Everything `ofString` builds is normal. -/
theorem normal_ofString (s : String) : (ofString s).Normal := by
  show ofString (ofString s).toString = ofString s
  rw [toString_ofString]

/-- A normal operator is recovered from its rendering. -/
theorem ofString_toString_of_normal {m : Mixop Unit} (h : m.Normal) :
    ofString m.toString = m := h

/-- `Mixop.toString` is injective on normal operators, so a rendered mixfix
operator determines its normal preimage. -/
theorem toString_injective_on_normal {m m' : Mixop Unit} (h : m.Normal) (h' : m'.Normal)
    (he : m.toString = m'.toString) : m = m' := by
  have hmm : ofString m.toString = ofString m'.toString := by rw [he]
  rwa [ofString_toString_of_normal h, ofString_toString_of_normal h'] at hmm

/-- The image of `Mixop.ofString` is exactly the normal operators.  It is far
from surjective: `Seq [Atom a; Arg ()]` renders as `a` alone
(`spectec/src/xl/mixop.ml:92`) and so is not normal. -/
theorem exists_ofString_iff_normal (m : Mixop Unit) : (∃ s, ofString s = m) ↔ m.Normal := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    subst hs
    exact normal_ofString s
  · intro h
    exact ⟨m.toString, h⟩

end Mixop

end Silmaril.SpecTec.IL
