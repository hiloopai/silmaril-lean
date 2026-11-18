module

public import Silmaril.Formats.LeanNDJSON.Decode.Defs

/-!
# Lean-NDJSON: reference validation

lean4export numbers each table's entries in the order it writes them: names `1, 2, …` (name `0`
is the implicit anonymous name), levels `1, 2, …` (level `0` is the implicit zero), expressions
`0, 1, …`. **Serial validity** (`SerialValid`) checks exactly that numbering and that every
reference is to an entry already written:

* each name, level or expression record defines the **next** id of its table (so no id is
  defined twice and none is skipped);
* every reference of a record (to names, levels and expressions) is to an id below the next one,
  so there are no forward references and, in particular, no cycles;
* every declared name is declared once (`DeclNamesNodup`), counting each type, constructor and
  recursor of an inductive block.

`validate?` decides both (`Thms`: `serialValid?_iff`), and `firstInvalid` names the first
offending record. Validation is about the shape of the reference graph only: it does not check
bound-variable scope, typing, or that a constant refers to a declared constant.
-/

@[expose] public section

namespace Silmaril.Formats.LeanNDJSON

/-- The next id of each table. -/
structure Counters where
  names : Nat
  levels : Nat
  exprs : Nat
  deriving DecidableEq, Repr

/-- Before the first record: the implicit anonymous name and zero level. -/
def Counters.initial : Counters := ⟨1, 1, 0⟩

/-- An entry already written. Declarations are never referred to by id. -/
def Counters.known (c : Counters) : Key → Bool
  | ⟨.name, i⟩ => decide (i < c.names)
  | ⟨.level, i⟩ => decide (i < c.levels)
  | ⟨.expr, i⟩ => decide (i < c.exprs)
  | ⟨.declaration, _⟩ => false

/-- The counters after a record, when it defines the next id of its table. -/
def Counters.next (c : Counters) : Event → Option Counters
  | .name i _ => if i = c.names then some { c with names := i + 1 } else none
  | .level i _ => if i = c.levels then some { c with levels := i + 1 } else none
  | .expr i _ => if i = c.exprs then some { c with exprs := i + 1 } else none
  | .declaration _ => some c

/-- **Serial validity**: each record defines the next id of its table and refers only to entries
already written. -/
def SerialValid : Counters → List Event → Prop
  | _, [] => True
  | c, e :: es => (∀ r ∈ e.references, c.known r = true) ∧
      ∃ c', c.next e = some c' ∧ SerialValid c' es

/-- Decide serial validity. -/
def serialValid? : Counters → List Event → Bool
  | _, [] => true
  | c, e :: es => e.references.all c.known &&
      match c.next e with
      | some c' => serialValid? c' es
      | none => false

/-- The declared names, in order. -/
def declNames (es : List Event) : List Nat :=
  es.flatMap fun | .declaration d => d.names | _ => []

/-- Every name is declared at most once. -/
def DeclNamesNodup (es : List Event) : Prop := (declNames es).Nodup

/-- **A valid file**: serially valid, with distinct declared names. -/
def Valid (es : List Event) : Prop := SerialValid .initial es ∧ DeclNamesNodup es

/-- Decide validity. -/
def validate? (es : List Event) : Bool := serialValid? .initial es && decide (declNames es).Nodup

/-- The first record that breaks serial validity (by line number, from `first`), and why. -/
def firstInvalid (first : Nat) : Counters → List Event → Option (Nat × String)
  | _, [] => none
  | c, e :: es =>
    match e.references.find? (fun r => !c.known r) with
    | some r => some (first, s!"refers to {repr r.table} {r.index}, which is not written before it")
    | none =>
      match c.next e with
      | some c' => firstInvalid (first + 1) c' es
      | none => some (first, s!"does not define the next id of its table ({repr c})")

end Silmaril.Formats.LeanNDJSON
