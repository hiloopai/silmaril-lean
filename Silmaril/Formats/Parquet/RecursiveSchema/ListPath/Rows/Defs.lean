module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

/-! The canonical ordered Dremel trace of the declared LIST path.
The inverse consumes logical slots with no page or byte assumptions. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows

open Arrow.RecursiveSchema.Batch.Rows (Cell Row Observation RowFits)
open RecursiveSchema.Chunk (Word)

@[expose] public section

structure Atom where
  repetition : Nat
  definition : Nat
  word : Option Word
  deriving DecidableEq, Repr

structure Segment where
  first : Atom
  rest : List Atom
  deriving DecidableEq, Repr

def Segment.atoms (part : Segment) : List Atom := part.first :: part.rest

def signedWord (kind : RecursiveSchema.Kind) (cell : Cell) : Option Word :=
  match kind, cell with
  | .int32, some (.int32 value) => some (.int32 value)
  | .int64, some (.int64 value) => some (.int64 value)
  | _, _ => none

def signedCell (kind : RecursiveSchema.Kind) (word : Option Word) : Option Cell :=
  match kind, word with
  | .int32, some (.int32 value) => some (some (.int32 value))
  | .int64, some (.int64 value) => some (some (.int64 value))
  | _, _ => none

/-- Ordered leaf values from the logical cells alone. -/
def words : Shape → Cell → List Word
  | .list _ child, some (.list cells) => cells.flatMap (words child)
  | .signed _ kind, cell => (signedWord kind cell).toList
  | _, _ => []

namespace Projection

def marker (repetition definition : Nat) : Segment := ⟨⟨repetition, definition, none⟩, []⟩

/-- Only the first child inherits the enclosing repetition. A later child
starts at the depth of its own repeated wrapper. OPTIONAL adds a
definition step before the empty slot, then the wrapper adds another. -/
def cell : Shape → Nat → Nat → Nat → Cell → Option Segment
  | .signed site kind, _, rep, base, value =>
    match value with
    | none => if site.nullable then some (marker rep base) else none
    | some _ => (signedWord kind value).map fun word =>
      ⟨⟨rep, base + site.nullable.toNat, some word⟩, []⟩
  | .list node child, depth, rep, base, value => do
    let empty := base + node.site.nullable.toNat
    match value with
    | none => if node.site.nullable then some (marker rep base) else none
    | some (.list []) => some (marker rep empty)
    | some (.list (first :: rest)) =>
      let head ← cell child (depth + 1) rep (empty + 1) first
      let tail ← rest.mapM (cell child (depth + 1) (depth + 1) (empty + 1))
      return ⟨head.first, head.rest ++ tail.flatMap Segment.atoms⟩
    | _ => none

def row (plan : Plan) : Row → Option Segment
  | [value] => cell plan.shape 0 0 0 value
  | _ => none

def trace (plan : Plan) (rows : List Row) : Option (List Atom) :=
  (rows.mapM (row plan)).map (·.flatMap Segment.atoms)

end Projection

def Relation (plan : Plan) (input : List Atom) (rows : List Row) : Prop :=
  Projection.trace plan rows = some input

instance (plan : Plan) (input : List Atom) (rows : List Row) : Decidable (Relation plan input rows) := by
  unfold Relation
  infer_instance

def sumDemand {α : Type} (measure : α → Nat) (values : List α) : Nat :=
  values.foldl (fun total value => total + measure value) 0

/-- Positive demand for each logical cell, including null or empty ones.
A malformed cell will subsequently be refused by the projection. -/
def demand : Shape → Cell → Nat
  | .list _ child, some (.list (first :: rest)) =>
    demand child first + sumDemand (demand child) rest
  | _, _ => 1

structure Limits where
  maxRows : Nat := 1024 * 1024
  maxSlots : Nat := 1024 * 1024

inductive Error where
  | rowLimit (actual : Nat)
  | slotLimit (actual : Nat)
  | rowCount (expected actual : Nat)
  | shape (row : Nat)
  | projection
  | traceMismatch
  deriving DecidableEq, Repr

def rowDemand (plan : Plan) : Row → Nat
  | [value] => demand plan.shape value
  | _ => 0

def slotDemand (plan : Plan) (rows : List Row) : Nat := sumDemand (rowDemand plan) rows

/-- Check demand before building the canonical trace. -/
def project (limits : Limits) (plan : Plan) (rows : List Row) : Except Error (List Atom) := do
  if rows.length > limits.maxRows then throw (.rowLimit rows.length)
  let slots := slotDemand plan rows
  if slots > limits.maxSlots then throw (.slotLimit slots)
  let some input := Projection.trace plan rows | throw .projection
  return input

/-- Partition a trace by later starts at or above the current LIST
boundary. The first atom of each segment is retained. -/
def splitFrom (depth : Nat) :
    List Atom → List Atom → List (List Atom) → List (List Atom)
  | [], active, closed => (active.reverse :: closed).reverse
  | first :: rest, active, closed =>
    if first.repetition ≤ depth then
      splitFrom depth rest [first] (active.reverse :: closed)
    else
      splitFrom depth rest (first :: active) closed

def split (depth : Nat) : List Atom → List (List Atom)
  | [] => []
  | first :: rest => splitFrom depth rest [first] []

/-- Read a single value under its original definition base. A null or empty
container consumes exactly its one marker, while any child has to pass
the container's repeated wrapper. -/
def assemble : Shape → Nat → Nat → List Atom → Option Cell
  | _, _, _, [] => none
  | .signed site kind, _, base, [atom] =>
    if site.nullable && atom.definition == base && atom.word.isNone then some none
    else if atom.definition = base + site.nullable.toNat then signedCell kind atom.word
    else none
  | .signed .., _, _, _ :: _ :: _ => none
  | .list node child, depth, base, input@(first :: rest) =>
    let empty := base + node.site.nullable.toNat
    if node.site.nullable && first.definition == base then
      if rest.isEmpty && first.word.isNone then some none else none
    else if first.definition = empty then
      if rest.isEmpty && first.word.isNone then some (some (.list [])) else none
    else if first.definition > empty then
      ((split (depth + 1) input).mapM (assemble child (depth + 1) (empty + 1))).map
        (fun cells => some (.list cells))
    else none

def assembleRows (plan : Plan) (slices : List (List Atom)) (start : Nat := 0) : Except Error (List Row) :=
  (slices.zipIdx start).mapM fun (segment, ordinal) =>
    match assemble plan.shape 0 0 segment with
    | some value => pure [value]
    | none => throw (.shape ordinal)

/-- Publish a batch only when the independent complete projection
reproduces every input level and aligned signed word. -/
def reconstruct (limits : Limits) (plan : Plan) (expected : Nat) (input : List Atom) :
    Except Error Observation := do
  if expected > limits.maxRows then throw (.rowLimit expected)
  if input.length > limits.maxSlots then throw (.slotLimit input.length)
  let slices := split 0 input
  if slices.length ≠ expected then throw (.rowCount expected slices.length)
  let rows ← assembleRows plan slices
  if Relation plan input rows then return ⟨expected, rows⟩ else throw .traceMismatch

def rowWords (plan : Plan) (row : Row) : List Word := row.flatMap (words plan.shape)

structure ObservationWire (limits : Limits) (plan : Plan) (input : List Atom)
    (expected : Nat) (out : Observation) : Prop where
  rowBudget : expected ≤ limits.maxRows
  slotBudget : input.length ≤ limits.maxSlots
  original : Relation plan input out.rows
  count : out.rows.length = expected
  rowCount : out.rowCount = expected
  typed : ∀ row ∈ out.rows, RowFits plan.arrow.fields row
  words : out.rows.flatMap (rowWords plan) = input.filterMap Atom.word

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows
