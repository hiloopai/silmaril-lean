module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

/-! Logical Arrow batches for the checked two-LIST Parquet leaf. The inverse
projection takes only the declaration and logical rows. It uses no cursor,
page boundary, classification or source byte evidence. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows

open Arrow.RecursiveSchema (Schema)
open Arrow.RecursiveSchema.Batch.Rows (Cell Row Observation RowFits)

@[expose] public section

def leafField (plan : Plan) : Arrow.RecursiveSchema.Field :=
  .node (some plan.leaf.name) plan.leaf.nullable plan.kind.arrow []

def innerField (plan : Plan) : Arrow.RecursiveSchema.Field :=
  .node (some plan.inner.site.name) plan.inner.site.nullable .list [leafField plan]

def outerField (plan : Plan) : Arrow.RecursiveSchema.Field :=
  .node (some plan.outer.site.name) plan.outer.site.nullable .list [innerField plan]

def arrowSchema (plan : Plan) : Schema := ⟨[outerField plan]⟩

structure Atom where
  repetition : Nat
  definition : Nat
  word : Option Chunk.Word
  deriving DecidableEq, Repr

def pageAtoms (decoded : Chunk.Decoded) : List Atom :=
  decoded.levels.zipWith (fun slot word => ⟨slot.repetition, slot.definition, word⟩) decoded.words

def atoms (pages : List Chunk.ObservedPage) : List Atom :=
  pages.flatMap (fun page => pageAtoms page.decoded)

def cellWord : Cell → Option Chunk.Word
  | some (.int32 word) => some (.int32 word)
  | some (.int64 word) => some (.int64 word)
  | _ => none

def elements : Cell → List Cell
  | some (.list children) => children
  | _ => []

def innerWords (cell : Cell) : List Chunk.Word :=
  (elements cell).flatMap (fun value => (cellWord value).toList)

def outerWords (cell : Cell) : List Chunk.Word :=
  (elements cell).flatMap innerWords

def rowWords (row : Row) : List Chunk.Word := row.flatMap outerWords

namespace Projection

def children (emit : Nat → Cell → Option (List Atom)) (headRep tailRep : Nat)
    (head : Cell) (tail : List Cell) : Option (List Atom) := do
  let first ← emit headRep head
  let rest ← tail.mapM (emit tailRep)
  return first ++ rest.flatten

def leaf (plan : Plan) (rep : Nat) : Cell → Option (List Atom)
  | none =>
    if plan.leaf.nullable then some [⟨rep, plan.innerEmpty + 1, none⟩] else none
  | some (.int32 word) =>
    if plan.kind = .int32 then some [⟨rep, plan.maxDefinition, some (.int32 word)⟩] else none
  | some (.int64 word) =>
    if plan.kind = .int64 then some [⟨rep, plan.maxDefinition, some (.int64 word)⟩] else none
  | _ => none

def inner (plan : Plan) (rep : Nat) : Cell → Option (List Atom)
  | none =>
    if plan.inner.site.nullable then some [⟨rep, plan.outerEmpty + 1, none⟩] else none
  | some (.list []) => some [⟨rep, plan.innerEmpty, none⟩]
  | some (.list (head :: tail)) => children (leaf plan) rep 2 head tail
  | _ => none

def outer (plan : Plan) : Cell → Option (List Atom)
  | none => if plan.outer.site.nullable then some [⟨0, 0, none⟩] else none
  | some (.list []) => some [⟨0, plan.outerEmpty, none⟩]
  | some (.list (head :: tail)) => children (inner plan) 0 1 head tail
  | _ => none

def row (plan : Plan) : Row → Option (List Atom)
  | [cell] => outer plan cell
  | _ => none

def trace (plan : Plan) (rows : List Row) : Option (List Atom) :=
  (rows.mapM (row plan)).map List.flatten

end Projection

/-- Logical rows independently denote exactly the original ordered levels
and aligned words. Outer rows and their inner lists come from the logical
shape, without access to source page boundaries or from-reader tags. -/
def Relation (plan : Plan) (input : List Atom) (rows : List Row) : Prop :=
  Projection.trace plan rows = some input

instance (plan : Plan) (input : List Atom) (rows : List Row) : Decidable (Relation plan input rows) := by
  unfold Relation
  infer_instance

inductive Error where
  | binding (original : Chunk.BindError)
  | chunk (original : Chunk.Error)
  | leadingContinuation (repetition : Nat)
  | rowShape (row : Nat)
  | innerShape (row : Nat)
  | leafShape (row : Nat)
  | rowCount (expected actual : Nat)
  | projection
  deriving DecidableEq, Repr

/-- Keep the event that starts each slice. The caller supplies either the
row-start test or the test for a new inner list inside one row. -/
def partitionFrom (starts : Atom → Bool) :
    List Atom → List (List Atom) → List Atom → Except Error (List (List Atom))
  | [], done, [] => .ok done.reverse
  | [], done, active@(_ :: _) => .ok (active.reverse :: done).reverse
  | first :: rest, done, active =>
    if starts first then
      let done := if active.isEmpty then done else active.reverse :: done
      partitionFrom starts rest done [first]
    else if active.isEmpty then .error (.leadingContinuation first.repetition)
    else partitionFrom starts rest done (first :: active)

def partition (starts : Atom → Bool) (input : List Atom) : Except Error (List (List Atom)) :=
  partitionFrom starts input [] []

def assembleLeaf (plan : Plan) (row : Nat) (atom : Atom) : Except Error Cell :=
  match plan.presence atom.definition, atom.word with
  | some .nullValue, none => .ok none
  | some .value, some (.int32 word) => .ok (some (.int32 word))
  | some .value, some (.int64 word) => .ok (some (.int64 word))
  | _, _ => .error (.leafShape row)

def assembleInner (plan : Plan) (row : Nat) (input : List Atom) : Except Error Cell := do
  let first :: rest := input | throw (.innerShape row)
  match plan.presence first.definition with
  | some .nullInner =>
    if rest.isEmpty && first.word.isNone then return none else throw (.innerShape row)
  | some .emptyInner =>
    if rest.isEmpty && first.word.isNone then return some (.list []) else throw (.innerShape row)
  | _ => return some (.list (← input.mapM (assembleLeaf plan row)))

def assembleRow (plan : Plan) (row : Nat) (input : List Atom) : Except Error Row := do
  let first :: rest := input | throw (.rowShape row)
  match plan.presence first.definition with
  | some .nullOuter =>
    if rest.isEmpty && first.word.isNone then return [none] else throw (.rowShape row)
  | some .emptyOuter =>
    if rest.isEmpty && first.word.isNone then return [some (.list [])] else throw (.rowShape row)
  | _ =>
    let children ← partition (·.repetition < 2) input
    return [some (.list (← children.mapM (assembleInner plan row)))]

/-- Partition the entire ordered trace before assembling. A page cut never
starts or closes a row or an inner list. Check the independent projection
before publishing the Arrow observation. -/
def reconstruct (plan : Plan) (expected : Nat) (input : List Atom) :
    Except Error Observation := do
  let slices ← partition (·.repetition == 0) input
  let rows ← slices.zipIdx.mapM fun (slots, index) => assembleRow plan index slots
  if rows.length = expected then
    if Relation plan input rows then return ⟨expected, rows⟩ else throw .projection
  else throw (.rowCount expected rows.length)

def reconstructObservation (plan : Plan) (column : Chunk.Observation) : Except Error Observation :=
  reconstruct plan column.stop.rows (atoms column.pages)

def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Observation := do
  let binding ← (Chunk.bind schema group).mapError .binding
  let column ← (Chunk.read limits binding).mapError .chunk
  reconstructObservation schema.plan column

def readAll {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) : Except Error (List Observation) :=
  (List.range snapshot.groupCount).mapM (readGroup limits schema)

structure ObservationWire (plan : Plan) (input : List Atom) (expected : Nat) (output : Observation) : Prop where
  original : Relation plan input output.rows
  count : output.rows.length = expected
  rowCount : output.rowCount = expected
  typed : ∀ row ∈ output.rows, RowFits (arrowSchema plan).fields row
  words : output.rows.flatMap rowWords = input.filterMap Atom.word

structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group : Nat)
    (output : Observation) : Prop where
  original : ∃ (binding : Chunk.Binding schema group) (column : Chunk.Observation),
    Chunk.bind schema group = .ok binding ∧ Chunk.read limits binding = .ok column ∧
    Chunk.Wire limits (Chunk.carrierOf binding) column ∧
    ObservationWire schema.plan (atoms column.pages) binding.rowGroup.numRows.toNat output

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows
