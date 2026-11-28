module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

/-! Original addressed leaf streams and bounded occurrence windows.
Only repetitions at or above a shared wrapper delimit its occurrences. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Occurrences

open RecursiveSchema (Location)
open RecursiveSchema.ListPath.Rows (Atom)
open Repeated.Rows (Point)
open Arrow.RecursiveSchema.Batch.Rows (Cell Row)

@[expose] public section

structure Addressed where
  point : Point
  atom : Atom
  deriving DecidableEq, Repr

structure Tape where
  slots : Array Addressed
  finish : Point

def addressed (carrier : RecursiveSchema.ListPath.Chunk.Carrier)
    (original : RecursiveSchema.ListPath.Chunk.Observation) : List Addressed :=
  (original.pages.zipIdx original.dictionary.isSome.toNat).flatMap fun (page, ordinal) =>
    (page.decoded.atoms.zipIdx page.start.slots).map fun (atom, slot) =>
      ⟨⟨carrier.address, ordinal, page.frame.header.start, slot⟩, atom⟩

def Tape.ofRead (carrier : RecursiveSchema.ListPath.Chunk.Carrier)
    (original : RecursiveSchema.ListPath.Chunk.Observation) : Tape :=
  ⟨(addressed carrier original).toArray,
    ⟨carrier.address, original.frames.length, carrier.span.stop, original.stop.slots⟩⟩

def Tape.atoms (tape : Tape) : List Atom :=
  tape.slots.toList.map (·.atom)

inductive Boundary where
  | slot (point : Point)
  | end (point : Point)
  deriving DecidableEq, Repr

def Boundary.point : Boundary → Point
  | .slot point | .end point => point

def Tape.boundary (tape : Tape) (index : Nat) : Boundary :=
  match tape.slots[index]? with
  | some entry => .slot entry.point
  | none => .end tape.finish

structure Slice where
  tape : Tape
  start : Nat
  stop : Nat
  ordered : start ≤ stop
  within : stop ≤ tape.slots.size

def Tape.full (tape : Tape) : Slice :=
  ⟨tape, 0, tape.slots.size, Nat.zero_le _, Nat.le_refl _⟩

def Slice.empty (slice : Slice) : Bool := slice.start == slice.stop

def Slice.boundary (slice : Slice) : Boundary := slice.tape.boundary slice.start

def Slice.first (slice : Slice) : Option Addressed :=
  if slice.start < slice.stop then slice.tape.slots[slice.start]? else none

/-- Advance only over slots from proper descendant continuations.
The bound counts remaining slots in the same original leaf window. -/
def seek (tape : Tape) (depth : Nat) (start : Nat) :
    (remaining : Nat) → {stop : Nat // start ≤ stop ∧ stop ≤ start + remaining}
  | 0 => ⟨start, Nat.le_refl _, Nat.le_refl _⟩
  | remaining + 1 =>
    if (tape.slots[start]?.any (fun entry => depth < entry.atom.repetition)) then
      let ⟨stop, low, high⟩ := seek tape depth (start + 1) remaining
      ⟨stop, by omega, by omega⟩
    else ⟨start, Nat.le_refl _, by omega⟩
termination_by n => n

/-- Split one occurrence at the current wrapper depth. The suffix is
retained as a view of the same tape, so its boundary remains original. -/
def Slice.take (slice : Slice) (depth : Nat) : Option (Slice × Slice) :=
  if valid : slice.start < slice.stop then
    let next := seek slice.tape depth (slice.start + 1) (slice.stop - (slice.start + 1))
    have low := next.property.1
    have high := next.property.2
    some (⟨slice.tape, slice.start, next.val, by omega, by have := slice.within; omega⟩,
      ⟨slice.tape, next.val, slice.stop, by omega, slice.within⟩)
  else none

structure Position where
  row : Nat
  /-- Inmost occurrence first, for constant-time descent. -/
  repeated : List (Location × Nat) := []
  deriving DecidableEq, Repr

inductive Marker where
  | null
  | empty
  | present
  deriving DecidableEq, Repr

inductive Fault where
  | presence (position : Position) (site : Location) (left right : Boundary) (expected actual : Marker)
  | cardinality (position : Position) (site : Option Location) (present absent : Boundary)
  | atom (position : Position) (site : Location) (atSlot : Boundary)
  | depth (position : Position) (site : Location)
  | occurrences (position : Position) (site : Location)
  | shape (position : Position)
  | slots (actual : Nat)
  | rows (expected actual : Nat)
  | projection
  | provenance
  deriving DecidableEq, Repr

def Fault.shared : Fault → Prop
  | .presence .. | .cardinality .. => True
  | _ => False

def fieldLocation : Repeated.Field → Location
  | .leaf plan => plan.site.location
  | .group site _ | .list site _ _ => site.location

/-- Descendant widths indexed by original declaration ordinal. Compute once
from the compiler paths before walking or projecting any row. -/
def widths (declarationCount : Nat) (leaves : Array LeafPlan) : Array Nat :=
  leaves.foldl (fun counts leaf =>
    leaf.path.ancestors.foldl (fun next ancestor => next.modify ancestor.site.location.ordinal (· + 1))
      (counts.modify leaf.path.site.location.ordinal (· + 1))) (Array.replicate (declarationCount + 1) 0)

def width (widths : Array Nat) (field : Repeated.Field) : Nat :=
  widths[(fieldLocation field).ordinal]?.getD 0

end

private def slotMarker (position : Position) (site : Location) (base : Nat) (nullable list : Bool)
    (slice : Slice) : Except Fault Marker := do
  let failure := Fault.atom position site slice.boundary
  let some first := slice.first | throw failure
  let present := base + nullable.toNat
  let oneMarker := slice.start + 1 == slice.stop && first.atom.word.isNone
  if nullable && first.atom.definition == base then
    if oneMarker then return .null else throw failure
  else if list && first.atom.definition == present then
    if oneMarker then return .empty else throw failure
  else if present + list.toNat ≤ first.atom.definition then
    return .present
  else throw failure

/-- Share only the marker at this original schema node. Slots below this
occurrence are left to the individual descendant cursors. -/
private def commonMarker (position : Position) (site : Location) (base : Nat) (nullable list : Bool)
    (columns : List Slice) : Except Fault Marker := do
  let first :: rest := columns | throw (.shape position)
  let expected ← slotMarker position site base nullable list first
  for other in rest do
    let actual ← slotMarker position site base nullable list other
    if actual ≠ expected then throw (.presence position site first.boundary other.boundary expected actual)
  return expected

/-- Advance each participating leaf once. The first column determines
which direction to report when one cursor has reached its boundary. -/
private def takeTogether (position : Position) (site : Option Location) (depth : Nat)
    (columns : List Slice) : Except Fault (Option (List Slice × List Slice)) := do
  let first :: rest := columns | throw (.shape position)
  match first.take depth with
  | none =>
    if let some present := rest.find? (fun slice => !slice.empty) then
      throw (.cardinality position site present.boundary first.boundary)
    return none
  | some (head, tail) =>
    let others ← rest.mapM fun other =>
      match other.take depth with
      | some pieces => .ok pieces
      | none => .error (.cardinality position site first.boundary other.boundary)
    return some (head :: others.map Prod.fst, tail :: others.map Prod.snd)

private def buildFields (read : Repeated.Field → List Slice → Except Fault Cell)
    (widths : Array Nat) (position : Position) : List Repeated.Field → List Slice → Except Fault Row
  | [], columns => if columns.isEmpty then .ok [] else .error (.shape position)
  | first :: tail, columns => do
    let (selected, rest) := columns.splitAt (width widths first)
    let value ← read first selected
    return value :: (← buildFields read widths position tail rest)

private def buildElements (read : Position → List Slice → Except Fault Cell)
    (position : Position) (site wrapper : Location) (depth : Nat) :
    Nat → Nat → List Slice → List Cell → Except Fault (List Cell)
  | 0, _, columns, reversed =>
    if columns.all Slice.empty then .ok reversed.reverse else .error (.occurrences position site)
  | remaining + 1, ordinal, columns, reversed => do
    let child := { position with repeated := (wrapper, ordinal) :: position.repeated }
    match ← takeTogether child (some site) depth columns with
    | none => return reversed.reverse
    | some (selected, rest) =>
      let value ← read child selected
      buildElements read position site wrapper depth remaining (ordinal + 1) rest (value :: reversed)

private def buildField (widths : Array Nat) (slotBudget : Nat) :
    Nat → Position → Nat → Nat → Repeated.Field → List Slice → Except Fault Cell
  | 0, position, _, _, field, _ => .error (.depth position (fieldLocation field))
  | fuel + 1, position, depth, base, field, columns => do
    match field with
    | .leaf plan =>
      let [slice] := columns | throw (.shape position)
      let failure := Fault.atom position plan.site.location slice.boundary
      let some first := slice.first | throw failure
      if slice.stop ≠ slice.start + 1 then throw failure
      if plan.site.nullable && first.atom.definition == base && first.atom.word.isNone then return none
      if first.atom.definition ≠ base + plan.site.nullable.toNat then throw failure
      let some value := RecursiveSchema.ListPath.Rows.signedCell plan.kind first.atom.word | throw failure
      return value
    | .group site children =>
      match ← commonMarker position site.location base site.nullable false columns with
      | .null => return none
      | .empty => throw (.shape position)
      | .present =>
        let read := buildField widths slotBudget fuel position depth (base + site.nullable.toNat)
        return some (.struct (← buildFields read widths position children columns))
    | .list site wrapper child =>
      match ← commonMarker position site.location base site.nullable true columns with
      | .null => return none
      | .empty => return some (.list [])
      | .present =>
        let read := fun atChild => buildField widths slotBudget fuel atChild (depth + 1)
          (base + site.nullable.toNat + 1) child
        return some (.list (← buildElements read position site.location wrapper (depth + 1) slotBudget 0 columns []))

private def buildRows (widths : Array Nat) (slotBudget fuel : Nat) (fields : List Repeated.Field) (expected : Nat) :
    Nat → Nat → List Slice → List Row → Except Fault (List Row)
  | 0, _, columns, reversed =>
    if columns.all Slice.empty then .ok reversed.reverse else .error (.rows expected (expected + 1))
  | remaining + 1, ordinal, columns, reversed => do
    let position : Position := ⟨ordinal, []⟩
    let some (selected, rest) ← takeTogether position none 0 columns | throw (.rows expected ordinal)
    let row ← buildFields (buildField widths slotBudget fuel position 0 0) widths position fields selected
    buildRows widths slotBudget fuel fields expected remaining (ordinal + 1) rest (row :: reversed)

public def assemble (widths : Array Nat) (slotBudget depth : Nat) (fields : List Repeated.Field)
    (expected : Nat) (columns : Array Tape) : Except Fault (List Row) :=
  buildRows widths slotBudget depth fields expected expected 0 (columns.toList.map Tape.full) []

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Occurrences
