module

public import Silmaril.Formats.Dasl.IndexSequence.Thms
public import Silmaril.Formats.PER.EGraph.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.EGraph

open Silmaril.Formats.PER.EGraph
open Silmaril.Semantics.Naming (Relation)

variable {Operator Name Cas : Type} {size classes : Nat} {dag : Dag Operator}

/-- The `classId` profile only: row `i` witnesses DAG term `i`. The class
count is independent of the number of witnesses. -/
structure Table (dag : Dag Operator) (Name : Type) (classes : Nat) where
  rows : IndexSequence.Checked (.classId classes) Name
  width : rows.val.length = dag.val.size

def Table.entry (table : Table dag Name classes) (id : dag.Id) : Name × Nat :=
  table.rows.val.get (Fin.cast table.width.symm id)

/-- Structural interpretation only. Class equality is not yet justified. -/
def Table.partition (table : Table dag Name classes) : Partition dag.val.size :=
  ⟨classes, fun id => ⟨(table.entry id).2, table.rows.property (Fin.cast table.width.symm id)⟩⟩

def Table.Named (table : Table dag Name classes) (names : Relation Name Nat) : Prop :=
  ∀ id : dag.Id, names (table.entry id).1 id.val

abbrev NamedTable (dag : Dag Operator) (classes : Nat) (names : Relation Name Nat) :=
  { table : Table dag Name classes // table.Named names }

/-- Check witness count and each claimed name-to-term binding. This does not
impose global name uniqueness or require enumerating all allowed bindings. -/
def checkTable? (dag : Dag Operator) (names : Relation Name Nat) [DecidableRel names]
    (rows : IndexSequence.Checked (.classId classes) Name) : Option (NamedTable dag classes names) :=
  if width : rows.val.length = dag.val.size then
    let table : Table dag Name classes := ⟨rows, width⟩
    letI : Decidable (table.Named names) :=
      inferInstanceAs (Decidable (∀ id : dag.Id, names (table.entry id).1 id.val))
    if named : table.Named names then some ⟨table, named⟩ else none
  else none

/-- An untrusted proposal uses the existing partition boundary, not a parent forest. -/
structure Step (size : Nat) where
  left : Fin size
  right : Fin size
  reason : Reason
  proposed : Partition size

def replayFrom? [DecidableEq Operator] (dag : Dag Operator) (seeds : Seeds dag.val.size) :
    Partition dag.val.size → List (Step dag.val.size) → Option (Partition dag.val.size)
  | current, [] => some current
  | current, step :: rest => do
    let accepted ← dag.merge? seeds current step.proposed step.left step.right step.reason
    replayFrom? dag seeds accepted.val rest

/-- Only the supplied finite list is replayed, starting with singleton classes. -/
def replay? [DecidableEq Operator] (dag : Dag Operator) (seeds : Seeds dag.val.size)
    (steps : List (Step dag.val.size)) : Option (Partition dag.val.size) :=
  replayFrom? dag seeds ⟨dag.val.size, id⟩ steps

/-- Compare the induced equivalence, not numeric labels or class counts. -/
def Agrees (table audited : Partition size) : Prop :=
  ∀ left right, table.classOf left = table.classOf right ↔ audited.classOf left = audited.classOf right

def certify? [DecidableEq Operator] (dag : Dag Operator) (seeds : Seeds dag.val.size)
    (names : Relation Name Nat) [DecidableRel names] (steps : List (Step dag.val.size))
    (rows : IndexSequence.Checked (.classId classes) Name) : Option (NamedTable dag classes names) := do
  let table ← checkTable? dag names rows
  let audited ← replay? dag seeds steps
  letI : Decidable (Agrees table.val.partition audited) :=
    inferInstanceAs (Decidable (∀ left right,
      table.val.partition.classOf left = table.val.partition.classOf right ↔ audited.classOf left = audited.classOf right))
  if Agrees table.val.partition audited then some table else none

def decodeCertified? [DecidableEq Operator] (dag : Dag Operator) (seeds : Seeds dag.val.size)
    (names : Relation Name Nat) [DecidableRel names] (steps : List (Step dag.val.size)) (classes : Nat)
    (codec : IndexSequence.SequenceCodec (Name × Nat) Cas) (raw : Shallow Cas) : Option (NamedTable dag classes names) :=
  ((IndexSequence.checked (.classId classes) codec).decode? raw).bind (certify? dag seeds names steps)

end Silmaril.Formats.Dasl.EGraph
