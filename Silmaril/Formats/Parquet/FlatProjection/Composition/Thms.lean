module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition

open Arrow.MixedFlat

/-- Positional lookup commutes with a field or column observation map. -/
theorem select_map {α β : Type} (f : α → β) (positions : List Nat) (values : List α) :
    select positions (values.map f) = (select positions values).map (List.map f) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.select_map
    f positions values

/-- Selecting checked bindings gives the exact direct bindings on the same snapshot. -/
theorem select_bound {snapshot : Snapshot.Checked} {ordinals positions composed : List Nat}
    {original direct : List (Bound snapshot)}
    (composition : composeOrdinals ordinals positions = some composed)
    (originalBind : bindProjection snapshot ordinals = .ok original)
    (directBind : bindProjection snapshot composed = .ok direct) :
    select positions original = some direct :=
  Proofs.Formats.Parquet.FlatProjection.Composition.select_bound
    composition originalBind directBind

/-- Comparable completed source reads agree under positional composition,
including repeated and empty selections. Source file admission can use
different row and field caps. IPC admission is independent. -/
theorem project_compose {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked}
    {wide narrow : List OrderedWriter.BatchInput}
    (sameColumnPolicy : originalLimits.column = directLimits.column)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide)
    (directRead : direct.readAll directLimits = .ok narrow) :
    project positions (observe original wide) = some (observe direct narrow) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.project_compose
    sameColumnPolicy composition originalOpen directOpen originalRead directRead

/-- A composed projection opens under its own file, row and field caps. -/
theorem open_compose {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original : Checked}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct, openFile directLimits input composed = .ok direct :=
  Proofs.Formats.Parquet.FlatProjection.Composition.open_compose
    same composition originalOpen fileBytes rows fields

/-- Successful wider exhaustion guarantees successful direct exhaustion after source admission. -/
theorem project_compose_success {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original direct : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (directOpen : openFile directLimits input composed = .ok direct)
    (originalRead : original.readAll originalLimits = .ok wide) :
    ∃ narrow, direct.readAll directLimits = .ok narrow ∧
      project positions (observe original wide) = some (observe direct narrow) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.project_compose_success
    same composition originalOpen directOpen originalRead

/-- With explicit direct source caps, both open and exhaustion succeed and return the selected observation. -/
theorem project_compose_of_caps {originalLimits directLimits : FlatProjection.Limits} {input : Bytes}
    {ordinals positions composed : List Nat} {original : Checked} {wide : List OrderedWriter.BatchInput}
    (same : SameColumnPolicy originalLimits directLimits)
    (composition : composeOrdinals ordinals positions = some composed)
    (originalOpen : openFile originalLimits input ordinals = .ok original)
    (originalRead : original.readAll originalLimits = .ok wide)
    (fileBytes : input.length ≤ directLimits.column.maxFileBytes)
    (rows : original.snapshot.metadata.numRows.toNat ≤ directLimits.maxFileRows)
    (fields : composed.length ≤ directLimits.maxFields) :
    ∃ direct narrow, openFile directLimits input composed = .ok direct ∧ direct.readAll directLimits = .ok narrow ∧
      project positions (observe original wide) = some (observe direct narrow) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.project_compose_of_caps
    same composition originalOpen originalRead fileBytes rows fields

/-- Projection preserves the row count at every original batch ordinal. -/
theorem project_rowCounts {positions : List Nat} {original direct : Observation}
    (projected : project positions original = some direct) :
    direct.batches.map Prod.fst = original.batches.map Prod.fst :=
  Proofs.Formats.Parquet.FlatProjection.Composition.project_rowCounts
    projected

end Silmaril.Formats.Parquet.FlatProjection.Composition
