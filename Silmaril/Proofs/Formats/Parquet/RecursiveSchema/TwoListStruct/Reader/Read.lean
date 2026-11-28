module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms
import Mathlib.Data.List.Forall2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct (Plan Compiled Side)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {out : α}
    (read : first.mapError wrap = .ok out) : first = .ok out := by
  cases first with
  | error => contradiction
  | ok => exact congrArg Except.ok (Except.ok.inj read)

public theorem path_levels (plan : Plan) (side : Side) :
    (plan.path side).shape.repetitions = 2 ∧
      (plan.path side).shape.definitions = plan.sharedDefinition + (plan.child side).1.nullable.toNat ∧
      RecursiveSchema.ListPath.Chunk.wrappers (plan.path side) =
        [plan.outer.site.nullable.toNat, plan.listDefinition - 1] := by
  cases outer : plan.outer.site.nullable <;> cases inner : plan.inner.site.nullable <;>
    cases element : plan.element.nullable <;>
    cases child : (plan.child side).1.nullable <;> cases side <;>
    simp_all [Plan.path, Plan.child, Side.select, Plan.sharedDefinition, Plan.listDefinition,
      RecursiveSchema.ListPath.Plan.shape, RecursiveSchema.ListPath.Shape.repetitions,
      RecursiveSchema.ListPath.Shape.definitions, RecursiveSchema.ListPath.Chunk.wrappers,
      RecursiveSchema.ListPath.Shape.steps, RecursiveSchema.TwoList.ListSite.enter,
      RecursiveSchema.Repeated.Context.enterList, RecursiveSchema.Repeated.Context.enter,
      RecursiveSchema.Repeated.Step.wrapper?, List.zipIdx]

public theorem optional_step (plan : Plan) (side : Side) (optional : plan.element.nullable = true) :
    ((plan.path side).shape.steps {})[plan.listDefinition]? =
      some (.optional plan.element.location .element) := by
  cases outer : plan.outer.site.nullable <;> cases inner : plan.inner.site.nullable <;>
    cases child : (plan.child side).1.nullable <;>
    simp [Plan.path, Plan.listDefinition, RecursiveSchema.ListPath.Plan.shape,
      RecursiveSchema.ListPath.Shape.steps, RecursiveSchema.TwoList.ListSite.enter,
      RecursiveSchema.Repeated.Context.enterList, RecursiveSchema.Repeated.Context.enter,
      RecursiveSchema.Repeated.Context.role, optional, outer, inner, child]

public theorem column_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} (read : readColumn limits binding = .ok out) :
    ColumnWire limits binding out :=
  ⟨(RecursiveSchema.ListPath.Chunk.readCarrier_wire read).1⟩

private theorem column_data_page {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} {page : RecursiveSchema.ListPath.Chunk.ObservedPage}
    (wire : ColumnWire limits binding out) (member : page ∈ out.pages) :
    let carrier := carrierOf binding
    Page.readPage limits.framing carrier.source carrier.span page.frame.header.start = .ok page.frame ∧
    RecursiveSchema.ListPath.Chunk.DataPageWire limits carrier.plan (RecursiveSchema.ListPath.Chunk.wrappers carrier.plan)
      carrier.source page.frame page.start (carrier.slots - page.start.slots) carrier.rows page.decoded
      carrier.codec out.dictionary := by
  have header := wire.original.originalHeader (frame := page.frame)
    (List.mem_append_right _ (List.mem_map_of_mem member))
  exact ⟨header, wire.original.checked.page_of_mem member⟩

public theorem column_v1_page {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} {page : RecursiveSchema.ListPath.Chunk.ObservedPage}
    {info : Page.DataV1} (wire : ColumnWire limits binding out) (member : page ∈ out.pages)
    (version : page.frame.value.kind = .dataV1 info) :
    let carrier := carrierOf binding
    Page.readPage limits.framing carrier.source carrier.span page.frame.header.start = .ok page.frame ∧
    ∃ encoding, encoding.From out.dictionary ∧
      RecursiveSchema.ListPath.Chunk.PageWire limits carrier.plan (RecursiveSchema.ListPath.Chunk.wrappers carrier.plan)
        carrier.source page.frame page.start (carrier.slots - page.start.slots) carrier.rows page.decoded
        carrier.codec encoding := by
  obtain ⟨header, pageWire⟩ := column_data_page wire member
  refine ⟨header, ?_⟩
  cases pageWire with
  | v1 fromTable v1 => exact ⟨_, fromTable, v1⟩
  | v2 _ v2 =>
    obtain ⟨_, _, _, _, kind, _⟩ := v2.original
    rw [version] at kind
    contradiction

public theorem column_v2_page {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : RecursiveSchema.ListPath.Chunk.Observation} {page : RecursiveSchema.ListPath.Chunk.ObservedPage}
    {info : Page.DataV2} (wire : ColumnWire limits binding out) (member : page ∈ out.pages)
    (version : page.frame.value.kind = .dataV2 info) :
    let carrier := carrierOf binding
    Page.readPage limits.framing carrier.source carrier.span page.frame.header.start = .ok page.frame ∧
    ∃ encoding, encoding.From out.dictionary ∧
      RecursiveSchema.ListPath.Chunk.V2PageWire limits carrier.plan (RecursiveSchema.ListPath.Chunk.wrappers carrier.plan)
        carrier.source page.frame page.start (carrier.slots - page.start.slots) carrier.rows page.decoded
        carrier.codec encoding := by
  obtain ⟨header, pageWire⟩ := column_data_page wire member
  refine ⟨header, ?_⟩
  cases pageWire with
  | v1 _ v1 =>
    obtain ⟨_, _, _, _, kind, _⟩ := v1.original
    rw [version] at kind
    contradiction
  | v2 fromTable v2 => exact ⟨_, fromTable, v2⟩

public theorem group_checked {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits} {out : Observation}
    (read : readGroup limits schema group = .ok out) :
    GroupWire limits schema group out ∧ (∀ row ∈ out.rows, RowFits schema.plan.arrow.fields row) := by
  unfold readGroup at read
  obtain ⟨bound, _, read⟩ := bind_ok read
  obtain ⟨left, _, read⟩ := bind_ok read
  obtain ⟨right, _, read⟩ := bind_ok read
  obtain ⟨leftOriginal, leftRead, read⟩ := bind_ok read
  obtain ⟨rightOriginal, rightRead, read⟩ := bind_ok read
  obtain ⟨⟨⟩, joined, read⟩ := bind_ok read
  obtain ⟨leftRows, leftLogical, read⟩ := bind_ok read
  obtain ⟨rightRows, rightLogical, read⟩ := bind_ok read
  split at read
  · rename_i rows merged
    cases Except.ok.inj read
    have topology := RecursiveSchema.TwoListStruct.Rows.checkTopology_wire (from_mapError joined)
    have leftExact := RecursiveSchema.ListPath.Rows.reconstruct_wire (from_mapError leftLogical)
    have rightExact := RecursiveSchema.ListPath.Rows.reconstruct_wire (from_mapError rightLogical)
    have projections := RecursiveSchema.TwoListStruct.Rows.mergeRows_wire merged
    have count := (RecursiveSchema.TwoListStruct.Rows.projectRows_count (projections .left)).symm.trans leftExact.count
    refine ⟨⟨bound, left, right, leftOriginal, rightOriginal, column_wire (from_mapError leftRead),
      column_wire (from_mapError rightRead), rfl, count, topology, ?_⟩,
      RecursiveSchema.TwoListStruct.Rows.mergeRows_typed merged leftExact.typed rightExact.typed⟩
    intro side
    cases side with
    | left => exact ⟨_, projections .left, leftExact.original⟩
    | right => exact ⟨_, projections .right, rightExact.original⟩
  · contradiction

private theorem bind_other_error {α β ε δ : Type} {first : Except ε α} {next : α → Except δ β}
    {wrap : ε → δ} {cause : δ} (different : ∀ reason, wrap reason ≠ cause)
    (read : (first.mapError wrap >>= next) = .error cause) :
    ∃ found, first = .ok found ∧ next found = .error cause := by
  cases first with
  | ok result => exact ⟨result, rfl, read⟩
  | error reason => exact (different reason (Except.error.inj read)).elim

public theorem group_topology_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {cause : RecursiveSchema.TwoListStruct.Rows.TopologyError}
    (read : readGroup limits schema group = .error (.topology cause)) :
    GroupTopologyFailure limits schema group cause := by
  unfold readGroup at read
  have bindingDiff : ∀ reason, Error.binding reason ≠ .topology cause := by simp
  have chunkDiff : ∀ reason, Error.chunk reason ≠ .topology cause := by simp
  have childDiff : ∀ column reason, Error.child column reason ≠ .topology cause := by simp
  obtain ⟨bound, _, read⟩ := bind_other_error bindingDiff read
  obtain ⟨left, _, read⟩ := bind_other_error bindingDiff read
  obtain ⟨right, _, read⟩ := bind_other_error bindingDiff read
  obtain ⟨lhs, leftRead, read⟩ := bind_other_error chunkDiff read
  obtain ⟨rhs, rightRead, read⟩ := bind_other_error chunkDiff read
  let first := address schema.plan group .left
  let other := address schema.plan group .right
  change ((RecursiveSchema.TwoListStruct.Rows.checkTopology schema.plan.sharedDefinition first other
    (RecursiveSchema.TwoListStruct.Rows.addressed first lhs)
    (RecursiveSchema.TwoListStruct.Rows.addressed other rhs) 0).mapError Error.topology >>= _) = _ at read
  cases compared : RecursiveSchema.TwoListStruct.Rows.checkTopology schema.plan.sharedDefinition first other
      (RecursiveSchema.TwoListStruct.Rows.addressed first lhs)
      (RecursiveSchema.TwoListStruct.Rows.addressed other rhs) 0 with
  | ok =>
    simp only [compared, Bind.bind, Except.bind, Except.mapError] at read
    obtain ⟨_, _, read⟩ := bind_other_error (childDiff _) read
    obtain ⟨_, _, read⟩ := bind_other_error (childDiff _) read
    split at read
    · simp [pure, Except.pure] at read
    · exact Error.noConfusion (Except.error.inj read)
  | error actual =>
    simp only [compared, Bind.bind, Except.bind, Except.mapError, Except.error.injEq, Error.topology.injEq] at read
    subst actual
    exact ⟨bound, left, right, lhs, rhs, column_wire leftRead, column_wire rightRead,
      RecursiveSchema.TwoListStruct.Rows.checkTopology_failure compared⟩

private theorem mapM_wire {α β ε : Type} {f : α → Except ε β} {input : List α} {out : List β}
    (read : input.mapM f = .ok out) : List.Forall₂ (fun item value => f item = .ok value) input out := by
  induction input generalizing out with
  | nil =>
    cases Except.ok.inj read
    exact .nil
  | cons first rest ih =>
    rw [List.mapM_cons] at read
    obtain ⟨_, firstRead, read⟩ := bind_ok read
    obtain ⟨_, restRead, result⟩ := bind_ok read
    cases Except.ok.inj result
    exact .cons firstRead (ih restRead)

public theorem all_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Limits} {out : List Observation}
    (read : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  List.Forall₂.imp (fun _ _ accepted => (group_checked accepted).1) (mapM_wire read)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader
