module

public import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
import Silmaril.Formats.Parquet.ListFile.Writer.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Thms
import Silmaril.Formats.Arrow.ListInt32.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Writer.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile
open Silmaril.Formats.Parquet.ListFile.Writer.FromIpc
open Silmaril.Formats.Parquet.ListFile.Writer

public theorem convert_source_error {limits : FromIpc.Limits} {input : KBytes}
    {cause : Arrow.ListInt32.Stream.Error}
    (failed : Arrow.ListInt32.Stream.read limits.ipc input = .error cause) :
    convert limits input = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

public theorem convert_child_name {limits : FromIpc.Limits} {input : KBytes}
    {observed : Arrow.ListInt32.Stream.Observed}
    (decoded : Arrow.ListInt32.Stream.read limits.ipc input = .ok observed)
    (unsupported : observed.field.childName ≠ "element") :
    convert limits input = .error (.childName observed.field.childName) := by
  simp [convert, decoded, unsupported, Except.mapError, Bind.bind, Except.bind]
  rfl

private theorem convert_source {limits : FromIpc.Limits} {input : KBytes} {output : Writer.Encoded}
    (h : convert limits input = .ok output) :
    ∃ observed, Arrow.ListInt32.Stream.read limits.ipc input = .ok observed ∧
      observed.field.childName = "element" ∧ Writer.emit limits.parquet (writerInput observed) = .ok output := by
  unfold convert at h
  cases parsed : Arrow.ListInt32.Stream.read limits.ipc input with
  | error err => simp [parsed, Except.mapError, Bind.bind, Except.bind] at h
  | ok observed =>
    simp only [parsed, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i canonical
      cases written : Writer.emit limits.parquet (writerInput observed) with
      | error e => simp [written] at h
      | ok result =>
        rw [written] at h
        obtain rfl := Except.ok.inj h
        exact ⟨observed, rfl, not_not.mp canonical, written⟩

public theorem convert_readback {limits : FromIpc.Limits} {input : KBytes} {output : Writer.Encoded}
    (h : convert limits input = .ok output) : Readback limits input output := by
  obtain ⟨observed, parsed, child, written⟩ := convert_source h
  obtain ⟨wf, size, envelope, schema, batches⟩ := Arrow.ListInt32.Stream.read_wire parsed
  obtain ⟨checked, opened, wire, name, childName, count, read, groups⟩ := Writer.emit_readback written
  exact ⟨observed, checked, size, parsed, child, wf, envelope, schema, batches, written,
    (Writer.emit_exact written).2.1, opened, wire, name, childName, by simpa [writerInput] using count, read, groups⟩

private theorem remap_reads (limits : Multi.Limits) (checked : ListFile.Checked)
    {indices : List Nat} {groups : List (List ListPage.Row)}
    (h : indices.mapM (Multi.readGroup limits.maxGroupSlots checked) = .ok groups) :
    (indices.mapM fun index =>
      (Multi.readGroup limits.maxGroupSlots checked index).mapError (Writer.Error.groupReadback index)) =
      .ok groups := by
  induction indices generalizing groups with
  | nil => obtain rfl := Except.ok.inj h; rfl
  | cons index rest ih =>
    rw [List.mapM_cons] at h ⊢
    cases first : Multi.readGroup limits.maxGroupSlots checked index with
    | error e => simp [first, Bind.bind, Except.bind] at h
    | ok rows =>
      simp only [first, Bind.bind, Except.bind] at h
      cases later : rest.mapM (Multi.readGroup limits.maxGroupSlots checked) with
      | error e => simp [later] at h
      | ok tail =>
        rw [later] at h
        obtain rfl := Except.ok.inj h
        have mapped := ih later
        simp only [Except.mapError] at mapped
        simp only [Except.mapError, Bind.bind, Except.bind]
        rw [mapped]
        rfl

public theorem roundTrip {limits : FromIpc.Limits} {returned : Arrow.ListInt32.Stream.Limits}
    {input output : KBytes} {parquet : Writer.Encoded}
    (forward : convert limits input = .ok parquet)
    (backward : (Multi.ToIpc.convert ⟨limits.parquet.readback, returned⟩ parquet.bytes).wire = .ok output) :
    ∃ before after,
      Arrow.ListInt32.Stream.read limits.ipc input = .ok before ∧
      Arrow.ListInt32.Stream.read returned output = .ok after ∧
      observation before = observation after := by
  obtain ⟨before, checked, _, parsed, _, _, _, _, _, _, _, opened, _, name, child, _, read, _⟩ :=
    (convert_readback forward).data
  obtain ⟨reopened, groups, after, _, backOpen, _, backReads, _, _, backParsed, agrees, _, _, _, _⟩ :=
    (Multi.ToIpc.convert_readback backward).data
  rw [opened] at backOpen
  obtain rfl := Except.ok.inj backOpen
  have observed : Writer.readGroups limits.parquet.readback checked = .ok groups :=
    remap_reads limits.parquet.readback checked backReads
  rw [read] at observed
  have rows := Except.ok.inj observed
  have field : Multi.ToIpc.fieldOf checked = before.field := by
    change (⟨checked.shape.outer.name, checked.shape.element.name⟩ : Arrow.ListInt32.Field) = before.field
    rw [name, child]
  refine ⟨before, after, parsed, backParsed, ?_⟩
  unfold observation
  rw [agrees.1, agrees.2.1, ← rows, field]

end Silmaril.Proofs.Formats.Parquet.ListFile.Writer.FromIpc
