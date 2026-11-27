module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc
open Silmaril.Formats.Arrow.BinaryView

theorem readSource_exact {ipc : Arrow.Limits} {view : Column.Limits} {input : KBytes} {source : Source}
    (accepted : readSource ipc view input = .ok source) :
    Stream.read ipc view input = .ok source.observed := by
  cases read : Stream.read ipc view input with
  | error cause => simp [readSource, read, Except.mapError, Bind.bind, Except.bind] at accepted
  | ok observed =>
    rcases observed with ⟨⟨name, nullable, kind⟩, batches⟩
    cases kind with
    | binary => simp [readSource, read, Except.mapError, Bind.bind, Except.bind, throw] at accepted
    | utf8 =>
      simp [readSource, read, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
      cases accepted
      rfl

private theorem readGroups_exact {limits : Utf8.FromIpc.Limits} {name : String} {layout : FlatColumn.Layout}
    {checked : Utf8.Checked name layout} {batches : List (List (Option String))}
    (read : Internal.readGroups limits checked = .ok batches) :
    List.Forall₂ (fun index slots => checked.readGroup limits.file index = .ok slots)
      (List.range checked.physical.snapshot.groupCount) batches := by
  obtain reads := List.mapM_eq_ok_iff_forall₂.mp read
  apply reads.imp
  intro index slots observed
  change (checked.readGroup limits.file index).mapError (Error.groupReadback index) = .ok slots at observed
  unfold Except.mapError at observed
  split at observed
  · contradiction
  · rename_i value current
    cases observed
    exact current

private theorem certify_wire {limits : Utf8.FromIpc.Limits} {source : Source} {raw wire : Bytes}
    (certified : Internal.certify limits source raw = .ok wire) : SinkWire limits source wire := by
  cases opened : Utf8.openFile limits.file raw source.name source.layout with
  | error cause => simp [Internal.certify, opened, Except.mapError, Bind.bind, Except.bind] at certified
  | ok checked =>
    cases read : Internal.readGroups limits checked with
    | error cause => simp [Internal.certify, opened, read, Except.mapError, Bind.bind, Except.bind] at certified
    | ok groups =>
      simp only [Internal.certify, opened, read, Except.mapError, Bind.bind, Except.bind] at certified
      split at certified
      · next agrees =>
        cases certified
        rcases agrees with ⟨schema, annotation, rfl⟩
        have reads := readGroups_exact read
        have bound := (File.openFile_wire (Utf8.openFile_wire opened).1).2.1
        refine ⟨checked, bound, opened, schema, annotation, by simpa using reads.length_eq, ?_⟩
        apply reads.imp
        intro index slots groupRead
        obtain ⟨group, octets, wire, _, rfl⟩ := Utf8.readGroup_wire groupRead
        exact ⟨groupRead, group, wire⟩
      · contradiction

theorem emit_readback {limits : Utf8.FromIpc.Limits} {source : Source} {wire : Bytes}
    (emitted : emit limits source = .ok wire) : SinkWire limits source wire := by
  cases assembled : Internal.assemble limits source with
  | error cause => simp [emit, assembled, Bind.bind, Except.bind] at emitted
  | ok raw =>
    exact certify_wire (by simpa [emit, assembled, Bind.bind, Except.bind] using emitted)

theorem convert_readback {ipc : Arrow.Limits} {view : Column.Limits} {limits : Utf8.FromIpc.Limits}
    {input : KBytes} {wire : Bytes} (written : convert ipc view limits input = .ok wire) :
    ∃ source, Stream.read ipc view input = .ok source.observed ∧
      SinkWire limits source wire ∧ input.wf = true ∧ ∃ start,
        Stream.readSchema ipc input = .ok (source.observed.field, start) ∧
        Stream.BatchesWire ipc view input source.observed.field ipc.batches start source.observed.batches := by
  cases sourceRead : readSource ipc view input with
  | error cause => simp [convert, sourceRead, Bind.bind, Except.bind] at written
  | ok source =>
    have sourceExact := readSource_exact sourceRead
    have emitted : emit limits source = .ok wire := by
      simpa [convert, sourceRead, Bind.bind, Except.bind] using written
    exact ⟨source, sourceExact, emit_readback emitted, (Stream.read_iff ipc view input _).mp sourceExact⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc
