module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Thms
import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToCsv

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.ToCsv
open Silmaril.Formats.Csv.Typed.Utf8

variable {parquet : File.Limits} {source sink : OpaqueIpc.IpcLimits}
variable {exportLimits importLimits : OpaqueIpc.CsvLimits}
variable {input : Bytes} {name : String} {layout : FlatColumn.Layout}

private theorem exportSteps {output : OpaqueIpc.Output}
    (exported : exportCsv parquet source exportLimits input name layout = .ok output) :
    ∃ wire, ToIpc.convert parquet source.ipc source.view input name layout = .ok wire ∧
      OpaqueIpc.toCsv source exportLimits .binaryView wire = .ok output := by
  cases native : ToIpc.convert parquet source.ipc source.view input name layout with
  | error cause => simp [exportCsv, native, Except.mapError, Bind.bind, Except.bind] at exported
  | ok wire =>
    refine ⟨wire, rfl, ?_⟩
    cases csv : OpaqueIpc.toCsv source exportLimits .binaryView wire <;>
      simp_all [exportCsv, Except.mapError, Bind.bind, Except.bind]

private theorem nativeReadback {wire : KBytes}
    (emitted : ToIpc.convert parquet source.ipc source.view input name layout = .ok wire) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      OpaqueIpc.readIpc source .binaryView wire = .ok
        ⟨descriptor name layout, groups.map (List.map (Option.map Bytes.toList))⟩ := by
  obtain ⟨checked, groups, batches, opened, groupRead, native, slots, _, _, _⟩ :=
    ToIpc.convert_readback emitted
  exact ⟨checked, groups, opened, groupRead, by
    simp [OpaqueIpc.readIpc, native, descriptor, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
    exact slots⟩

theorem exportCsv_readback {output : OpaqueIpc.Output}
    (exported : exportCsv parquet source exportLimits input name layout = .ok output) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      output.field = descriptor name layout ∧
      OpaqueIpc.decode exportLimits output.field output.wire = .ok (groups.flatten.map (Option.map Bytes.toList)) := by
  obtain ⟨wire, native, csv⟩ := exportSteps exported
  obtain ⟨checked, groups, opened, readGroups, readWire⟩ := nativeReadback native
  obtain ⟨observed, read, field, encoded⟩ := OpaqueIpc.toCsv_observation csv
  have same := Except.ok.inj (read.symm.trans readWire)
  subst observed
  refine ⟨checked, groups, opened, readGroups, field, ?_⟩
  rw [field]
  simpa only [List.map_flatten] using OpaqueIpc.decode_encode encoded

theorem convert_readback {output : Output}
    (converted : convert parquet source sink exportLimits importLimits input name layout = .ok output) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      output.csv.field = descriptor name layout ∧
      OpaqueIpc.decode importLimits output.csv.field output.csv.wire =
        .ok (groups.flatten.map (Option.map Bytes.toList)) ∧
      OpaqueIpc.readIpc sink .binaryView output.ipc =
        .ok ⟨descriptor name layout, [groups.flatten.map (Option.map Bytes.toList)]⟩ := by
  cases csvResult : exportCsv parquet source exportLimits input name layout with
  | error cause => simp [convert, csvResult, Bind.bind, Except.bind] at converted
  | ok csv =>
    cases ipcResult : OpaqueIpc.fromCsv importLimits sink csv.field csv.wire with
    | error cause =>
      simp [convert, csvResult, ipcResult, Except.mapError, Bind.bind, Except.bind] at converted
    | ok ipc =>
      have equal : (⟨csv, ipc⟩ : Output) = output := by
        simpa [convert, csvResult, ipcResult, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
          using converted
      subst output
      obtain ⟨wire, native, exported⟩ := exportSteps csvResult
      obtain ⟨checked, groups, opened, readGroups, readWire⟩ := nativeReadback native
      obtain ⟨observed, read, field, sinkRead⟩ := OpaqueIpc.roundtrip exported ipcResult
      have same := Except.ok.inj (read.symm.trans readWire)
      subst observed
      have finalRead : OpaqueIpc.readIpc sink .binaryView ipc =
          .ok ⟨descriptor name layout, [groups.flatten.map (Option.map Bytes.toList)]⟩ := by
        simpa only [descriptor, List.map_flatten] using sinkRead
      obtain ⟨values, parsed, readback⟩ := OpaqueIpc.fromCsv_readback ipcResult
      rw [field] at readback
      have exactBatches := congrArg OpaqueIpc.Observation.batches (Except.ok.inj (readback.symm.trans finalRead))
      have exactSlots := List.cons.inj exactBatches |>.1
      rw [exactSlots] at parsed
      exact ⟨checked, groups, opened, readGroups, field, parsed, finalRead⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToCsv
