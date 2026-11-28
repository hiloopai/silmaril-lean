module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Levels
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Sections

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {out : α}
    (read : first.mapError wrap = .ok out) : first = .ok out := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

private theorem checked_extent {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status}
    (checked : Page.Checksum.verify cap source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent => exact (Page.Checksum.verify_absent_iff.mp checked).2.1
  | valid => exact (Page.Checksum.verify_valid_iff.mp checked).2.1

public theorem decodePage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodePage limits plan wrappers source frame start remaining ceiling = .ok decoded) :
    PageWire limits plan wrappers source frame start remaining ceiling decoded := by
  unfold decodePage at accepted
  obtain ⟨info, header, accepted⟩ := bind_ok accepted
  obtain ⟨status, checked, accepted⟩ := bind_ok accepted
  obtain ⟨reps, repRead, accepted⟩ := bind_ok accepted
  obtain ⟨defs, defRead, accepted⟩ := bind_ok accepted
  obtain ⟨stop, scanned, accepted⟩ := bind_ok accepted
  obtain ⟨words, wordsRead, accepted⟩ := bind_ok accepted
  obtain ⟨aligned, alignedRead, done⟩ := bind_ok accepted
  cases Except.ok.inj done
  have crc := from_mapError checked
  obtain ⟨repWire, repCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError repRead)
  obtain ⟨defWire, defCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError defRead)
  have parts := sections_wire (checked_extent crc) repWire defWire
  have states := scan_wire (from_mapError scanned)
  have alignedWire := FlatPage.reconstruct_ok_iff.mp (from_mapError alignedRead)
  obtain ⟨_, physical, suffix, count, widths, values⟩ :=
    Plain.decodeFixedWidth_ok_iff.mp (from_mapError wordsRead)
  exact ⟨info, status, reps, defs, aligned, physical,
    RecursiveSchema.Chunk.admitPage_wire (from_mapError header), crc, parts, states,
    repCount, defCount, suffix, count, widths, alignedWire.1, alignedWire.2.trans values, rfl⟩

public theorem page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (wire : PageWire limits plan wrappers source frame start remaining ceiling decoded) :
    ∃ info, frame.value.kind = .dataV1 info ∧ decoded.atoms.length = info.numValues ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨info, _, reps, defs, aligned, _, header, _, _, scanned, repCount, defCount,
    _, _, _, maskWire, _, atomsWire⟩ := wire.original
  have len : aligned.length = (reps.levels.zip defs.levels).length := by
    have maskCount := congrArg List.length maskWire
    simpa [mask, repCount, defCount] using maskCount
  have axes := (atoms_axes len).1
  have lengths := congrArg List.length axes
  have count : (atoms (reps.levels.zip defs.levels) aligned).length = info.numValues := by
    simpa [repCount, defCount] using lengths
  have rows : (atoms (reps.levels.zip defs.levels) aligned).countP (·.repetition == 0) =
      (reps.levels.zip defs.levels).countP (fun level => level.1 == 0) := by
    have counted := congrArg (List.countP fun level : Nat × Nat => level.1 == 0) axes
    simpa [Function.comp_def] using counted
  have ⟨slots, afterRows⟩ := scan_counts scanned
  rw [atomsWire, rows]
  exact ⟨info, header.kind, count, by simpa [count, repCount, defCount] using slots, afterRows⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
