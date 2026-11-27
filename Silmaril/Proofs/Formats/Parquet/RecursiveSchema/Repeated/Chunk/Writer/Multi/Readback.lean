module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Pack

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

open Silmaril.Formats
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

private theorem agrees_wire {input : Input} {start stop : Chunk.Cursor}
    {original : List (List Rows.Atom)} {pieces : List Writer.Output} {pages : List Chunk.ObservedPage}
    (checked : agrees input stop start original pieces pages = true) :
    PageAgreement start stop original pieces pages := by
  induction original generalizing start pieces pages with
  | nil =>
    cases pieces <;> cases pages <;> simp [agrees] at checked
    subst stop
    exact .nil _
  | cons atoms rest ih =>
    cases pieces with
    | nil => simp [agrees] at checked
    | cons piece pieces =>
      cases pages with
      | nil => simp [agrees] at checked
      | cons page pages =>
        simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at checked
        obtain ⟨levels, words, after⟩ := Writer.agrees_exact checked.1.2
        exact .cons checked.1.1.1 checked.1.1.2 levels words after (ih checked.2)

private theorem terminal_eq {limits : Chunk.Limits} {source : Chunk.Carrier}
    {start a b : Chunk.Cursor} {original : List (List Rows.Atom)}
    {pieces : List Writer.Output} {pages : List Chunk.ObservedPage}
    (wire : Chunk.ChainWire limits source start b pages)
    (same : PageAgreement start a original pieces pages) : a = b := by
  induction wire generalizing a original pieces with
  | nil => cases same; rfl
  | more _ _ _ _ ih =>
    cases same
    apply ih
    assumption

public theorem readback {limits : Chunk.Limits} {input : Input} {packed : Packed}
    {output : Output} (checked : certify limits input packed = .ok output) :
    Readback limits input packed output := by
  unfold certify at checked
  dsimp only at checked
  cases walked : Chunk.walk limits (carrier input (assemble packed.pieces))
      limits.framing.maxPages Writer.Multi.initial [] with
  | error cause => simp [walked, Except.mapError, bind, Except.bind] at checked
  | ok pages =>
    simp only [walked, Except.mapError, bind, Except.bind] at checked
    split at checked
    · rename_i equal
      cases Except.ok.inj checked
      have same := agrees_wire equal
      obtain ⟨stop, _, byteEnd, slotEnd, rowEnd, chain⟩ := Chunk.walk_empty_prefix_wire walked
      have stopEq := terminal_eq chain same
      subst stop
      have finalByte : packed.stop.byte = (assemble packed.pieces).length := byteEnd
      have frames := chain.originalFrames
      rw [finalByte] at frames
      exact ⟨rfl, walked, chain, frames, finalByte, rfl, slotEnd, rowEnd, same⟩
    · contradiction

public theorem original {start stop : Chunk.Cursor}
    {atoms : List (List Rows.Atom)} {pieces : List Writer.Output} {pages : List Chunk.ObservedPage}
    (agreement : PageAgreement start stop atoms pieces pages) :
    pages.map (·.decoded.levels) = atoms.map (List.map (·.levels)) ∧
      pages.map (·.decoded.words) = atoms.map (List.map (·.word)) := by
  induction agreement with
  | nil => simp
  | cons _ _ levels words _ _ ih => simp [levels, words, ih.1, ih.2]

public theorem checksums {limits : Chunk.Limits} {input : Input}
    {start stop readStop : Chunk.Cursor} {atoms : List (List Rows.Atom)}
    {pieces : List Writer.Output} {pages : List Chunk.ObservedPage}
    (built : PiecesWire limits input start stop atoms pieces)
    (matched : PageAgreement start readStop atoms pieces pages) :
    pages.map (·.frame.value.crc) =
      pieces.map (fun piece =>
        if input.checksum then some (Compression.Checksum.crc32.digest piece.page.body.toList) else none) := by
  induction built generalizing pages with
  | nil => cases matched; rfl
  | @cons start stop atoms rest piece pieces _ construction _ ih =>
    cases matched with
    | @cons _ _ _ _ _ _ page pages _ frame _ _ after next =>
      have nextState : start.advance page = advance start piece := by
        simp [Chunk.Cursor.advance, advance, frame, frameAt, after]
      rw [nextState] at next
      have tail := ih next
      simp [frame, frameAt, construction.header, Writer.header,
        Writer.checksumOf, Input.page] at tail ⊢
      exact ⟨rfl, tail⟩

public theorem emit_wire {limits : Chunk.Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    ∃ packed, serialize limits input = .ok packed ∧
      Construction limits input packed ∧ Readback limits input packed output := by
  unfold emit at written
  cases packed : serialize limits input with
  | error cause => simp [packed, bind, Except.bind] at written
  | ok built =>
    simp only [packed, bind, Except.bind] at written
    exact ⟨built, rfl, construction packed, readback written⟩

private theorem first_header {span : Parquet.Footer.Span} {start stop : Nat}
    {frame : Parquet.Page.Frame} {rest : List Parquet.Page.Frame}
    (frames : Parquet.Page.Chain span start stop (frame :: rest)) : frame.header.start = start := by
  cases frames with
  | cons within _ => exact within.headerStart

public theorem first_data_page {limits : Chunk.Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    ∃ frame, output.frames.head? = some frame ∧ frame.header.start = output.dataPageOffset := by
  obtain ⟨packed, _, built, checked⟩ := emit_wire written
  cases listed : output.frames with
  | nil =>
    have noPages : output.observation.pages = [] := List.map_eq_nil_iff.mp listed
    have restored := (original checked.agreement).1
    have empty : input.pages = [] :=
      List.map_eq_nil_iff.mp (by simpa only [noPages, List.map_nil] using restored.symm)
    have partition := built.partition
    cases rows : input.rows <;> simp [Input.validPartition, rows, empty] at partition
  | cons first rest =>
    have frames := checked.frames
    rw [listed] at frames
    exact ⟨first, rfl, first_header frames⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi
