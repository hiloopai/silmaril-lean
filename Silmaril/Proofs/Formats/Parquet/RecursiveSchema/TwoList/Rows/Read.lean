module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Projection

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)

private theorem zip_axes {levels : List Chunk.Slot} {words : List (Option Chunk.Word)} {after : Chunk.State}
    (same : levels.length = words.length) :
    let input := pageAtoms ⟨levels, words, after⟩
    input.map Atom.repetition = levels.map Chunk.Slot.repetition ∧
    input.map Atom.definition = levels.map Chunk.Slot.definition ∧
    input.map Atom.word = words := by
  induction levels generalizing words with
  | nil =>
    cases words <;> simp [pageAtoms] at same ⊢
  | cons first tail ih =>
    cases words with
    | nil => simp at same
    | cons word rest =>
      simp only [List.length_cons, Nat.succ.injEq] at same
      obtain ⟨rep, defn, values⟩ := ih same
      simp [pageAtoms] at rep defn values ⊢
      exact ⟨rep, defn, values⟩

public theorem decoded_axes {limits : Chunk.Limits} {encoding : Chunk.ValueEncoding} {plan : Plan} {ceiling : Nat} {start : Chunk.State} {reps defs : List Nat}
    {suffix : Silmaril.Formats.Bytes} {decoded : Chunk.Decoded}
    (wire : Chunk.DecodedWire limits plan ceiling start reps defs suffix decoded encoding) :
    (pageAtoms decoded).map Atom.repetition = reps ∧
    (pageAtoms decoded).map Atom.definition = defs ∧
    (pageAtoms decoded).map Atom.word = decoded.words := by
  obtain ⟨rep, defn⟩ := wire.levels.originalLevels
  have lengths : decoded.levels.length = decoded.words.length := by
    simpa only [List.length_map] using (congrArg List.length wire.aligned).symm
  obtain ⟨r, d, w⟩ := zip_axes lengths (after := decoded.after)
  exact ⟨r.trans rep, d.trans defn, w⟩

private theorem decoded_row_starts {limits : Chunk.Limits} {encoding : Chunk.ValueEncoding} {plan : Plan} {source : Silmaril.Formats.Bytes}
    {start : Chunk.State} {ceiling : Nat} {reps defs : List Nat} {decoded : Chunk.Decoded}
    (original : Chunk.DecodedWire limits plan ceiling start reps defs source decoded encoding) :
    (pageAtoms decoded).countP (fun slot => slot.repetition == 0) =
      decoded.levels.countP Chunk.Slot.startsRow := by
  have reps := (decoded_axes original).1
  have counts := congrArg (List.countP (· == 0)) reps
  simpa only [List.countP_map, Function.comp_def] using counts.trans (original.levels.repetitionCount)

private theorem page_row_starts {limits : Chunk.Limits} {plan : Plan} {source : Silmaril.Formats.Bytes}
    {frame : Page.Frame} {start : Chunk.State} {remaining ceiling : Nat} {decoded : Chunk.Decoded} {codec : Chunk.Codec}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : Chunk.DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary) :
    (pageAtoms decoded).countP (fun slot => slot.repetition == 0) =
      decoded.levels.countP Chunk.Slot.startsRow := by
  cases wire with
  | v1 _ v1 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, original, _⟩ := v1.original
    exact decoded_row_starts original
  | v2 _ v2 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, original, rfl⟩ := v2.original
    simpa only [Chunk.closeV2, pageAtoms] using decoded_row_starts original

public theorem chain_trace_rows {limits : Chunk.Limits} {carrier : Chunk.Carrier} {start stop : Chunk.State}
    {frames : List Page.Frame} {pages : List Chunk.ObservedPage}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : Chunk.ChainWire limits carrier dictionary start frames pages stop) :
    start.rows + (atoms pages).countP (fun slot => slot.repetition == 0) = stop.rows := by
  have rows := wire.counts.2
  suffices exactCount : (atoms pages).countP (fun slot => slot.repetition == 0) =
      (pages.flatMap (·.decoded.levels)).countP Chunk.Slot.startsRow by
    simpa only [exactCount] using rows
  clear rows
  induction wire with
  | nil => rfl
  | cons first _ ih =>
    simp only [atoms] at ih
    simp only [atoms, List.flatMap_cons, List.countP_append, page_row_starts first, ih]

public theorem reframe {plan : Plan} {before after : Chunk.Observation}
    {leftLimits rightLimits : Chunk.Limits} {left right : Chunk.Carrier}
    (first : Chunk.Wire leftLimits left before) (second : Chunk.Wire rightLimits right after)
    (same : atoms before.pages = atoms after.pages) :
    reconstructObservation plan before = reconstructObservation plan after := by
  have beforeRows := chain_trace_rows first.decoded
  have afterRows := chain_trace_rows second.decoded
  simp only [Nat.zero_add, same] at beforeRows afterRows
  have count := beforeRows.symm.trans afterRows
  simp only [reconstructObservation, count, same]

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, accepted⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at accepted
  | ok => simpa only [Except.mapError, Except.ok.injEq] using accepted

public theorem reconstruct_wire {plan : Plan} {expected : Nat} {input : List Atom} {out : Observation}
    (accepted : reconstruct plan expected input = .ok out) :
    ObservationWire plan input expected out := by
  unfold reconstruct at accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  split at accepted
  · rename_i count
    split at accepted
    · rename_i relation
      cases Except.ok.inj accepted
      obtain ⟨typed, words⟩ := relation_sound relation
      exact ⟨relation, count, rfl, typed, words⟩
    · contradiction
  · contradiction

public theorem group_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {out : Observation}
    (accepted : readGroup limits schema group = .ok out) : GroupWire limits schema group out := by
  unfold readGroup at accepted
  obtain ⟨binding, bound, accepted⟩ := bind_ok accepted
  obtain ⟨column, read, ready⟩ := bind_ok accepted
  have source := from_mapError read
  have wire := Chunk.read_wire source
  have count : column.stop.rows = binding.rowGroup.numRows.toNat := wire.rows
  refine ⟨binding, column, from_mapError bound, source, wire, ?_⟩
  rw [← count]
  exact reconstruct_wire ready

private theorem all_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {indices : List Nat} {out : List Observation}
    (accepted : indices.mapM (readGroup limits schema) = .ok out) :
    List.Forall₂ (GroupWire limits schema) indices out := by
  induction indices generalizing out with
  | nil =>
    cases Except.ok.inj accepted
    exact .nil
  | cons index tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, decoded, accepted⟩ := bind_ok accepted
    obtain ⟨rest, continued, result⟩ := bind_ok accepted
    cases Except.ok.inj result
    exact .cons (group_wire decoded) (ih continued)

public theorem read_all_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {out : List Observation}
    (accepted : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  all_wire accepted

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows
