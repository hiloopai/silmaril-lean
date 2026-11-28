module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader

open Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Reader
open Arrow.RecursiveSchema.Batch.Rows (Observation)

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

public theorem group_wire {schemaLimits : Parquet.Snapshot.Limits} {snapshot : Parquet.Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Chunk.Limits} {out : Observation}
    (accepted : readGroup limits schema group = .ok out) :
    GroupWire limits schema group out := by
  unfold readGroup at accepted
  obtain ⟨binding, bound, accepted⟩ := bind_ok accepted
  obtain ⟨original, parsed, accepted⟩ := bind_ok accepted
  exact ⟨binding, original, from_mapError bound, from_mapError parsed,
    Chunk.read_wire (from_mapError parsed), Rows.reconstruct_wire (from_mapError accepted)⟩

private theorem groups_wire {schemaLimits : Parquet.Snapshot.Limits} {snapshot : Parquet.Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Chunk.Limits} {groups : List Nat}
    {out : List Observation}
    (accepted : groups.mapM (readGroup limits schema) = .ok out) :
    List.Forall₂ (GroupWire limits schema) groups out := by
  induction groups generalizing out with
  | nil => cases Except.ok.inj accepted; exact .nil
  | cons group groups ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨rows, first, accepted⟩ := bind_ok accepted
    obtain ⟨rest, later, assembled⟩ := bind_ok accepted
    cases Except.ok.inj assembled
    exact .cons (group_wire first) (ih later)

public theorem all_wire {schemaLimits : Parquet.Snapshot.Limits} {snapshot : Parquet.Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Chunk.Limits} {out : List Observation}
    (accepted : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  groups_wire accepted

public theorem reframe {limits : Chunk.Limits} {left right : Chunk.Carrier}
    {before after : Chunk.Observation}
    (first : Chunk.Wire limits left before) (second : Chunk.Wire limits right after)
    (samePlan : left.plan = right.plan) (sameTrace : before.atoms = after.atoms) :
    Rows.reconstruct limits.logical left.plan left.rows before.atoms =
      Rows.reconstruct limits.logical right.plan right.rows after.atoms := by
  have firstRows : before.atoms.countP (·.repetition == 0) = left.rows := by
    simpa [Chunk.Observation.atoms, first.rowCount] using (Chunk.ChainWire.counts first.checked).2
  have secondRows : after.atoms.countP (·.repetition == 0) = right.rows := by
    simpa [Chunk.Observation.atoms, second.rowCount] using (Chunk.ChainWire.counts second.checked).2
  rw [samePlan, ← firstRows, sameTrace, secondRows]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader
