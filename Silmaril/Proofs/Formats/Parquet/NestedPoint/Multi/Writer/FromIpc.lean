module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Defs
import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Thms
import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Thms
import Silmaril.Formats.Arrow.StructInt32.Stream.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc
open Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc (NativeRow nativeRow)
open Arrow.StructInt32.Stream (Observed Batch)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem map_agrees {α β γ : Type} {xs : List α} {ys : List β} {f : α → γ} {g : β → γ}
    (agreement : List.Forall₂ (fun x y => f x = g y) xs ys) :
    xs.map f = ys.map g := by
  induction agreement with
  | nil => rfl
  | cons head _ tail => simp [head, tail]

private theorem bindRow_exact {group index : Nat} {raw : NativeRow} {row : NestedPoint.Row}
    (accepted : bindRow group index raw = .ok row) : raw = nativeRow row := by
  cases raw with
  | none => cases Except.ok.inj accepted; rfl
  | some seen =>
    obtain ⟨left, right⟩ := seen
    cases left with
    | none => contradiction
    | some value => cases Except.ok.inj accepted; rfl

private theorem bindGroup_exact {group : Nat} {rows : List NativeRow} {groupRows : List NestedPoint.Row}
    (accepted : bindGroup group rows = .ok groupRows) : rows = groupRows.map nativeRow := by
  have agreement := (List.mapM_eq_ok_iff_forall₂.mp accepted).imp (fun x y checked =>
    show x.1 = nativeRow y from bindRow_exact checked)
  simpa using map_agrees agreement

theorem bind_exact {observed : Observed Int64} {input : NestedPoint.Multi.Writer.Input}
    (accepted : bindInput observed = .ok input) :
    input.field = observed.field ∧ input.groups.map (List.map nativeRow) = observed.batches.map Batch.rows := by
  unfold bindInput at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i left
    split at accepted
    · contradiction
    · rename_i right
      obtain ⟨groups, bound, accepted⟩ := bind_ok accepted
      cases Except.ok.inj accepted
      have agreement := (List.mapM_eq_ok_iff_forall₂.mp bound).imp
        (fun x y checked => show x.1.rows = y.map nativeRow from bindGroup_exact checked)
      have rows : groups.map (List.map nativeRow) = (observed.batches.zipIdx.map Prod.fst).map Batch.rows := by
        simpa only [List.map_map, Function.comp_def] using (map_agrees agreement).symm
      refine ⟨?_, by simpa only [List.zipIdx_map_fst] using rows⟩
      obtain ⟨⟨name, ⟨leftName, leftNullable⟩, ⟨rightName, rightNullable⟩⟩, batches⟩ := observed
      cases leftNullable <;> cases rightNullable <;> simp_all [NestedPoint.Multi.Writer.Input.field]

theorem convert_readback {limits : Limits} {wire : KBytes} {output : NestedPoint.Multi.Writer.Encoded}
    (written : convert limits wire = .ok output) : Readback limits wire output := by
  unfold convert at written
  obtain ⟨observed, decoded, written⟩ := bind_ok written
  obtain ⟨input, bound, written⟩ := bind_ok written
  have read := mapError_ok decoded
  obtain ⟨wf, size, envelope, schema, groups⟩ := Arrow.StructInt32.Stream.readFor_wire (width := .int64) read
  obtain ⟨field, rows⟩ := bind_exact bound
  exact ⟨observed, input, size, read, wf, envelope, schema, groups, field, rows,
    NestedPoint.Multi.Writer.emit_readback (mapError_ok written)⟩

theorem roundtrip_ipc {limits : Limits} {target : Arrow.ObservationLimits} {wire returned : KBytes}
    {output : NestedPoint.Multi.Writer.Encoded} (written : convert limits wire = .ok output)
    (reemitted : (NestedPoint.Multi.ToIpc.convert ⟨limits.parquet.readback, target⟩ output.bytes).wire = .ok returned) :
    ∃ observed restored,
      Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire = .ok observed ∧
      Arrow.StructInt32.Stream.readFor .int64 target returned = .ok restored ∧
      Arrow.StructInt32.Stream.Writer.AgreesFor observed.field (observed.batches.map Batch.rows) restored := by
  obtain ⟨observed, input, _, read, _, _, _, _, fields, rows, outputWire⟩ := (convert_readback written).data
  obtain ⟨checked, opened, _, field, _, groups, _⟩ := outputWire.groups
  obtain ⟨restoredFile, restoredGroups, restored, _, reopened, _, restoredRead, _, _, ipcRead, agrees, _, _, _, _⟩ :=
    (NestedPoint.Multi.ToIpc.convert_readback reemitted).data
  have same := Except.ok.inj (reopened.symm.trans opened)
  subst restoredFile
  have exactGroups := Except.ok.inj (restoredRead.symm.trans groups)
  exact ⟨observed, restored, read, ipcRead, by simpa only [field, fields, exactGroups, rows] using agrees⟩

end Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc
