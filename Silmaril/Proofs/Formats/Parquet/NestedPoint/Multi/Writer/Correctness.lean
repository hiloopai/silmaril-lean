module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Defs
import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open NestedPoint.Multi.Writer
open Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc (groupSource rowsFor)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem levelPair_contract (row : NestedPoint.Row) :
    let (left, right) := PageEncoding.levelPair row
    left ≤ NestedPoint.Multi.Kind.signed.child.maxDefinition ∧
    right ≤ NestedPoint.Multi.Kind.wide.child.maxDefinition ∧
    NestedPresence.classify NestedPoint.Multi.Kind.signed.child left =
      (if row.isSome then .value else .parentAbsent) ∧
    NestedPresence.classify NestedPoint.Multi.Kind.wide.child right =
      (match row with | none => .parentAbsent | some (_, none) => .childNull | some (_, some _) => .value) := by
  cases row with
  | none => decide
  | some row =>
    obtain ⟨signed, wide⟩ := row
    cases wide <;> simp [PageEncoding.levelPair, NestedPoint.Multi.Kind.child,
      NestedPresence.Child.maxDefinition, NestedPresence.classify]

private theorem place_rows {limits : Limits} {offset ordinal stop : Nat}
    {rows : List (List NestedPoint.Row)} {groups : List GroupPlan}
    (placed : place limits offset ordinal rows = .ok (stop, groups)) :
    groups.map GroupPlan.rows = rows := by
  induction rows generalizing offset ordinal stop groups with
  | nil =>
    simp [place] at placed
    simp [← placed.2]
  | cons rows tail ih =>
    rw [place] at placed
    obtain ⟨_, _, placed⟩ := bind_ok placed
    obtain ⟨_, _, placed⟩ := bind_ok placed
    dsimp only at placed
    split at placed
    · contradiction
    · obtain ⟨⟨_, rest⟩, later, placed⟩ := bind_ok placed
      cases Except.ok.inj placed
      simp [ih later]

private theorem serialize_rows {limits : Limits} {input : Input} {output : Encoded}
    (serialized : serialize limits input = .ok output) :
    output.groups.map GroupPlan.rows = input.groups := by
  unfold serialize at serialized
  obtain ⟨_, _, serialized⟩ := bind_ok serialized
  obtain ⟨⟨_, groups⟩, placed, serialized⟩ := bind_ok serialized
  dsimp only at serialized
  split at serialized
  · contradiction
  · obtain ⟨_, _, serialized⟩ := bind_ok serialized
    obtain ⟨_, _, serialized⟩ := bind_ok serialized
    split at serialized
    · contradiction
    · cases Except.ok.inj serialized
      exact place_rows placed

private theorem certify_exact {limits : Limits} {input : Input} {output : Encoded}
    (accepted : certify limits input output = .ok ()) :
    Footer.readFooter limits.readback.snapshot.footer output.bytes =
        .ok (output.footer, metadata input output.groups) ∧
      ∃ checked, NestedPoint.Multi.ToIpc.openFile limits.readback output.bytes = .ok checked ∧
        checked.field = input.field ∧ checked.snapshot.groupCount = input.groups.length ∧
        (List.range checked.snapshot.groupCount).mapM (NestedPoint.Multi.read limits.readback.group checked.snapshot) =
          .ok input.groups := by
  unfold certify at accepted
  split at accepted
  · contradiction
  · rename_i footer
    obtain ⟨checked, opened, accepted⟩ := bind_ok accepted
    split at accepted
    · contradiction
    · rename_i same
      obtain ⟨decoded, decodedOk, accepted⟩ := bind_ok accepted
      split at accepted
      · contradiction
      · rename_i groups
        have shapes := Decidable.of_not_not same
        have exactGroups : decoded = input.groups := Decidable.of_not_not groups
        subst decoded
        have agreement := (List.mapM_eq_ok_iff_forall₂.mp decodedOk).imp (fun _ _ read => mapError_ok read)
        exact ⟨Decidable.of_not_not footer, checked, mapError_ok opened, shapes.1, shapes.2,
          List.mapM_eq_ok_iff_forall₂.mpr agreement⟩

private theorem denote_groups {limits : NestedPoint.Multi.Limits} {checked : NestedPoint.Multi.ToIpc.Checked}
    {indices : List Nat} {groups : List (List NestedPoint.Row)}
    (decoded : indices.mapM (NestedPoint.Multi.read limits checked.snapshot) = .ok groups) :
    Reader.denoteGroups (groupSource limits checked).readGroup indices =
      (groups.map (rowsFor checked.field), .eos) := by
  induction indices generalizing groups with
  | nil =>
    have empty : [] = groups := Except.ok.inj decoded
    subst groups
    rfl
  | cons index tail ih =>
    rw [List.mapM_cons] at decoded
    obtain ⟨rows, first, decoded⟩ := bind_ok decoded
    obtain ⟨rest, later, decoded⟩ := bind_ok decoded
    cases Except.ok.inj decoded
    have following := ih later
    simpa only [Reader.denoteGroups, groupSource, first, Except.map, Except.mapError, List.map_cons] using
      congrArg (fun pair => (rowsFor checked.field rows :: pair.1, pair.2)) following

private theorem events_agree {limits : Limits} {input : Input} {output : Encoded}
    {checked : NestedPoint.Multi.ToIpc.Checked}
    (opened : NestedPoint.Multi.ToIpc.openFile limits.readback output.bytes = .ok checked)
    (field : checked.field = input.field)
    (decoded : (List.range checked.snapshot.groupCount).mapM
      (NestedPoint.Multi.read limits.readback.group checked.snapshot) = .ok input.groups) :
    NestedPoint.Multi.ToIpc.readAll limits.readback output.bytes = .ok ⟨NestedPoint.Multi.ToIpc.schema input.field,
      ⟨input.groups.map (AlignedColumns.ofRows ∘ rowsFor input.field), .eos⟩⟩ := by
  have following := denote_groups decoded
  rw [NestedPoint.Multi.ToIpc.readAll_reader opened, Reader.readAll_opened]
  change (Except.ok ⟨NestedPoint.Multi.ToIpc.schema checked.field,
    ⟨(Reader.denoteGroups (groupSource limits.readback.group checked).readGroup
      (List.range checked.snapshot.groupCount)).1.map AlignedColumns.ofRows,
      (Reader.denoteGroups (groupSource limits.readback.group checked).readGroup
        (List.range checked.snapshot.groupCount)).2⟩⟩ : NestedPoint.Multi.ToIpc.SourceTrace) = _
  rw [following, List.map_map, field]

theorem emit_readback {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) : Readback limits input output := by
  unfold emit at written
  obtain ⟨_, serialized, written⟩ := bind_ok written
  obtain ⟨_, accepted, written⟩ := bind_ok written
  cases Except.ok.inj written
  obtain ⟨footer, checked, opened, field, count, decoded⟩ := certify_exact accepted
  have original := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp
    (fun _ _ => NestedPoint.Multi.ToIpc.readGroup_wire)
  exact ⟨serialize_rows serialized, footer,
    ⟨checked, opened, NestedPoint.Multi.ToIpc.openFile_wire opened, field, count, decoded, original⟩,
    events_agree opened field decoded⟩

end Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer
