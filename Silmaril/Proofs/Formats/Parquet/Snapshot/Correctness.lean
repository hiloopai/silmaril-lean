module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Formats
open Silmaril.Formats.Parquet.Snapshot

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

theorem check_metadata {limits : Limits} {bytes : Bytes} {checked : Checked}
    {span : Footer.Span} {metadata : Footer.Metadata}
    (opened : check (Failure := Failure) limits bytes = .ok checked)
    (footer : Footer.readFooter limits.footer bytes = .ok (span, metadata)) :
    checked.metadata = metadata := by
  cases validation : Footer.validate span.start limits.maxSchemaDepth metadata with
  | error cause => simp [check, footer, validation, Except.mapError, Bind.bind, Except.bind] at opened
  | ok result =>
    cases result
    simp [check, footer, validation, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] at opened
    cases opened
    rfl

theorem check_groups {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits input = .ok snapshot) :
    snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      ∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]? := by
  cases footer : Footer.readFooter limits.footer input with
  | error cause => simp [check, footer, Except.mapError, Bind.bind, Except.bind] at opened
  | ok spanAndMetadata =>
    obtain ⟨span, metadata⟩ := spanAndMetadata
    cases validation : Footer.validate span.start limits.maxSchemaDepth metadata with
    | error cause => simp [check, footer, validation, Except.mapError, Bind.bind, Except.bind] at opened
    | ok result =>
      cases result
      simp [check, footer, validation, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] at opened
      subst snapshot
      simp [Checked.groupCount, Checked.groupAt]

theorem readGroup_ok_iff (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (index : Nat) (rows : Reader.RowGroup schema Value) :
    snapshot.readGroup decode index = .ok rows ↔ ∃ group,
      snapshot.groupAt index = some group ∧ decode snapshot index group = .ok rows ∧
        rows.length = group.numRows.toNat := by
  cases groupAt : snapshot.groupAt index with
  | none => simp [Checked.readGroup, groupAt]
  | some group =>
    cases decoded : decode snapshot index group with
    | error reason => simp [Checked.readGroup, groupAt, decoded]
    | ok actual =>
      by_cases count : actual.length = group.numRows.toNat
      · simp [Checked.readGroup, groupAt, decoded, count]
        intro equal
        rw [← equal, count]
      · simp [Checked.readGroup, groupAt, decoded, count]
        intro equal
        rw [← equal]
        exact count

private theorem denoteGroups_append (read : Nat → Except (Error Failure) (Reader.RowGroup schema Value))
    (before after : List Nat) (groups : List (Reader.RowGroup schema Value))
    (decoded : before.mapM read = .ok groups) :
    Reader.denoteGroups read (before ++ after) =
      (groups ++ (Reader.denoteGroups read after).1, (Reader.denoteGroups read after).2) := by
  induction before generalizing groups with
  | nil =>
    change Except.ok [] = Except.ok groups at decoded
    cases decoded
    simp
  | cons index before ih =>
    cases head : read index with
    | error reason =>
      rw [List.mapM_cons, head] at decoded
      change Except.error reason = Except.ok groups at decoded
      cases decoded
    | ok rows =>
      cases tail : before.mapM read with
      | error reason =>
        rw [List.mapM_cons, head, tail] at decoded
        change Except.error reason = Except.ok groups at decoded
        cases decoded
      | ok rest =>
        rw [List.mapM_cons, head, tail] at decoded
        change Except.ok (rows :: rest) = Except.ok groups at decoded
        cases decoded
        simp [Reader.denoteGroups, head, ih rest tail]

private theorem mapM_ok_of_eof (read : Nat → Except (Error Failure) (Reader.RowGroup schema Value))
    (indices : List Nat) (eof : (Reader.denoteGroups read indices).2 = .eos) :
    indices.mapM read = .ok (Reader.denoteGroups read indices).1 := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    cases head : read index with
    | error reason => simp [Reader.denoteGroups, head] at eof
    | ok rows =>
      simp only [Reader.denoteGroups, head] at eof
      rw [List.mapM_cons, head, ih eof, Reader.denoteGroups, head]
      rfl

theorem collect_readAll_success (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (groups : List (Reader.RowGroup schema Value))
    (decoded : (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .eos⟩ := by
  have ordered := denoteGroups_append (snapshot.readGroup decode) (List.range snapshot.groupCount) [] groups decoded
  simp [Reader.denoteGroups] at ordered
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map, ordered]

theorem collect_readAll_eof (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (observation : Events.Observation Id Value (Error Failure))
    (collected : (snapshot.readAll decode).collect = .ok observation)
    (eof : observation.termination = .eos) :
    ∃ groups, (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups ∧
      observation = ⟨⟨schema, groups.flatten⟩, .eos⟩ := by
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map] at collected
  subst observation
  exact ⟨_, mapM_ok_of_eof _ _ eof, congrArg (Events.Observation.mk _) eof⟩

theorem collect_readAll_first_error (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (before after : List Nat) (index : Nat) (groups : List (Reader.RowGroup schema Value))
    (error : Error Failure) (split : List.range snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (snapshot.readGroup decode) = .ok groups)
    (failed : snapshot.readGroup decode index = .error error) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .readError error⟩ := by
  simp [Checked.readAll, Reader.collect_readAll, Reader.denote, Checked.source, Except.map, split,
    denoteGroups_append _ before (index :: after) groups earlier, Reader.denoteGroups, failed]

/-- A checked singleton footer and a successful group read yield one batch
followed by EOS, including when the decoded row list is empty. -/
theorem readAll_single {limits : Limits} {bytes : Bytes} {footer : Footer.Span}
    {metadata : Footer.Metadata} {group : Footer.RowGroup} {bind : Bind schema Value Failure}
    {decode : DecodeGroup schema Value Failure} {rows : Reader.RowGroup schema Value}
    (read : Footer.readFooter limits.footer bytes = .ok (footer, metadata))
    (valid : Footer.validate footer.start limits.maxSchemaDepth metadata = .ok ())
    (single : metadata.rowGroups = [group]) (bound : bind metadata = .ok decode)
    (decoded : ∀ snapshot, snapshot.bytes = bytes → snapshot.footer = footer →
      decode snapshot 0 group = .ok rows)
    (count : rows.length = group.numRows.toNat) :
    readAll limits bind bytes = .ok ⟨schema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ := by
  let snapshot : Checked := ⟨bytes, footer, metadata, metadata.rowGroups.toArray⟩
  have checked : check (Failure := Failure) limits bytes = .ok snapshot := by
    simp [check, read, valid, snapshot, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have opened : openSource limits bind bytes = .ok (snapshot.source decode) := by
    simp [openSource, checked, show snapshot.metadata = metadata from rfl, bound]
  have groupAt : snapshot.groupAt 0 = some group := by
    simp [Checked.groupAt, snapshot, single]
  have groups : snapshot.groupCount = 1 := by
    simp [Checked.groupCount, snapshot, single]
  have readGroup : snapshot.readGroup decode 0 = .ok rows :=
    (readGroup_ok_iff snapshot decode 0 rows).2 ⟨group, groupAt, decoded snapshot rfl rfl, count⟩
  simp [readAll, opened, Except.map, Reader.readAll_opened, Checked.source, groups, Reader.denoteGroups, readGroup]

/-- Logical scanning of the actual byte reader observes the projected ordered
prefix, with EOS after all groups or the first indexed read error. The
predicate and projection operate on decoded rows. -/
theorem collect_scan_readAll_of_checked
    (limits : Limits) (bind : Bind schema Value Failure) (bytes : Bytes)
    {snapshot : Checked} {decode : DecodeGroup schema Value Failure}
    (checked : check (Failure := Failure) limits bytes = .ok snapshot)
    (bound : bind snapshot.metadata = .ok decode)
    (projection : (s : Scan.Schema Id Kind) → Scan.Projection s)
    (keep : (s : Scan.Schema Id Kind) → Scan.Predicate s Value) :
    ((readAll limits bind bytes).scan projection keep).collect =
      let source := snapshot.source decode
      let groups := Reader.denoteGroups source.readGroup source.groups
      .ok ⟨⟨(projection schema).schema,
        (projection schema).scan (keep schema) groups.1.flatten⟩, groups.2⟩ := by
  have opened : openSource limits bind bytes = .ok (snapshot.source decode) := by
    simp [openSource, checked, bound]
  simp [readAll, opened, Except.map, Reader.collect_scan_readAll, Reader.denote]

end Silmaril.Proofs.Formats.Parquet.Snapshot
