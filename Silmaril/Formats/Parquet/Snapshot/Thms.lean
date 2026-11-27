module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.Correctness
import Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessInt32
import Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessTimestamp

public section

namespace Silmaril.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- The opt-in snapshot preserves the exact input footer and all its ordinals. -/
theorem checkPageLessInt32_exact {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : checkPageLessInt32 limits input = .ok snapshot) :
    Footer.readFooter limits.footer input = .ok (snapshot.footer, snapshot.metadata) ∧
      Footer.PageLessInt32.validate limits.footer limits.maxSchemaDepth input
        snapshot.footer snapshot.metadata = .ok () ∧ snapshot.bytes = input ∧
      snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      ∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]? :=
  Proofs.Formats.Parquet.Snapshot.PageLessInt32.check_exact opened

/-- The strict snapshot never enables the no-frame TIMESTAMP policy. -/
theorem check_noPageLessTimestamp {Failure : Type*} {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits input = .ok snapshot) (group : Footer.RowGroup) :
    snapshot.admitsPageLessTimestamp group = false :=
  Proofs.Formats.Parquet.Snapshot.PageLessTimestamp.check_strict opened group

/-- The opt-in snapshot retains the original footer, bytes, and no-frame group ordinals. -/
theorem checkPageLessTimestamp_exact {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : checkPageLessTimestamp limits input = .ok snapshot) :
    Footer.readFooter limits.footer input = .ok (snapshot.footer, snapshot.metadata) ∧
      Footer.PageLessTimestamp.validate limits.footer limits.maxSchemaDepth input
        snapshot.footer snapshot.metadata = .ok () ∧ snapshot.bytes = input ∧
      snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      (∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]?) ∧
      ∀ group, snapshot.admitsPageLessTimestamp group = Footer.PageLessTimestamp.isPageLess group :=
  Proofs.Formats.Parquet.Snapshot.PageLessTimestamp.check_exact opened

/-- The checked snapshot retains the metadata parsed from the original footer. -/
theorem check_metadata {limits : Limits} {bytes : Bytes} {checked : Checked}
    {span : Footer.Span} {metadata : Footer.Metadata}
    (opened : check (Failure := Failure) limits bytes = .ok checked)
    (footer : Footer.readFooter limits.footer bytes = .ok (span, metadata)) :
    checked.metadata = metadata :=
  Proofs.Formats.Parquet.Snapshot.check_metadata opened footer

/-- The strict snapshot retains the exact immutable input bytes. -/
theorem check_bytes {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits input = .ok snapshot) : snapshot.bytes = input :=
  Proofs.Formats.Parquet.Snapshot.check_bytes opened

/-- The strict snapshot retains all original footer groups at their original indices. -/
theorem check_groups {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits input = .ok snapshot) :
    snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      ∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]? :=
  Proofs.Formats.Parquet.Snapshot.check_groups opened

/-- A successful indexed read returns exactly the decoder's rows at the
footer's declared count. -/
theorem Checked.readGroup_ok_iff (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (index : Nat) (rows : Reader.RowGroup schema Value) :
    snapshot.readGroup decode index = .ok rows ↔ ∃ group,
      snapshot.groupAt index = some group ∧ decode snapshot index group = .ok rows ∧
        rows.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.Snapshot.readGroup_ok_iff snapshot decode index rows

/-- Successful full consumption observes the concatenation in footer order. -/
theorem Checked.collect_readAll_success (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (groups : List (Reader.RowGroup schema Value))
    (decoded : (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .eos⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_success snapshot decode groups decoded

/-- An EOF observation certifies successful reads of all footer indices and
contains exactly the concatenated rows of those reads. -/
theorem Checked.collect_readAll_eof (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (observation : Events.Observation Id Value (Error Failure))
    (collected : (snapshot.readAll decode).collect = .ok observation)
    (eof : observation.termination = .eos) :
    ∃ groups, (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups ∧
      observation = ⟨⟨schema, groups.flatten⟩, .eos⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_eof snapshot decode observation collected eof

/-- The first failed read retains exactly the earlier rows and determines the
terminal payload independently of all later groups. -/
theorem Checked.collect_readAll_first_error (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (before after : List Nat) (index : Nat) (groups : List (Reader.RowGroup schema Value))
    (error : Error Failure) (split : List.range snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (snapshot.readGroup decode) = .ok groups)
    (failed : snapshot.readGroup decode index = .error error) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .readError error⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_first_error snapshot decode before after index groups
    error split earlier failed

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
    readAll limits bind bytes = .ok ⟨schema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ :=
  Proofs.Formats.Parquet.Snapshot.readAll_single read valid single bound decoded count

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
        (projection schema).scan (keep schema) groups.1.flatten⟩, groups.2⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_scan_readAll_of_checked limits bind bytes checked bound projection keep

end Silmaril.Formats.Parquet.Snapshot
