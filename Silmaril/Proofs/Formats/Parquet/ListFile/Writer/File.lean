module

public import Silmaril.Formats.Parquet.ListFile.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Writer.Body
import Silmaril.Formats.Parquet.ListFile.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.Page.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Writer

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile
open Silmaril.Formats.Parquet.ListFile.Writer
open ListPage (Row)

public theorem checkInput_exact {limits : Writer.Limits} {input : Input}
    (h : checkInput limits input = .ok ()) :
    let compact := limits.readback.file.snapshot.footer.compact
    input.childName = "element" ∧ 4 ≤ compact.maxCollectionSize ∧
      max 7 input.name.utf8ByteSize ≤ compact.maxBinaryBytes ∧
      input.groups.length ≤ limits.maxGroups ∧ input.groups.length ≤ compact.maxCollectionSize ∧
      input.totalRows ≤ limits.maxTotalRows ∧ input.totalRows < 2^63 ∧
      input.totalSlots ≤ limits.maxTotalSlots := by
  unfold checkInput at h
  split at h
  · contradiction
  · rename_i name
    dsimp only at h
    split at h
    · contradiction
    · rename_i schema
      split at h
      · contradiction
      · rename_i groups
        split at h
        · contradiction
        · rename_i rows
          split at h
          · contradiction
          · rename_i slots
            have schemaBounds := not_or.mp (by simpa using schema :
              ¬ (limits.readback.file.snapshot.footer.compact.maxCollectionSize < 4 ∨
                 limits.readback.file.snapshot.footer.compact.maxBinaryBytes < max 7 input.name.utf8ByteSize))
            have groupBounds := not_or.mp (by simpa using groups :
              ¬ (limits.maxGroups < input.groups.length ∨
                 limits.readback.file.snapshot.footer.compact.maxCollectionSize < input.groups.length))
            have rowBounds := not_or.mp (by simpa using rows :
              ¬ (limits.maxTotalRows < input.totalRows ∨ 2^63 ≤ input.totalRows))
            exact ⟨not_not.mp name, Nat.le_of_not_gt schemaBounds.1, Nat.le_of_not_gt schemaBounds.2,
              Nat.le_of_not_gt groupBounds.1, Nat.le_of_not_gt groupBounds.2,
              Nat.le_of_not_gt rowBounds.1, Nat.lt_of_not_ge rowBounds.2, Nat.le_of_not_gt slots⟩

private theorem encodePages_wire {limits : Multi.Limits}
    {ordinal : Nat} {rows : List (List Row)} {plan : List PlannedPage} {groups : List GroupPage}
    (h : encodePages limits ordinal rows plan = .ok groups) :
    List.Forall₂ (fun input group =>
      group.page.body = PageEncoding.body input ∧
      ListPage.PageWire limits.file.page 0 group.page.header input.length group.page.body input) rows groups := by
  induction rows generalizing ordinal plan groups with
  | nil =>
    cases plan with
    | nil => obtain rfl := Except.ok.inj h; exact .nil
    | cons _ _ => contradiction
  | cons input rest ih =>
    cases plan with
    | nil => contradiction
    | cons first tail =>
      rw [encodePages] at h
      cases page : PageEncoding.encode limits input first.headerBytes with
      | error e => simp [page, Except.mapError, Bind.bind, Except.bind] at h
      | ok actual =>
        simp only [page, Except.mapError, Bind.bind, Except.bind] at h
        split at h
        · contradiction
        · cases later : encodePages limits (ordinal + 1) rest tail with
          | error e => simp [later] at h
          | ok pages =>
            rw [later] at h
            obtain rfl := Except.ok.inj h
            obtain ⟨_, _, body, _, wire⟩ := encode_wire page
            exact .cons ⟨body, wire⟩ (ih later)

private theorem place_fits {limits : Writer.Limits} {start ordinal : Nat}
    {rows : List (List Row)} {plan : List PlannedPage} (h : place limits start ordinal rows = .ok plan) :
    ∀ group ∈ rows, PageEncoding.Fits limits.readback group := by
  induction rows generalizing start ordinal plan with
  | nil => simp
  | cons head rest ih =>
    rw [place] at h
    cases measured : PageEncoding.measure limits.readback head with
    | error e => simp [measured, Except.mapError, Bind.bind, Except.bind] at h
    | ok header =>
      simp only [measured, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      · intro group member
        rcases List.mem_cons.mp member with rfl | tail
        · exact (measure_fits measured).1
        · cases placed : place limits (start + header.length + PageEncoding.bodySize head) (ordinal + 1) rest with
          | error e => simp [placed] at h
          | ok more => exact ih placed group tail

private theorem assemble_wire {limits : Writer.Limits} {input : Input} {output : Encoded}
    (h : assemble limits input = .ok output) :
    (∀ rows ∈ input.groups, PageEncoding.Fits limits.readback rows) ∧
    List.Forall₂ (fun rows group =>
      group.page.body = PageEncoding.body rows ∧
      ListPage.PageWire limits.readback.file.page 0 group.page.header rows.length group.page.body rows)
      input.groups output.groups := by
  unfold assemble at h
  cases planned : place limits 4 0 input.groups with
  | error e => simp [planned, Bind.bind, Except.bind] at h
  | ok plan =>
    simp only [planned, Bind.bind, Except.bind, Except.mapError] at h
    let start := (plan.getLast?.map (·.index.span.stop)).getD 4
    let cap := min (min limits.readback.file.snapshot.footer.maxFooterBytes (2^32 - 1))
      (limits.fileLimit - start - 8)
    split at h
    · contradiction
    · cases foot : Compact.encode cap input (plan.map (·.index)) with
      | error e => rw [foot] at h; contradiction
      | ok footer =>
        have exactFooter : Compact.encode
            (min (min limits.readback.file.snapshot.footer.maxFooterBytes (2^32 - 1))
              (limits.fileLimit - (plan.getLast?.map (·.index.span.stop)).getD 4 - 8))
            input (plan.map (·.index)) = .ok footer := foot
        simp only [exactFooter] at h
        split at h
        · contradiction
        · cases encoded : encodePages limits.readback 0 input.groups plan with
          | error e => simp [encoded] at h
          | ok groups =>
            simp only [encoded] at h
            split at h
            · contradiction
            · obtain rfl := Except.ok.inj h
              exact ⟨place_fits planned, encodePages_wire encoded⟩

public theorem emit_exact {limits : Writer.Limits} {input : Input} {output : Encoded}
    (h : emit limits input = .ok output) :
    checkInput limits input = .ok () ∧ output.Layout limits input ∧
    (∀ rows ∈ input.groups, PageEncoding.Fits limits.readback rows) ∧
    List.Forall₂ (fun rows group =>
      group.page.body = PageEncoding.body rows ∧
      ListPage.PageWire limits.readback.file.page 0 group.page.header rows.length group.page.body rows)
      input.groups output.groups ∧
    ∃ checked,
      ListFile.openFile limits.readback.file output.bytes = .ok checked ∧
      checked.shape.outer.name = input.name ∧ checked.shape.element.name = input.childName ∧
      checked.snapshot.groupCount = input.groups.length ∧
      readGroups limits.readback checked = .ok input.groups := by
  unfold emit at h
  cases accepted : checkInput limits input with
  | error e => simp [accepted, Bind.bind, Except.bind] at h
  | ok result =>
    cases result
    simp only [accepted, Bind.bind, Except.bind, Except.mapError] at h
    cases packed : assemble limits input with
    | error e => simp [packed] at h
    | ok file =>
      simp only [packed] at h
      split at h
      · contradiction
      · rename_i layout
        cases opened : ListFile.openFile limits.readback.file file.bytes with
        | error e => simp [opened] at h
        | ok checked =>
          simp only [opened] at h
          split at h
          · contradiction
          · rename_i shape
            cases parsed : readGroups limits.readback checked with
            | error e => simp [parsed] at h
            | ok rows =>
              simp only [parsed] at h
              split at h
              · rename_i agrees
                obtain rfl := Except.ok.inj h
                subst rows
                obtain ⟨fit, pages⟩ := assemble_wire packed
                exact ⟨rfl, not_not.mp layout, fit, pages, checked, opened,
                  (not_not.mp shape).1, (not_not.mp shape).2.1, (not_not.mp shape).2.2, parsed⟩
              · contradiction

private theorem indexed_wire {limits : Multi.Limits} {checked : ListFile.Checked} {indices : List Nat}
    {groups : List (List Row)}
    (h : (indices.mapM fun ordinal =>
      (Multi.readGroup limits.maxGroupSlots checked ordinal).mapError (Writer.Error.groupReadback ordinal)) =
        .ok groups) :
    List.Forall₂ (Multi.GroupWire limits.maxGroupSlots checked) indices groups := by
  induction indices generalizing groups with
  | nil => obtain rfl := Except.ok.inj h; exact .nil
  | cons ordinal rest ih =>
    rw [List.mapM_cons] at h
    cases decoded : Multi.readGroup limits.maxGroupSlots checked ordinal with
    | error e => simp [decoded, Except.mapError, Bind.bind, Except.bind] at h
    | ok rows =>
      simp only [decoded, Except.mapError, Bind.bind, Except.bind] at h
      cases later : (rest.mapM fun index =>
          (Multi.readGroup limits.maxGroupSlots checked index).mapError (Writer.Error.groupReadback index)) with
      | error e =>
        simp only [Except.mapError] at later
        simp [later] at h
      | ok following =>
        have continued := later
        simp only [Except.mapError] at later
        rw [later] at h
        obtain rfl := Except.ok.inj h
        exact .cons (Multi.readGroup_wire decoded) (ih continued)

public theorem emit_readback {limits : Writer.Limits} {input : Input} {output : Encoded}
    (h : emit limits input = .ok output) :
    ∃ checked,
      ListFile.openFile limits.readback.file output.bytes = .ok checked ∧
      ListFile.OpenWire limits.readback.file output.bytes checked ∧
      checked.shape.outer.name = input.name ∧ checked.shape.element.name = input.childName ∧
      checked.snapshot.groupCount = input.groups.length ∧
      readGroups limits.readback checked = .ok input.groups ∧
      List.Forall₂ (Multi.GroupWire limits.readback.maxGroupSlots checked)
        (List.range checked.snapshot.groupCount) input.groups := by
  obtain ⟨_, _, _, _, checked, opened, name, child, groups, values⟩ := emit_exact h
  exact ⟨checked, opened, ListFile.openFile_wire opened, name, child, groups, values, indexed_wire values⟩

public theorem emitted_frame {limits : Writer.Limits} {input : Input} {output : Encoded} {group : GroupPage}
    (h : emit limits input = .ok output) (member : group ∈ output.groups) :
    Page.Chain group.index.span group.index.span.start group.index.span.stop [group.frame] := by
  have layout := (emit_exact h).2.1
  exact (Page.readChunk_chain (layout.2.2.2.2.2 group member).2.1).2.2

end Silmaril.Proofs.Formats.Parquet.ListFile.Writer
