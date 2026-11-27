module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessTimestamp

open Silmaril.Formats Parquet Snapshot

theorem check_exact {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : checkPageLessTimestamp limits input = .ok snapshot) :
    Footer.readFooter limits.footer input = .ok (snapshot.footer, snapshot.metadata) ∧
      Footer.PageLessTimestamp.validate limits.footer limits.maxSchemaDepth input
        snapshot.footer snapshot.metadata = .ok () ∧ snapshot.bytes = input ∧
      snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      (∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]?) ∧
      ∀ group, snapshot.admitsPageLessTimestamp group = Footer.PageLessTimestamp.isPageLess group := by
  cases footerRead : Footer.readFooter limits.footer input with
  | error cause => simp [checkPageLessTimestamp, footerRead, Except.mapError, Bind.bind, Except.bind] at opened
  | ok admitted =>
    obtain ⟨span, metadata⟩ := admitted
    cases valid : Footer.PageLessTimestamp.validate limits.footer limits.maxSchemaDepth input span metadata with
    | error cause =>
      simp [checkPageLessTimestamp, footerRead, valid, Except.mapError, Bind.bind, Except.bind] at opened
    | ok success =>
      cases success
      simp only [checkPageLessTimestamp, footerRead, valid, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.ok.injEq] at opened
      subst snapshot
      exact ⟨rfl, valid, rfl, by simp [Checked.groupCount], fun index => by simp [Checked.groupAt], fun _ => rfl⟩

theorem check_strict {Failure : Type*} {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits input = .ok snapshot) (group : Footer.RowGroup) :
    snapshot.admitsPageLessTimestamp group = false := by
  cases footerRead : Footer.readFooter limits.footer input with
  | error cause => simp [check, footerRead, Except.mapError, Bind.bind, Except.bind] at opened
  | ok parsed =>
    obtain ⟨span, metadata⟩ := parsed
    cases valid : Footer.validate span.start limits.maxSchemaDepth metadata with
    | error cause => simp [check, footerRead, valid, Except.mapError, Bind.bind, Except.bind] at opened
    | ok success =>
      cases success
      simp only [check, footerRead, valid, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.ok.injEq] at opened
      subst snapshot
      rfl

end Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessTimestamp
