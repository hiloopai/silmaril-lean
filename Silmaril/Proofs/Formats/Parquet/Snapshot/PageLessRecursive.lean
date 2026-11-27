module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs

namespace Silmaril.Proofs.Formats.Parquet.Snapshot

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Snapshot

public theorem admitsPageLessRecursive_isPageLess {snapshot : Checked} {group : Footer.RowGroup}
    (admitted : snapshot.admitsPageLessRecursive group = true) :
    Footer.PageLessRecursive.isPageLess group = true := by
  simp only [Checked.admitsPageLessRecursive, Bool.and_eq_true] at admitted
  exact admitted.2

public theorem checkRecursive_exact {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : checkRecursive limits input = .ok snapshot) :
    Footer.readFooter limits.footer input = .ok (snapshot.footer, snapshot.metadata) ∧
      snapshot.bytes = input ∧ snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      (∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]?) ∧
      ∀ group, snapshot.admitsPageLessRecursive group = true →
        Footer.PageLessRecursive.isPageLess group = true ∧
        Footer.PageLessRecursive.validate limits.footer limits.maxSchemaDepth input
          snapshot.footer snapshot.metadata = .ok () := by
  unfold checkRecursive at opened
  cases parsed : Footer.readFooter limits.footer input with
  | error reason => simp [parsed, Except.mapError, Except.bind, Bind.bind] at opened
  | ok result =>
    obtain ⟨span, metadata⟩ := result
    cases strict : Footer.validate span.start limits.maxSchemaDepth metadata with
    | ok value =>
      cases value
      simp [parsed, strict, Except.mapError, Except.bind, Bind.bind, Pure.pure, Except.pure] at opened
      subst snapshot
      simp [Checked.groupCount, Checked.groupAt, Checked.admitsPageLessRecursive]
    | error reason =>
      simp only [parsed, Except.mapError, Except.bind, Bind.bind, strict] at opened
      split at opened
      · contradiction
      · cases checked : Footer.PageLessRecursive.validate limits.footer limits.maxSchemaDepth input span metadata with
        | error reason => simp [checked] at opened
        | ok value =>
          cases value
          simp [checked, Pure.pure, Except.pure] at opened
          subst snapshot
          simp [checked, Checked.groupCount, Checked.groupAt, Checked.admitsPageLessRecursive]

end Silmaril.Proofs.Formats.Parquet.Snapshot
