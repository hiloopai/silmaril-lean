module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound bindWith)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess

theorem openLeaf_exact {profile : AnnotationProfile} {limits : Snapshot.Limits}
    {input : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : openLeaf profile limits input ordinal = .ok bound) :
    ∃ snapshot, Snapshot.checkPageLessTimestamp limits input = .ok snapshot ∧
      bindWith profile limits.footer snapshot ordinal = .ok bound := by
  cases snapshotRead : Snapshot.checkPageLessTimestamp limits input with
  | error cause => simp [openLeaf, snapshotRead, Except.mapError, Bind.bind, Except.bind] at opened
  | ok snapshot =>
    exact ⟨snapshot, rfl, by
      simpa [openLeaf, snapshotRead, Except.mapError, Bind.bind, Except.bind] using opened⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess
