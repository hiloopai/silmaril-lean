module

public import Silmaril.Formats.Sqlite.File.Freeblocks.Defs
import Silmaril.Proofs.Formats.Sqlite.File.Freeblocks.Layout

@[expose] public section

namespace Silmaril.Formats.Sqlite.File.Freeblocks

open Silmaril.Formats.Sqlite

/-- A successful scan exactly follows the recorded headers and yields bounded disjoint blocks in order. -/
theorem read_bounded_ordered (view : File.View) (content fuel offset : Nat) (blocks : List Span)
    (decoded : read? view content fuel offset = some blocks) :
    Chain view offset blocks ∧ blocks.Pairwise (fun a b => a.stop ≤ b.start) ∧
      ∀ block ∈ blocks, content ≤ block.start ∧ block.start + 4 ≤ block.stop ∧
        block.stop ≤ view.length ∧ offset ≤ block.start :=
  Silmaril.Proofs.Formats.Sqlite.File.Freeblocks.read_bounded_ordered view content fuel offset blocks decoded

/-- A checked layout has nonempty ordered spans within the content bounds. -/
theorem cover_order (lo hi : Nat) (blocks : List Span) (checked : covers lo hi blocks = true) :
    blocks.Pairwise (fun a b => a.stop ≤ b.start) ∧
      ∀ span ∈ blocks, lo ≤ span.start ∧ span.start < span.stop ∧ span.stop ≤ hi :=
  Silmaril.Proofs.Formats.Sqlite.File.Freeblocks.cover_order lo hi blocks checked

/-- Each byte in an accepted content area lies in exactly one span. -/
theorem cover_partition (lo hi : Nat) (spans : List Span) (checked : covers lo hi spans = true)
    (index : Nat) (lower : lo ≤ index) (upper : index < hi) :
    ∃ span ∈ spans, (span.start ≤ index ∧ index < span.stop) ∧
      ∀ other ∈ spans, (other.start ≤ index ∧ index < other.stop) → other = span :=
  Silmaril.Proofs.Formats.Sqlite.File.Freeblocks.cover_partition lo hi spans checked index lower upper

end Silmaril.Formats.Sqlite.File.Freeblocks
