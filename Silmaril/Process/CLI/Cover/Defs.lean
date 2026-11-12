module

public import Silmaril.Process.CLI.Loaded.Defs
public import Silmaril.X86.Link.Blob.Defs

/-!
# Placed segments covered by a `CLI.Image`

A function-level statement about a pinned executable depends only on part of its image: the
code a call can run and the read-only data it reads. Stating it for **every image that holds
those bytes at those addresses** covers every build that carries the same bytes at the same
place at once.

* `CodeIn img a code`: one non-writable executable segment of `img` holds `code` at `a`;
  `DataIn img a bytes`: one non-writable readable segment holds `bytes` at `a`. Both are
  decidable, so one `decide +kernel` per pinned image proves them.
* `Range`, `Seg`: a placed segment as data, a list of ranges, each code (`exec`) or read-only
  data, with its bytes as one little-endian number (`Silmaril.X86.Link.Blob.valueLE`).
* `covers img seg`: the `Bool` check that the image holds every range of `seg`; `Covers` is
  `covers img seg = true`. Comparing numbers keeps the kernel check one pass per range, also
  over large tables.

`Covers` gives `CodeIn` for each code range and `DataIn` for each data range
(`Covers.codeIn`, `Covers.dataIn`), and a loaded image (`Image.Loaded`) then fetches the code
and reads the data (`CodeIn.fetch`, `DataIn.read`): see `Silmaril/Process/CLI/Cover/Thms.lean`.
Placement is not abstracted: the machine fetches and addresses absolute bytes.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.X86.Link.Blob (valueLE)

/-- **The image holds `code` at `a`**, inside one non-writable executable segment. -/
abbrev CodeIn (img : Image) (a : Nat) (code : List Byte) : Prop :=
  ∃ s ∈ img.segments, s.permissions.write = false ∧ s.permissions.execute = true ∧
    s.vaddr ≤ a ∧ a + code.length ≤ s.vaddr + s.memSize ∧
    (s.contents.drop (a - s.vaddr)).take code.length = code

/-- **The image holds `bytes` at `a`**, inside one non-writable readable segment. -/
abbrev DataIn (img : Image) (a : Nat) (bytes : List Byte) : Prop :=
  ∃ s ∈ img.segments, s.permissions.write = false ∧ s.permissions.read = true ∧
    s.vaddr ≤ a ∧ a + bytes.length ≤ s.vaddr + s.memSize ∧
    (s.contents.drop (a - s.vaddr)).take bytes.length = bytes

/-- One range of a placed segment: `size` bytes at `addr`, code (`exec`) or read-only data,
holding `val` (the bytes as a little-endian number). -/
structure Range where
  addr : Nat
  size : Nat
  exec : Bool
  val : Nat
  deriving DecidableEq

/-- A placed segment: the entry address of its function and its ranges. -/
structure Seg where
  entry : Nat
  ranges : List Range
  deriving DecidableEq

/-- The image segment `s` holds the range `r`: `s` is not writable, is executable (code) or
readable (data), spans the range, and its bytes there are `r.val`. -/
def Range.inSeg (r : Range) (s : Segment) : Bool :=
  !s.permissions.write && (if r.exec then s.permissions.execute else s.permissions.read)
    && decide (s.vaddr ≤ r.addr) && decide (r.addr + r.size ≤ s.vaddr + s.memSize)
    && valueLE ((s.contents.drop (r.addr - s.vaddr)).take r.size) == r.val

/-- The image holds every range of the segment. -/
def covers (img : Image) (seg : Seg) : Bool :=
  seg.ranges.all fun r => img.segments.any r.inSeg

/-- **The image covers the segment.** -/
abbrev Covers (img : Image) (seg : Seg) : Prop := covers img seg = true

end Silmaril.Process.CLI
