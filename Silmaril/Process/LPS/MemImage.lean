module

public import Silmaril.Process.LPS.Basic

/-!
# LPS in Lean: memory images

Translation of LPS `MemImageType.v` (upstream commit `f1006fe8`). An `Image` is what
`elf-snapshot` extracts from a static ELF: the `PT_LOAD` segments, the entry point and the
program-header facts the auxiliary vector publishes.

Deviation: LPS stores segment bytes as lowercase hex chunks (`list PrimString.string`, read
by the `rocq-read-file` plugin) and decodes them with `segment_byte_at`. Here a segment holds
its bytes directly; `Segment.byteAt` is `segment_byte_at` on well-formed hex. The image is
therefore produced in Lean (for instance by `Silmaril.Formats.ELF`), not by a plugin.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `MemImageType.v:16` `Segment`. `perms` holds the `"rwx"` letters. -/
structure Segment where
  base : Nat
  size : Nat
  perms : String
  bytes : List Byte
  deriving DecidableEq, Repr

/-- LPS `MemImageType.v:64` `PhdrInfo`: `AT_PHDR`, `AT_PHENT` and `AT_PHNUM`. -/
structure PhdrInfo where
  addr : Nat
  ent : Nat
  num : Nat
  deriving DecidableEq, Repr

/-- LPS `MemImageType.v:95` `seg_readable`. -/
def Segment.readable (s : Segment) : Bool := s.perms.contains 'r'
/-- LPS `MemImageType.v:96` `seg_writable`. -/
def Segment.writable (s : Segment) : Bool := s.perms.contains 'w'
/-- LPS `MemImageType.v:97` `seg_executable`. -/
def Segment.executable (s : Segment) : Bool := s.perms.contains 'x'

/-- LPS `RiscvSemantics.v:298` `segment_byte_at`, over decoded bytes. -/
def Segment.byteAt (s : Segment) (off : Nat) : Option Byte := s.bytes[off]?

/-- LPS `MemImageType.v:125` `Image`. -/
structure Image where
  segments : List Segment
  initPc : Nat
  phdrs : PhdrInfo
  deriving DecidableEq, Repr

/-- LPS `RiscvSemantics.v:332` `find_segment`: the first segment holding `[addr, addr+n)`. -/
def findSegment : List Segment → Int → Int → Option Segment
  | [], _, _ => none
  | seg :: rest, addr, n =>
    if (seg.base : Int) ≤ addr ∧ addr + n ≤ seg.base + seg.size then some seg
    else findSegment rest addr n

/-- LPS `RiscvSemantics.v:397` `memory_read`: `n` bytes of a readable segment. -/
def memoryRead (segs : List Segment) (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs (uns addr) n with
  | some seg =>
    if seg.readable then
      let off := (uns addr - seg.base).toNat
      (List.range n).mapM fun k => seg.byteAt (off + k)
    else none
  | none => none

/-- LPS `RiscvSemantics.v:528` `wview` (segment part): a writable segment's byte. -/
def segmentWritableByte (segs : List Segment) (addr : Word) : Option Byte :=
  match findSegment segs (uns addr) 1 with
  | some seg => if seg.writable then seg.byteAt (uns addr - seg.base).toNat else none
  | none => none

end Silmaril.Process.LPS
