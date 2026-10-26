module

public import Silmaril.Process.LPS.Isa
public import Silmaril.Process.Memory

/-!
# LPS effects on Silmaril's `Process.Memory`

Silmaril's RV64 and x86-64 machines keep user memory as a `Process.Memory`: mapped regions
with read/write/execute permissions over a byte map. LPS keeps it as an overlay over the
read-only image (`Overlay`). This file gives the LPS operations on `Process.Memory`:

* the initial memory: one region per `PT_LOAD` segment with its permissions and bytes, and a
  read-write stack region from `sp - 8 MiB` to the page end of the entry block;
* the readable and writable views (`ms_read_byte`, `ms_writable_byte`): a byte with the
  permission;
* the effect application of LPS `Run.apply_effect`, in LPS's order: unmaps (remove the
  ranges from the regions and the bytes), zeros (map read-write and zero), copies (from the
  pre-effect memory) and writes (install the bytes; the specification has already checked
  that they are writable). Addresses wrap modulo `2^64` as LPS's `word` addresses do.

The correspondence with LPS: for every address, `readByte` of the result equals LPS's
`ms_read_byte` after `apply_effect`, provided that the memory before agreed with LPS's
overlay and that every zeroed or written range lies in a region LPS also treats as writable
memory. This is the invariant an instantiation proof maintains; it is not proved here.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Machines

open Silmaril.Process (Memory Region Permissions ByteMemory Access)

/-- The permissions a segment's `"rwx"` letters give. -/
def segmentPermissions (s : Segment) : Permissions := ⟨s.readable, s.writable, s.executable⟩

/-- The region of a `PT_LOAD` segment. -/
def segmentRegion (s : Segment) : Region := ⟨s.base, s.size, segmentPermissions s⟩

/-- Install bytes at consecutive addresses, wrapping modulo `2^64`. -/
def installWrapping (m : ByteMemory) (base : Nat) (bytes : List Byte) : ByteMemory :=
  (bytes.zipIdx).foldl (fun acc (b, k) => acc.insert ((base + k) % 2 ^ 64) b) m

/-- The part of a region outside `[lo, hi)`: zero, one or two regions. -/
def Region.subtract (r : Region) (lo hi : Nat) : List Region :=
  let left := if r.base < lo then [{ r with size := min r.size (lo - r.base) }] else []
  let right :=
    if hi < r.base + r.size then
      [{ r with base := max r.base hi, size := r.base + r.size - max r.base hi }]
    else []
  left ++ right

/-- Remove `[lo, hi)` from every region. -/
def regionsSubtract (rs : List Region) (lo hi : Nat) : List Region :=
  rs.flatMap (Region.subtract · lo hi)

/-- The initial memory: segment regions and bytes, and the stack region with the entry block
at `sp` over zeros. -/
def initialMemory (segs : List Segment) (sp : Word) (stack : List Byte) : Memory :=
  let stackLo := sp.toNat - stackMaxSize.toNat
  let stackTop := (pageRoundUp (uns sp + stack.length)).toNat
  let stackRegion : Region := ⟨stackLo, stackTop - stackLo, ⟨true, true, false⟩⟩
  let segBytes := segs.foldl (fun acc s => installWrapping acc s.base s.bytes) ∅
  let zeros := List.replicate (sp.toNat - stackLo) (0 : Byte)
  let withZeros := installWrapping segBytes stackLo zeros
  { regions := segs.map segmentRegion ++ [stackRegion]
    bytes := installWrapping withZeros sp.toNat stack }

/-- A byte with the given permission (`ms_read_byte`, `ms_writable_byte`). -/
def viewByte (mem : Memory) (access : Access) (addr : Word) : Option Byte :=
  if mem.permits access addr.toNat then mem.bytes[addr.toNat]? else none

/-- Unmap `[a, a+n)`. -/
def unmapRange (mem : Memory) (a n : Nat) : Memory :=
  { regions := regionsSubtract mem.regions a (a + n)
    bytes := (List.range n).foldl (fun acc k => acc.erase ((a + k) % 2 ^ 64)) mem.bytes }

/-- Map `[a, a+n)` read-write and fill it with zeros. -/
def zeroRange (mem : Memory) (a n : Nat) : Memory :=
  { regions := ⟨a, n, ⟨true, true, false⟩⟩ :: regionsSubtract mem.regions a (a + n)
    bytes := installWrapping mem.bytes a (List.replicate n 0) }

/-- Copy `c.len` bytes from the pre-effect memory `before` (absent bytes become absent). -/
def copyRange (before mem : Memory) (c : MemCopy) : Memory :=
  { mem with
    bytes := (List.range c.len.toNat).foldl (fun acc k =>
      let src := (c.src.toNat + k) % 2 ^ 64
      let dst := (c.dst.toNat + k) % 2 ^ 64
      match viewByte before .read (BitVec.ofNat 64 src) with
      | some b => acc.insert dst b
      | none => acc.erase dst) mem.bytes }

/-- LPS `Run.v:175` `apply_effect`, memory part, on a `Process.Memory`. -/
def applyMemoryEffect (mem : Memory) (eff : SyscallEffect) : Memory :=
  let unmapped := eff.unmaps.foldl (fun acc u => unmapRange acc u.1.toNat u.2.toNat) mem
  let zeroed := eff.zeros.foldl (fun acc z => zeroRange acc z.1.toNat z.2.toNat) unmapped
  let copied := eff.copies.foldl (copyRange mem) zeroed
  eff.writes.foldl (fun acc w => { acc with bytes := installWrapping acc.bytes w.1.toNat w.2 })
    copied

end Silmaril.Process.LPS.Machines
