module

public import Silmaril.X86.Features.Ext.SseMerged.Extension
public import Silmaril.X86.Features.Ext.Sse2.Vectors
public meta import Silmaril.X86.Features.Ext.SseMerged.Extension
public meta import Silmaril.X86.Features.Ext.Sse2.Vectors

/-!
# Differential agreement of the two SSE/SSE2 lanes

The native differential vectors of the `Sse2` lane (`Sse2.Vectors.vectors`,
recorded on an i7-8700 by `scripts/x86-features/gen_sse2_vectors.py`) are
replayed through the recovered `SsePacked` lane: for every vector whose form
`SsePacked` has (`toPacked (form n) = some j`), `SsePacked.ext.exec j` must
reproduce the recorded hardware outputs with the checker of
`Sse2.Checks.checkVector`. Since `Sse2` passes the same vectors, the two
semantics agree on all of them. The forms without an `SsePacked` counterpart
(`movRRStore`, `movqStore` with a register destination) are counted
separately.

The GNU as encodings (`Sse2.Vectors.encodings`) are replayed too:
`SsePacked.encode` gives the same bytes for the translated form and
`SsePacked.decode` reads them back, or rejects them when there is no
counterpart (this is also the theorem `decode_sse2_encode`).
-/

@[expose] public section

namespace Silmaril.X86.Features.SseMerged.Vectors

open Silmaril.X86
open Silmaril.X86.Features.Sse2.Checks
open Silmaril.X86.Features.Sse2.Vectors (form vectors encodings)

/-- `Sse2.Checks.checkVector` with the `SsePacked` semantics. -/
def checkPacked (j : SsePacked.Instr) (a b rax off mem ra rax' mem' : Nat) : Bool :=
  match SsePacked.ext.exec j 5 (vstate a b rax (vbase + off)) (vmemory mem) with
  | .retired s m =>
    s.zmm 0 == BitVec.ofNat 512 (upperTag + ra) && s.zmm 1 == BitVec.ofNat 512 b &&
      s.core.read .rax == BitVec.ofNat 64 rax' && s.core.read .rdi == BitVec.ofNat 64 (vbase + off) &&
      s.rip == 0x1005 && m.readBytes vbase 32 == some (bytesOf mem' 32)
  | _ => false

/-- The `SsePacked` check of a vector line, or `none` when `SsePacked` has no
counterpart of its form. -/
def packedLine : List Nat → Option Bool
  | [n, a, b, rax, off, mem, ra, rax', mem'] =>
    (toPacked (form n)).map fun j => checkPacked j a b rax off mem ra rax' mem'
  | _ => some false

-- Every vector of a shared form passes with the `SsePacked` semantics.
#guard (hexFields vectors).all fun l => (packedLine l).getD true

-- The number of vectors of shared forms, and of forms only `Sse2` has.
#guard ((hexFields vectors).filter fun l => (packedLine l).isSome).length = 3792

#guard ((hexFields vectors).filter fun l => (packedLine l).isNone).length = 84

-- The GNU as encodings: same bytes, read back, or rejected without a counterpart.
#guard encodings.all fun (i, bs) =>
  match toPacked i with
  | some j => SsePacked.encode j == bs && SsePacked.decode bs == some (j, bs.length)
  | none => SsePacked.decode bs == none

end Silmaril.X86.Features.SseMerged.Vectors
