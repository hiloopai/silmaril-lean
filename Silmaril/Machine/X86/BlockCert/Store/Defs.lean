module

public import Silmaril.Machine.X86.BlockCert.Defs

/-!
# Block certificates with a memory write

`Silmaril.Machine.X86.BlockCert` checks listings that write no memory (`listingAt`), so a
function certificate there keeps the code image loaded for free. Byte loops store. This
module admits **one memory write per block, as its last instruction**:

* `listingAtW code o L`: as `listingAt`, except that the last instruction may write memory.
  Every earlier instruction writes no memory and falls through, so the whole block is fetched
  from the entry memory, before the write. A loop body `load; store; add; cmp; jne` is cut into
  `load; store` and `add; cmp; jne`.
* `FunCert.checkedW`, `FunCert.NextW`, `FunCert.VCW`, `FunCert.BlockVCW`: the function
  certificate of `BlockCert` with these listings. Because a block may change memory, arriving
  at a block also requires the code image to be loaded in the new memory (`NextW`); the block
  VC proves it, usually because the write is outside the code (`loaded_of_writesWithin`).

The bridge (`runLW_open`: a checked listing that executes is a run of `Open.step`) and the
assembly (`FunCert.totalW`) are in `Store/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Lift.Bir (LInstr)

/-- **The listing check with a final write.** `L` is what `Ext.decode` reads in `code` from
offset `o` on; every instruction is an `Ext` form; every instruction but the last writes no
memory and falls through. -/
def listingAtW (code : List Byte) : Nat → List (LInstr × Nat) → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    match toExt i with
    | none => false
    | some e =>
      decide (Silmaril.X86.Ext.decode ((code.drop o).take l) = some (e, l)) &&
        decide (o + l ≤ code.length) && (rest.isEmpty || (noWrite e && fallsThrough e)) &&
        listingAtW code (o + l) rest

namespace FunCert

variable (F : FunCert)

/-- Every block's listing is checked against the code, with a final write allowed. -/
def checkedW : Bool := F.blocks.all fun b => listingAtW F.code b.off b.instrs

/-- Where a block may arrive: the exit condition, or an annotated block with a smaller
measure **in a memory where the code is still loaded**. -/
def NextW (Q : MState → MState → Prop) (m0 : MState) (μ : Nat) (m' : MState) : Prop :=
  Q m0 m' ∨ ∃ b ∈ F.blocks, m'.core.rip = F.base + BitVec.ofNat 64 b.off ∧
    Loaded m'.memory F.base F.code ∧ F.ann b.off m0 m' ∧ F.measure b.off m0 m' < μ

/-- The verification condition with writing blocks. -/
def VCW (Q : MState → MState → Prop) : Prop :=
  ∀ b ∈ F.blocks, ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', runL b.instrs m = some m' ∧ F.NextW Q m0 (F.measure b.off m0 m) m'

/-- The VC of one block. -/
def BlockVCW (Q : MState → MState → Prop) (b : Blk) : Prop :=
  ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', runL b.instrs m = some m' ∧ F.NextW Q m0 (F.measure b.off m0 m) m'

end FunCert

end Silmaril.Machine.X86.BlockCert
