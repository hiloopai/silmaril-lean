module

public import Silmaril.X86.BlockCert9.Defs

/-!
# Bir9 block certificates on the open machine over `Ext8`

A function proof on the open machine `Silmaril.X86.Open` is assembled from **block
certificates**: straight-line pieces of the function's code, each with its Bir9 listing.
Proof obligations are stated over the pure block semantics (`runL`, rewritten to the Bir9
summary `runB` by `Bir9.liftBlock_sound`), never by stepping fetched machine states. These
are the certificates of `BlockCert9` for code proved on `Open` (and moved to `Open9` with
`FnContract.toOpen9`): the listings are checked against `Ext.decode`, and they may contain
the Bir9 extension form `LInstr.x (.cmov …)`, which `BlockCert9` rejects.

* `listingAt code o L`: the decidable check that the listing `L` is what `Ext.decode` reads
  in `code` from offset `o` on, instruction after instruction; that every instruction is an
  `X86.Ext` form (`toExt`; the extension form `LInstr.x (.cmov …)` is accepted as the `Ext`
  CMOV it denotes); that no instruction writes memory (`noWrite`); and that every instruction
  but the last falls through (`fallsThrough`). It is closed by `decide +kernel` against the
  transcribed bytes, which ties a Bir9 block to the binary.
* `runL L m`, `runB b m`: a listing and a Bir9 block as partial maps of machine states
  (`Bir9.runL9`, `Bir9.runB9`: the XMM registers, which `X86.Ext` does not have, start at
  zero and are dropped).
* `Blk`, `FunCert`: a function as a list of blocks (offset and listing) with an annotation
  and a measure per block offset; `FunCert.VC` is the verification condition: from every
  block whose annotation holds, the block runs and arrives at the exit condition or at an
  annotated block with a smaller measure.
* `blockSub`: a checked block as a summary (`SegVC.Call`) for the segment VC generator.

The bridge `execBlock_open` (a checked listing that executes is a run of `Open.step`) and
the assembly `FunCert.total` (VCs give a total System V `FnContract`) are in
`BlockCert/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM)
open Silmaril.X86.Bir9 (LInstr XState XResult execBlock Block liftBlock)
open Silmaril.Machine.Execution (Reaches)

/- The instruction classes, the leaf frame and the leaf spec are `BlockCert9`'s, and the
register lookup and the result reading are `Bir9.lookupE` and `Bir9.ofX`. -/
export Silmaril.X86.BlockCert9 (rmIsReg fallsThrough noWrite Frame leafSpec)
export Silmaril.X86.Bir9 (lookupE ofX)

/-- The `X86.Ext` instruction a listed instruction denotes. The Bir9 extension form
`cmov` has the semantics of the `Ext` CMOV (`execL_toExt`); every other extension form is
rejected. -/
def toExt : LInstr → Option Silmaril.X86.Ext.Instr
  | .ext i => some i
  | .x (.cmov sz c dst src) => some (.cmov sz c dst src)
  | _ => none

/-- **The listing check.** `L` is what `Ext.decode` reads in `code` from offset `o` on;
every instruction is an `Ext` form, writes no memory, and all but the last fall through. -/
def listingAt (code : List Byte) : Nat → List (LInstr × Nat) → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    match toExt i with
    | none => false
    | some e =>
      decide (Silmaril.X86.Ext.decode ((code.drop o).take l) = some (e, l)) &&
        decide (o + l ≤ code.length) && noWrite e && (rest.isEmpty || fallsThrough e) &&
        listingAt code (o + l) rest

/-- The lifting state of a core: no XMM state (all zero). -/
def xs (c : State) : XState := ⟨c, fun _ => 0⟩

/-- A straight-line listing as a partial map of machine states (`Bir9.runL9`). -/
def runL (L : List (LInstr × Nat)) (m : MState) : Option MState :=
  Bir9.ofX (execBlock L (xs m.core) m.memory)

/-- A Bir9 block as a partial map of machine states (`Bir9.runB9`). -/
def runB (b : Block) (m : MState) : Option MState :=
  Bir9.ofX (b.run (xs m.core) m.memory)

/-- A block of a function: its offset in the code and its listing. -/
structure Blk where
  off : Nat
  instrs : List (LInstr × Nat)

/-- A function certificate: the code it is loaded from, its blocks, and per block offset
an annotation (from the entry state `m0` to the current state) and a measure. -/
structure FunCert where
  code : List Byte
  base : Word
  blocks : List Blk
  ann : Nat → MState → MState → Prop
  measure : Nat → MState → MState → Nat

namespace FunCert

variable (F : FunCert)

/-- Every block's listing is checked against the code. -/
def checked : Bool := F.blocks.all fun b => listingAt F.code b.off b.instrs

/-- Where a block may arrive, from entry state `m0`, under the measure bound `μ`: the exit
condition `Q`, or an annotated block with a smaller measure. -/
def Next (Q : MState → MState → Prop) (m0 : MState) (μ : Nat) (m' : MState) : Prop :=
  Q m0 m' ∨ ∃ b ∈ F.blocks, m'.core.rip = F.base + BitVec.ofNat 64 b.off ∧
    F.ann b.off m0 m' ∧ F.measure b.off m0 m' < μ

/-- **The verification condition** of a function certificate with exit condition `Q`. -/
def VC (Q : MState → MState → Prop) : Prop :=
  ∀ b ∈ F.blocks, ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', runL b.instrs m = some m' ∧ F.Next Q m0 (F.measure b.off m0 m) m'

/-- The VC of one block. -/
def BlockVC (Q : MState → MState → Prop) (b : Blk) : Prop :=
  ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', runL b.instrs m = some m' ∧ F.Next Q m0 (F.measure b.off m0 m) m'

end FunCert

end Silmaril.X86.BlockCert
