module

public import Silmaril.Machine.X86.BlockCert.Defs
public import Silmaril.Machine.X86.Open9.Defs

/-!
# Block certificates on the open machine over `Ext9`

`BlockCert` (Bir listings checked against `Ext.decode`, run on `Open.step`) extended to the
`Ext9` forms. A block's code is either

* `.bir L`: a Bir listing, checked by `BlockCert.listingAt` and run by `BlockCert.runL`, as
  before (its VC can be rewritten to a pure Bir term with `BlockCert.runL_eq_runB`); or
* `.x9 L`: an `Ext9` listing, checked by `listingAt9` against `Open9.decode` and run by
  `runX` (instruction after instruction, `Ext9.exec`). It may mix `X86.Ext` forms and new
  `Ext9` forms; the 8-bit `Ext8` forms are not accepted here (no rip/memory lemmas for
  them yet).

`FunCert9` is `BlockCert.FunCert` over such blocks; its VC has the same shape, and
`FunCert9.total` (in `BlockCert9/Thms.lean`) gives a total `FnContract.Spec` on `Open9.isa`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM)
open Silmaril.X86.Lift.Bir (LInstr)

/-- New forms that always continue at the next instruction when they retire. -/
def fallsThroughNew : Ext9.New → Bool
  | .callInd _ | .jmpInd _ | .repRet => false
  | _ => true

/-- New forms that never write memory. -/
def noWriteNew : Ext9.New → Bool
  | .adc _ _ d _ | .adcI _ _ d _ | .alu16 _ d _ | .alu16I _ d _ => BlockCert.rmIsReg d
  | .callInd _ | .pushI _ => false
  | _ => true

/-- An `Ext9` instruction that falls through. -/
def fallsThrough9 : Ext9.Instr → Bool
  | .ext8 (.base e) => BlockCert.fallsThrough e
  | .ext8 (.new _) => false
  | .new n => fallsThroughNew n

/-- An `Ext9` instruction that writes no memory (8-bit `Ext8` forms are not accepted). -/
def noWrite9 : Ext9.Instr → Bool
  | .ext8 (.base e) => BlockCert.noWrite e
  | .ext8 (.new _) => false
  | .new n => noWriteNew n

/-- **The `Ext9` listing check.** `L` is what `Open9.decode` reads in `code` from offset `o`
on; no instruction writes memory, and all but the last fall through. -/
def listingAt9 (code : List Byte) : Nat → List (Ext9.Instr × Nat) → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    decide (Open9.decode ((code.drop o).take l) = some (i, l)) &&
      decide (o + l ≤ code.length) && noWrite9 i && (rest.isEmpty || fallsThrough9 i) &&
      listingAt9 code (o + l) rest

/-- An `Ext9` listing as a partial map of machine states. -/
def runX : List (Ext9.Instr × Nat) → MState → Option MState
  | [], m => some m
  | (i, l) :: rest, m =>
    match Ext9.exec i m.core m.memory l with
    | .ok c mem => runX rest ⟨c, mem⟩
    | _ => none

/-- The code of a block: a Bir listing or an `Ext9` listing. -/
inductive Code where
  | bir (L : List (LInstr × Nat))
  | x9 (L : List (Ext9.Instr × Nat))

/-- The check of a block's code at offset `o`. -/
def Code.check (code : List Byte) (o : Nat) : Code → Bool
  | .bir L => BlockCert.listingAt code o L
  | .x9 L => listingAt9 code o L

/-- A block's code as a partial map of machine states. -/
def Code.run : Code → MState → Option MState
  | .bir L => BlockCert.runL L
  | .x9 L => runX L

/-- A block of a function: its offset and its code. -/
structure Blk where
  off : Nat
  code : Code

/-- A function certificate over `Ext9` (as `BlockCert.FunCert`). -/
structure FunCert9 where
  code : List Byte
  base : Word
  blocks : List Blk
  ann : Nat → MState → MState → Prop
  measure : Nat → MState → MState → Nat

namespace FunCert9

variable (F : FunCert9)

/-- Every block's code is checked against the code. -/
def checked : Bool := F.blocks.all fun b => b.code.check F.code b.off

/-- Where a block may arrive: the exit condition, or an annotated block with a smaller
measure. -/
def Next (Q : MState → MState → Prop) (m0 : MState) (μ : Nat) (m' : MState) : Prop :=
  Q m0 m' ∨ ∃ b ∈ F.blocks, m'.core.rip = F.base + BitVec.ofNat 64 b.off ∧
    F.ann b.off m0 m' ∧ F.measure b.off m0 m' < μ

/-- The VC of one block. -/
def BlockVC (Q : MState → MState → Prop) (b : Blk) : Prop :=
  ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', b.code.run m = some m' ∧ F.Next Q m0 (F.measure b.off m0 m) m'

/-- **The verification condition**: every block's VC. -/
def VC (Q : MState → MState → Prop) : Prop := ∀ b ∈ F.blocks, F.BlockVC Q b

end FunCert9

end Silmaril.Machine.X86.BlockCert9
