module

public import Silmaril.Machine.X86.FnContract.Defs
public import Silmaril.Machine.X86.Bir.Defs

/-!
# Bir block certificates on the open machine

A function proof on the open machine (`Silmaril.Machine.X86.Open`) is assembled from **block
certificates**: straight-line pieces of the function's code, each with its Bir listing.
Proof obligations are stated over the pure block semantics (`runL`, rewritten to the Bir
summary `runB` by `liftBlock_sound`), never by stepping fetched machine states.

* `listingAt code o L`: the decidable check that the listing `L` is what `Ext.decode` reads
  in `code` from offset `o` on, instruction after instruction; that every instruction is an
  `X86.Ext` form (`toExt`; the extension form `LInstr.x (.cmov …)` is accepted as the `Ext`
  CMOV it denotes); that no instruction writes memory (`noWrite`); and that every instruction
  but the last falls through (`fallsThrough`). It is closed by `decide +kernel` against the
  transcribed bytes, which ties a Bir block to the binary.
* `runL L m`, `runB b m`: a listing and a Bir block as partial maps of machine states (the
  XMM registers, which `X86.Ext` does not have, start at zero and are dropped).
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

namespace Silmaril.Machine.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM)
open Silmaril.X86.Lift.Bir (LInstr XState XResult execBlock Block liftBlock)
open Silmaril.Machine.Execution (Reaches)

/-- A register operand. -/
def rmIsReg : RM → Bool
  | .reg _ => true
  | .mem _ => false

/-- Instructions that always continue at the next instruction when they retire. -/
def fallsThrough : Silmaril.X86.Ext.Instr → Bool
  | .jmp _ | .jmp8 _ | .jcc _ _ | .jcc8 _ _ | .call _ | .ret | .ud2 => false
  | _ => true

/-- Instructions that never write memory (register destinations, loads, compares, `ret`,
`pop`, jumps). Pushes, calls and memory destinations are excluded. -/
def noWrite : Silmaril.X86.Ext.Instr → Bool
  | .mov _ d _ | .movI _ d _ | .movI16 d _ | .movI8 d _ | .store _ d _ | .alu _ _ d _
  | .aluI _ _ d _ | .aluI8 _ _ d _ | .incdec _ _ d | .unary _ _ d | .shift _ _ d _
  | .setcc _ d => rmIsReg d
  | .pushRM _ | .push _ | .call _ => false
  | _ => true

/-- The `X86.Ext` instruction a listed instruction denotes. The Bir extension form
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

/-- A successful lifting result as a machine state. -/
def ofX : XResult → Option MState
  | .ok s mem => some ⟨s.core, mem⟩
  | _ => none

/-- A straight-line listing as a partial map of machine states. -/
def runL (L : List (LInstr × Nat)) (m : MState) : Option MState :=
  ofX (execBlock L (xs m.core) m.memory)

/-- A Bir block as a partial map of machine states. -/
def runB (b : Block) (m : MState) : Option MState :=
  ofX (b.run (xs m.core) m.memory)

/-- A register's final expression in a Bir register map, by decidable equality (the form
`simp` evaluates; `Block.reg` uses `List.lookup`). -/
def lookupE (r : Reg) : List (Reg × Silmaril.X86.Lift.Bir.E) → Silmaril.X86.Lift.Bir.E
  | [] => .reg r
  | (a, e) :: rest => if r = a then e else lookupE r rest

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

/-- The leaf-function frame invariant from entry state `m0` to the current state `m`: the
entry satisfied the System V entry obligations, and memory, `rsp` and the callee-saved
registers are as at entry. -/
structure Frame (m0 m : MState) : Prop where
  abi : FnContract.AbiEntry m0.core m0.memory
  mem : m.memory = m0.memory
  rsp : m.core.read .rsp = m0.core.read .rsp
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, m.core.read r = m0.core.read r

/-- The spec of a leaf function loaded at `base` from `code`, entered at offset `off`, that
writes no memory, with functional postcondition `post`. -/
def leafSpec (base : Word) (code : List Byte) (off : Nat) (post : MState → MState → Prop) :
    FnContract.Spec MState where
  entry m := Loaded m.memory base code ∧ m.core.rip = base + BitVec.ofNat 64 off
  footprint _ _ := False
  post := post

end Silmaril.Machine.X86.BlockCert
