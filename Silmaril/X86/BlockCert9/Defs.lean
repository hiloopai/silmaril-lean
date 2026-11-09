module

public import Silmaril.X86.Bir9.Defs
public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.FnContract.Defs

/-!
# Block certificates on the open machine over `Ext9`

A function proof on `Open9` is assembled from **block certificates**: straight-line pieces
of the function's code, each with its listing. Proof obligations are stated over the pure
block semantics (an `Ext9` listing run, or a Bir9 block), never by stepping fetched machine
states. A block's code is

* `.x9 L`: an `Ext9` listing, checked by `listingAt9` against `Open9.decode` and run by
  `runX` (instruction after instruction, `Ext9.exec`); or
* `.bir L`: a Bir9 listing of `Ext` and `Ext9` forms (`Bir9.toX9L`), checked as the `Ext9`
  listing it is and run by `Bir9.runL9`. With the lifter's certificate
  `Bir9.liftBlock L = some b` its run is the pure Bir9 block `b` (`runX_eq_runB9`,
  `Code.run_bir` in `BlockCert9/Thms.lean`).

`listingAt9 code o L` is the decidable check that `L` is what `Open9.decode` reads in `code`
from offset `o` on, that no instruction writes memory (`noWrite9`) and that every
instruction but the last falls through (`fallsThrough9`). It is closed by `decide +kernel`
against the bytes, which ties a block to the binary. The 8-bit `Ext8` forms are not
accepted (no `rip` or memory lemmas for them yet).

`FunCert9` is a function as a list of blocks with an annotation and a measure per block
offset; `FunCert9.VC` is the verification condition: from every block whose annotation
holds, the block runs and arrives at the exit condition or at an annotated block with a
smaller measure. `FunCert9.total` (in `BlockCert9/Thms.lean`) turns the VCs into a total
`FnContract.Spec` on `Open9.isa`.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert9

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM)

/-! ## Instruction classes -/

/-- A register operand. -/
def rmIsReg : RM → Bool
  | .reg _ => true
  | .mem _ => false

/-- `Ext` instructions that always continue at the next instruction when they retire. -/
def fallsThrough : Silmaril.X86.Ext.Instr → Bool
  | .jmp _ | .jmp8 _ | .jcc _ _ | .jcc8 _ _ | .call _ | .ret | .ud2 => false
  | _ => true

/-- `Ext` instructions that never write memory (register destinations, loads, compares,
`ret`, `pop`, jumps). Pushes, calls and memory destinations are excluded. -/
def noWrite : Silmaril.X86.Ext.Instr → Bool
  | .mov _ d _ | .movI _ d _ | .movI16 d _ | .movI8 d _ | .store _ d _ | .alu _ _ d _
  | .aluI _ _ d _ | .aluI8 _ _ d _ | .incdec _ _ d | .unary _ _ d | .shift _ _ d _
  | .setcc _ d => rmIsReg d
  | .pushRM _ | .push _ | .call _ => false
  | _ => true

/-- New forms that always continue at the next instruction when they retire. -/
def fallsThroughNew : Ext9.New → Bool
  | .callInd _ | .jmpInd _ | .repRet => false
  | _ => true

/-- New forms that never write memory. -/
def noWriteNew : Ext9.New → Bool
  | .adc _ _ d _ | .adcI _ _ d _ | .alu16 _ d _ | .alu16I _ d _ => rmIsReg d
  | .callInd _ | .pushI _ => false
  | _ => true

/-- An `Ext9` instruction that falls through (8-bit `Ext8` forms are not accepted). -/
def fallsThrough9 : Ext9.Instr → Bool
  | .ext8 (.base e) => fallsThrough e
  | .ext8 (.new _) => false
  | .new n => fallsThroughNew n

/-- An `Ext9` instruction that writes no memory (8-bit `Ext8` forms are not accepted). -/
def noWrite9 : Ext9.Instr → Bool
  | .ext8 (.base e) => noWrite e
  | .ext8 (.new _) => false
  | .new n => noWriteNew n

/-! ## Listings -/

/-- **The listing check.** `L` is what `Open9.decode` reads in `code` from offset `o` on;
no instruction writes memory, and all but the last fall through. -/
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

/-- The code of a block: a Bir9 listing or an `Ext9` listing. -/
inductive Code where
  | bir (L : List (Bir9.LInstr × Nat))
  | x9 (L : List (Ext9.Instr × Nat))

/-- The check of a block's code at offset `o`. A Bir9 listing is checked as the `Ext9`
listing it denotes, and rejected if it has an `XInstr` or SSE entry. -/
def Code.check (code : List Byte) (o : Nat) : Code → Bool
  | .bir L =>
    match Bir9.toX9L L with
    | some L9 => listingAt9 code o L9
    | none => false
  | .x9 L => listingAt9 code o L

/-- A block's code as a partial map of machine states. -/
def Code.run : Code → MState → Option MState
  | .bir L => Bir9.runL9 L
  | .x9 L => runX L

/-! ## Function certificates -/

/-- A block of a function: its offset and its code. -/
structure Blk where
  off : Nat
  code : Code

/-- A function certificate: the code it is loaded from, its blocks, and per block offset an
annotation (from the entry state `m0` to the current state) and a measure. -/
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

/-- Where a block may arrive, from entry state `m0`, under the measure bound `μ`: the exit
condition `Q`, or an annotated block with a smaller measure. -/
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

/-! ## Leaf functions -/

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

end Silmaril.X86.BlockCert9
