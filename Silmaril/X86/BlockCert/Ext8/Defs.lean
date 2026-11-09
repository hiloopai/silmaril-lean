module

public import Silmaril.X86.BlockCert.Defs

/-!
# Block certificates over `Ext8` listings

`BlockCert` checks Bir9 listings of `X86.Ext` forms. Code with the 8-bit ALU forms that only
`Ext8` decodes (for example zlib's byte-wise CRC, `xor (%rcx),%al`, `32 /r`) cannot be listed
there. This module is the same certificate shape over **`Ext8` listings**, for leaf code that
writes no memory:

* `listing8 code o L`: `L` is what the open machine's listing decoder `Open.decode` reads in
  `code` from offset `o` on, instruction after instruction (closed by `decide +kernel`);
* `run8 L m`: the listing executed by `Ext8.exec`, **checked as it runs**: every instruction
  must leave the memory unchanged, and every instruction but the last must continue at the
  next one. The checks are part of the run, so no case analysis over `Ext8` is needed; on a
  concrete block they reduce to `True` by `simp`;
* `Cert`, `Cert.VC`: a function as blocks (offset, listing) with an annotation and a measure,
  as `BlockCert.FunCert`.

The bridge (`run8_open`: a checked listing whose run succeeds is a run of `Open.step`) and the
assembly (`Cert.total`) are in `BlockCert/Ext8/Thms.lean`. The leaf frame lemmas of
`BlockCert` (`Frame`, `Frame.step`, `Frame.result`) apply unchanged.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert8

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)

/-- A listed `Ext8` instruction with its length. -/
abbrev LI := Silmaril.X86.Ext8.Instr × Nat

/-- **The listing check.** `L` is what `Open.decode` reads in `code` from offset `o` on. -/
def listing8 (code : List Byte) : Nat → List LI → Bool
  | _, [] => true
  | o, (i, l) :: rest =>
    decide (Open.decode ((code.drop o).take l) = some (i, l)) && decide (o + l ≤ code.length) &&
      listing8 code (o + l) rest

open Classical in
/-- **A checked run.** Execute each instruction with `Ext8.exec`; fail unless it keeps the
memory and, when it is not the last one, continues at the next instruction. -/
noncomputable def run8 : List LI → MState → Option MState
  | [], m => some m
  | (i, l) :: rest, m =>
    match Silmaril.X86.Ext8.exec i m.core m.memory l with
    | .ok c mem =>
      if mem = m.memory ∧ (rest = [] ∨ c.rip = m.core.rip + BitVec.ofNat 64 l) then
        run8 rest ⟨c, m.memory⟩
      else none
    | _ => none

/-- A block: its offset in the code and its listing. -/
structure Blk where
  off : Nat
  instrs : List LI

/-- A function certificate over `Ext8` listings. -/
structure Cert where
  code : List Byte
  base : Word
  blocks : List Blk
  ann : Nat → MState → MState → Prop
  measure : Nat → MState → MState → Nat

namespace Cert

variable (F : Cert)

/-- Every block's listing is checked against the code. -/
def checked : Bool := F.blocks.all fun b => listing8 F.code b.off b.instrs

/-- Where a block may arrive: the exit condition, or an annotated block with a smaller
measure. -/
def Next (Q : MState → MState → Prop) (m0 : MState) (μ : Nat) (m' : MState) : Prop :=
  Q m0 m' ∨ ∃ b ∈ F.blocks, m'.core.rip = F.base + BitVec.ofNat 64 b.off ∧
    F.ann b.off m0 m' ∧ F.measure b.off m0 m' < μ

/-- The VC of one block. -/
def BlockVC (Q : MState → MState → Prop) (b : Blk) : Prop :=
  ∀ m0 m, F.ann b.off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 b.off → Loaded m.memory F.base F.code →
    ∃ m', run8 b.instrs m = some m' ∧ F.Next Q m0 (F.measure b.off m0 m) m'

/-- **The verification condition**: every block's VC. -/
def VC (Q : MState → MState → Prop) : Prop := ∀ b ∈ F.blocks, F.BlockVC Q b

end Cert

end Silmaril.X86.BlockCert8
