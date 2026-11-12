module

public import Silmaril.X86.Bir9.Defs
public import Silmaril.X86.Ext8.Basic

/-! # Bir9X: Bir9 lifting of the `Ext8` byte forms and of ADC/SBB

Silmaril's Bir9 lifter (`Silmaril.X86.Bir9`) lifts listings of `Ext` and `Ext9` instructions
(`LInstr.ext`, `LInstr.n9`). Two families that compiled code uses are not lifted:

* the `Ext8` byte forms (`Ext8.New`: `op r/m8, r8`, `op r8, r/m8`, `op r/m8, imm8`,
  `op al, imm8`, `test r/m8, r8`, `shl/shr/sar r/m8`), which `Open9.decode` reads as
  `.ext8 (.new i)` but which have no `LInstr` entry;
* ADC and SBB (`Ext9.New.adc`, `.adcR`, `.adcI`), for which `Bir9.symStep` returns `none`.

This module extends the lifter without changing it:

* `XL` is a listing entry: a Bir9 entry (`base`) or an `Ext8` byte form (`e8`), executed by
  `Ext8.execNew` (the semantics `Open9` runs for these bytes);
* `symStepX` handles `e8` entries and ADC/SBB and defers everything else to `Bir9.symStep`.
  The new symbolic shapes are built from Bir9's own statements and expressions: `sRead`,
  `sWriteN` (byte writes keep the other register bits, `E.merge`), `E.shift`, `Stmt.cond`
  (the carry-in of ADC/SBB, which stops the block when CF is undefined), `E.xop .carry` and
  `F.xop .carry`;
* `liftBlockX` is `symExecX` followed by Bir9's simplifier.

Byte forms on the legacy high-byte registers (AH, CH, DH, BH), shifts by `CL` and shifts by
a masked count of 0 or of 8 and more are not lifted (`none`): the 8-bit shift's flags differ
from `E.shift`'s modular count there.

Soundness (`Silmaril.X86.Bir9X.liftBlockX_sound`, in `Thms.lean`): `liftBlockX L = some b`
gives `execBlockX L s mem = b.run s mem`; the proof unfolds `Ext8.execNew` and
`Ext9.carryStep` against the symbolic shapes, reusing Bir9's simulation relation.

Nothing here is trusted beyond the `Ext8`/`Ext9` semantics the lifter is proved against.
-/

@[expose] public section

namespace Silmaril.X86.Bir9X

open Silmaril.X86 (Reg Word State Byte AluOp)
open Silmaril.X86.Ext (Sz RM Mem Narrow ShiftOp Count Cond)
open Silmaril.X86.Bir9
open Silmaril.Process (Memory)

/-- A listing entry: a Bir9 entry, or an `Ext8` byte form. -/
inductive XL where
  | base (i : LInstr)
  | e8 (i : Silmaril.X86.Ext8.New)
  deriving DecidableEq, Repr

/-- Execute a listing entry with its byte length. -/
def XL.exec : XL → XState → Memory → Nat → XResult
  | .base i, s, m, len => i.exec s m len
  | .e8 i, s, m, len =>
    liftR s.xmm (Silmaril.X86.Ext8.execNew i s.core m (s.core.rip + BitVec.ofNat 64 len))

/-- Run a straight-line listing: stop at the first non-`ok` result. -/
def execBlockX : List (XL × Nat) → XState → Memory → XResult
  | [], s, m => .ok s m
  | (i, len) :: rest, s, m =>
    match i.exec s m len with
    | .ok s' m' => execBlockX rest s' m'
    | r => r

/-- The `Ext9` instruction a listing entry is (`Ext`, `Ext9` and `Ext8` forms). -/
def toX9X : XL → Option Silmaril.X86.Ext9.Instr
  | .base i => toX9 i
  | .e8 i => some (.ext8 (.new i))

/-! ## Symbolic steps -/

/-- A byte operand on a low-byte register or in memory, as an `RM`; `none` on AH..BH. -/
def rm8 : Silmaril.X86.Ext8.RM8 → Option RM
  | .reg (.low r) => some (.reg r)
  | .reg (.high _) => none
  | .mem m => some (.mem m)

/-- `op r8, r/m8` on a low-byte register `d`: read the source, then ALU on `d`'s low byte. -/
def sAluR8 (σ : SState) (len : Nat) (op : AluOp) (d : Reg) (src : RM) : List Stmt × SState :=
  if op = .cmp then sReadF σ len src 1 (fun y => .alu 8 op (σ.regs d) y)
  else sReadSetF σ len src 1 d (fun y => .merge .b (σ.regs d) (.alu 8 op (σ.regs d) y))
    (fun y => .alu 8 op (σ.regs d) y)

/-- Read-modify-write of a byte operand, with flags. -/
def sRMW8 (σ : SState) (len : Nat) (dst : RM) (val : E → E) (fl : E → F) :
    List Stmt × SState :=
  let nx := nxOf σ len
  let rd := sRead σ nx 1 dst
  let w := sWriteN rd.2.2 nx .b dst (val rd.2.1)
  (rd.1 ++ w.1, { w.2 with flags := fl rd.2.1, rip := nx })

/-- The masked count of a byte shift, when it is a constant. -/
def countConst : Count → Option Nat
  | .one => some 1
  | .imm n => some (n.toNat % 32)
  | .cl => none

/-- `shl`/`shr`/`sar r/m8` by a constant `c` with `0 < c < 8`. -/
def sShift8 (σ : SState) (len : Nat) (op : ShiftOp) (dst : RM) (c : Nat) : List Stmt × SState :=
  sRMW8 σ len dst (fun x => .shift 8 op x (.imm (BitVec.ofNat 64 c)))
    (fun x => .shift 8 op x (.imm (BitVec.ofNat 64 c)) σ.flags)

/-- ADC (`sub = false`) / SBB on `dst` with second operand `y`: read `dst`, evaluate the
carry-in (`cond .b`: stops with `undefinedCondition .b` when CF is undefined), write. -/
def sCarry (σ : SState) (len : Nat) (sz : Sz) (sub : Bool) (dst : RM) (y : E) :
    List Stmt × SState :=
  let nx := nxOf σ len
  let rd := sRead σ nx sz.bytes dst
  let c : E := .v rd.2.2.n
  let r : E := .xop (.carry sz sub) rd.2.1 y c
  let w := sWriteRM rd.2.2.fresh nx sz dst r
  (rd.1 ++ [.cond .b σ.flags] ++ w.1,
    { w.2 with flags := .xop (.carry sz sub) rd.2.1 y c, rip := nx })

/-- One symbolic step of an `Ext8` byte form; `none` for the forms not lifted. -/
def symStep8 (σ : SState) (i : Silmaril.X86.Ext8.New) (len : Nat) : Option (List Stmt × SState) :=
  match i with
  | .alu op dst (.low r) =>
    match rm8 dst with
    | some o => symStep σ (.x (.alu8 op o (.reg r))) len
    | none => none
  | .aluI op dst imm =>
    match rm8 dst with
    | some o => symStep σ (.x (.alu8 op o (.imm imm))) len
    | none => none
  | .aluA op imm => symStep σ (.x (.alu8 op (.reg .rax) (.imm imm))) len
  | .test dst (.low r) =>
    match rm8 dst with
    | some o => symStep σ (.x (.test8 o (.reg r))) len
    | none => none
  | .aluR op (.low d) src =>
    match rm8 src with
    | some o => some (sAluR8 σ len op d o)
    | none => none
  | .shift op dst cnt =>
    match rm8 dst, countConst cnt with
    | some o, some c => if 0 < c ∧ c < 8 then some (sShift8 σ len op o c) else none
    | _, _ => none
  | _ => none

/-- One symbolic step of a listing entry. -/
def symStepX (σ : SState) (i : XL) (len : Nat) : Option (List Stmt × SState) :=
  match i with
  | .e8 i => symStep8 σ i len
  | .base (.n9 (.adc sz sub dst src)) => some (sCarry σ len sz sub dst (σ.regs src))
  | .base (.n9 (.adcI sz sub dst imm)) => some (sCarry σ len sz sub dst (immSz sz imm))
  | .base i => symStep σ i len

/-- Symbolically execute a listing. -/
def symGoX : List (XL × Nat) → SState → Option (List Stmt × SState)
  | [], σ => some ([], σ)
  | (i, len) :: rest, σ =>
    match symStepX σ i len with
    | none => none
    | some (s1, σ1) =>
      match symGoX rest σ1 with
      | none => none
      | some (s2, σ2) => some (s1 ++ s2, σ2)

def symExecX (instrs : List (XL × Nat)) : Option Block :=
  (symGoX instrs SState.init).map fun p => SState.toBlock p.1 p.2

/-- **The extended lifter**: lift a listing and simplify the block. -/
def liftBlockX (instrs : List (XL × Nat)) : Option Block := (symExecX instrs).map Block.simp

end Silmaril.X86.Bir9X
