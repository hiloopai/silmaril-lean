module

public import Silmaril.X86.Loose.Forms.Mem
public import Silmaril.X86.Ext9.Defs

/-!
# Loose forms, group `Int`: integer moves, ALU, tests, shifts and `nop`

Each form is a `Kernel` (`Forms/Mem.lean`): at most one memory read, then an effect that
writes registers and at most one memory span. What each form **promises**:

* `rip` advances to the next instruction (`nextOf c l`);
* the result (register value or stored bytes), exactly as `X86.Ext`/`Ext8`/`Ext9` compute it;
* CF, ZF, SF and OF as Ext computes them (`FlagEff.loose`); flag-free forms keep every flag.

Where it is **looser** than Ext:

* PF and AF are undefined (any value) after every flag-writing form, although Ext defines
  PF, and AF for the arithmetic forms;
* a flag that Ext leaves `none` (for example OF after a shift by more than one, AF after a
  shift, CF/OF after an 8-bit SHL/SHR by a count of 8 or more) is undefined;
* where Ext reports `dataFault` (a read or write not permitted), the form is unspecified
  (`Kernel.bad`).

The specification functions:

* `specExt : Ext.Instr → Option EffSpec`: the Ext forms of `Int`, and the memory forms
  `load` and `store` (`loadS`, `storeS`);
* `specNew8 : Ext8.New → Option EffSpec`: the 8-bit forms with legacy high-byte registers;
* `specNew9 : Ext9.New → Option EffSpec`: the 16-bit ALU/TEST forms and the immediate TESTs;
* `spec9 : Ext9.Instr → Option EffSpec` combines them (`none` on the forms of the other
  groups).
-/

@[expose] public section

namespace Silmaril.X86.Loose.Forms

open Silmaril.X86 (State Word Byte Flags Reg AluOp)
open Silmaril.X86.Ext (Sz Narrow RM Count ShiftOp UnOp leBytes leValue narrowMask
  logicFlagsN subFlagsN negFlagsN incFlagsN decFlagsN byteSwap)
open Silmaril.Process (Memory)
open Silmaril.X86.Loose

/-- An effect with no write that retires to `next`. -/
abbrev Effect.retire (next : Word) (flags : FlagEff := FlagEff.keepAll) : Effect :=
  Effect.ofWrites next ([], []) flags

/-! ## Moves -/

/-- `mov r/m, reg` (`89 /r`). -/
def movK (sz : Sz) (dst : RM) (src : Reg) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (szDst sz dst c next (sz.read c src))

/-- `mov r/m, imm32` (`C7 /0 id`). -/
def movIK (sz : Sz) (dst : RM) (imm : BitVec 32) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (szDst sz dst c next (imm.signExtend sz.bits))

/-- `mov r/m16, imm16` (`66 C7 /0 iw`). -/
def movI16K (dst : RM) (imm : BitVec 16) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (narrowDst .w dst c next imm)

/-- `mov r8, r/m8` (`8A /r`). -/
def mov8K (dst : Reg) (src : RM) : Kernel where
  rd := rmRd 1 src
  body c next inp := Effect.ofWrites next
    ([(dst, (c.read dst &&& ~~~(0xFF#64)) ||| (rmVal 8 src c inp).setWidth 64)], [])

/-- `mov r/m8, imm8` (`C6 /0 ib`). -/
def movI8K (dst : RM) (imm : BitVec 8) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (narrowDst .b dst c next imm)

/-- `mov r32, imm32` (`B8+r id`), zero-extending. -/
def movI32K (dst : Reg) (imm : BitVec 32) : Kernel where
  rd _ _ := none
  body _ next _ := Effect.ofWrites next ([(dst, imm.setWidth 64)], [])

/-- `mov r64, imm64` (`REX.W B8+r io`). -/
def movabsK (dst : Reg) (imm : BitVec 64) : Kernel where
  rd _ _ := none
  body _ next _ := Effect.ofWrites next ([(dst, imm)], [])

/-- MOVZX/MOVSX from 8 or 16 bits. -/
def movxK (sx : Bool) (sz : Sz) (n : Narrow) (dst : Reg) (src : RM) : Kernel where
  rd := rmRd n.bytes src
  body c next inp :=
    let v := rmVal n.bits src c inp
    Effect.ofWrites next
      ([(dst, (if sx then v.signExtend sz.bits else v.setWidth sz.bits).setWidth 64)], [])

/-- `movsxd r64, r/m32` (`REX.W 63 /r`). -/
def movsxdK (dst : Reg) (src : RM) : Kernel where
  rd := rmRd 4 src
  body c next inp := Effect.ofWrites next ([(dst, (rmVal 32 src c inp).signExtend 64)], [])

/-- `lea` (`8D /r`): the effective address, truncated to the operand size. -/
def leaK (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext.Mem) : Kernel where
  rd _ _ := none
  body c next _ :=
    Effect.ofWrites next ([(dst, ((src.addr c next).setWidth sz.bits).setWidth 64)], [])

/-! ## ALU and tests -/

/-- `op r/m, y` at size `sz` (`alu`, `aluI`, `aluI8`, `aluA`): CMP writes nothing. -/
def aluK (sz : Sz) (op : AluOp) (dst : RM) (y : State → BitVec sz.bits) : Kernel where
  rd := rmRd sz.bytes dst
  body c next inp :=
    let x := rmVal sz.bits dst c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x (y c))
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next (szDst sz dst c next (Silmaril.X86.Ext.AluOp.resultN op x (y c))) fl

/-- `op reg, r/m` (`aluR`, the direction-1 form). -/
def aluRK (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) : Kernel where
  rd := rmRd sz.bytes src
  body c next inp :=
    let x := sz.read c dst
    let y := rmVal sz.bits src c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x y)
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next
      ([(dst, (Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64)], []) fl

/-- A flags-only form reading an `r/m` operand of `k` bytes at width `n` (TEST, CMP8). -/
def flagRMK (n k : Nat) (dst : RM) (f : State → BitVec n → Flags) : Kernel where
  rd := rmRd k dst
  body c next inp := Effect.retire next (FlagEff.loose (f c (rmVal n dst c inp)))

/-- A flags-only form on registers (TEST/CMP on the accumulator). -/
def flagRegK (f : State → Flags) : Kernel where
  rd _ _ := none
  body c next _ := Effect.retire next (FlagEff.loose (f c))

/-- `inc r/m` and `dec r/m` (`FF /0`, `FF /1`). -/
def incdecK (sz : Sz) (dec : Bool) (dst : RM) : Kernel where
  rd := rmRd sz.bytes dst
  body c next inp :=
    let x := rmVal sz.bits dst c inp
    Effect.ofWrites next (szDst sz dst c next (if dec then x - 1#sz.bits else x + 1#sz.bits))
      (FlagEff.loose (if dec then decFlagsN x c.flags else incFlagsN x c.flags))

/-- `neg r/m` (`F7 /3`). -/
def negK (sz : Sz) (dst : RM) : Kernel where
  rd := rmRd sz.bytes dst
  body c next inp :=
    let x := rmVal sz.bits dst c inp
    Effect.ofWrites next (szDst sz dst c next (0#sz.bits - x)) (FlagEff.loose (negFlagsN x))

/-- `not r/m` (`F7 /2`): no flags. -/
def notK (sz : Sz) (dst : RM) : Kernel where
  rd := rmRd sz.bytes dst
  body c next inp := Effect.ofWrites next (szDst sz dst c next (~~~(rmVal sz.bits dst c inp)))

/-- Shifts and rotates (`D1`/`D3`/`C1 /digit`); the count is masked to the operand size. -/
def shiftK (sz : Sz) (op : ShiftOp) (dst : RM) (count : Count) : Kernel where
  rd := rmRd sz.bytes dst
  body c next inp :=
    let n := (count.raw c).toNat % sz.bits
    let x := rmVal sz.bits dst c inp
    Effect.ofWrites next (szDst sz dst c next (op.result x n))
      (FlagEff.loose (op.flags x n c.flags))

/-- `bswap` (`0F C8+r`). -/
def bswapK (sz : Sz) (dst : Reg) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next ([(dst, (byteSwap sz (sz.read c dst)).setWidth 64)], [])

/-- CDQ/CQO (`99`). -/
def cxdK (sz : Sz) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next
    ([(.rdx, (if (sz.read c .rax).msb then BitVec.allOnes sz.bits else 0#sz.bits).setWidth 64)],
      [])

/-- CWDE/CDQE (`98`). -/
def cxeK : Sz → Kernel
  | .d => { rd := fun _ _ => none
            body := fun c next _ => Effect.ofWrites next
              ([(.rax, (((c.read .rax).setWidth 16).signExtend 32).setWidth 64)], []) }
  | .q => { rd := fun _ _ => none
            body := fun c next _ => Effect.ofWrites next
              ([(.rax, (Sz.d.read c .rax).signExtend 64)], []) }

/-- `nop` and `endbr64`: only `rip` advances. -/
def nopK : Kernel where
  rd _ _ := none
  body _ next _ := Effect.retire next

/-! ## `Ext8` byte forms (legacy high-byte registers) -/

/-- An 8-bit ALU step (`Ext8.alu8`). -/
def alu8K (op : AluOp) (dst : Silmaril.X86.Ext8.RM8) (y : State → BitVec 8) : Kernel where
  rd := rm8Rd dst
  body c next inp :=
    let x := rm8Val dst c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x (y c))
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next (rm8Dst dst c next (Silmaril.X86.Ext.AluOp.resultN op x (y c))) fl

/-- `op r8, r/m8` (`Ext8.New.aluR`): the destination is a byte register. -/
def alu8RK (op : AluOp) (dst : Silmaril.X86.Ext8.BReg) (src : Silmaril.X86.Ext8.RM8) :
    Kernel where
  rd := rm8Rd src
  body c next inp :=
    let x := dst.read c
    let y := rm8Val src c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x y)
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next ([bregDst c dst (Silmaril.X86.Ext.AluOp.resultN op x y)], []) fl

/-- `test r/m8, r8` over `RM8`. -/
def test8K (dst : Silmaril.X86.Ext8.RM8) (y : State → BitVec 8) : Kernel where
  rd := rm8Rd dst
  body c next inp := Effect.retire next (FlagEff.loose (logicFlagsN (rm8Val dst c inp &&& y c)))

/-- An 8-bit shift (`Ext8.New.shift`): the count is masked to 5 bits; a zero count writes
nothing and keeps the flags. -/
def shift8K (op : ShiftOp) (dst : Silmaril.X86.Ext8.RM8) (count : Count) : Kernel where
  rd := rm8Rd dst
  body c next inp :=
    let n := (count.raw c).toNat % 32
    let x := rm8Val dst c inp
    if n = 0 then Effect.retire next
    else Effect.ofWrites next (rm8Dst dst c next (op.result x n))
      (FlagEff.loose (Silmaril.X86.Ext8.shift8Flags op x n c.flags))

/-- `mov r/m8, r8` over `RM8`. -/
def mov8bK (dst : Silmaril.X86.Ext8.RM8) (src : Silmaril.X86.Ext8.BReg) : Kernel where
  rd _ _ := none
  body c next _ := Effect.ofWrites next (rm8Dst dst c next (src.read c))

/-- `mov r8, r/m8` over `RM8`. -/
def mov8RK (dst : Silmaril.X86.Ext8.BReg) (src : Silmaril.X86.Ext8.RM8) : Kernel where
  rd := rm8Rd src
  body c next inp := Effect.ofWrites next ([bregDst c dst (rm8Val src c inp)], [])

/-- MOVZX/MOVSX from an `RM8`. -/
def movx8K (sx : Bool) (sz : Sz) (dst : Reg) (src : Silmaril.X86.Ext8.RM8) : Kernel where
  rd := rm8Rd src
  body c next inp :=
    let v := rm8Val src c inp
    Effect.ofWrites next
      ([(dst, (if sx then v.signExtend sz.bits else v.setWidth sz.bits).setWidth 64)], [])

/-! ## `Ext9` 16-bit forms -/

/-- A 16-bit ALU step (`Ext9.alu16`). -/
def alu16K (op : AluOp) (dst : RM) (y : State → BitVec 16) : Kernel where
  rd := rmRd 2 dst
  body c next inp :=
    let x := rmVal 16 dst c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x (y c))
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next (narrowDst .w dst c next (Silmaril.X86.Ext.AluOp.resultN op x (y c))) fl

/-- `op r16, r/m16` (`Ext9.New.alu16R`). -/
def alu16RK (op : AluOp) (dst : Reg) (src : RM) : Kernel where
  rd := rmRd 2 src
  body c next inp :=
    let x := (c.read dst).setWidth 16
    let y := rmVal 16 src c inp
    let fl := FlagEff.loose (Silmaril.X86.Ext.AluOp.flagsN op x y)
    if op = .cmp then Effect.retire next fl
    else Effect.ofWrites next (narrowDst .w (.reg dst) c next
      (Silmaril.X86.Ext.AluOp.resultN op x y)) fl

/-! ## The specification functions -/

/-- **The Ext forms of `Int`** (with `load` and `store`). -/
def specExt : Silmaril.X86.Ext.Instr → Option EffSpec
  | .mov sz dst src => some (movK sz dst src).spec
  | .movI sz dst imm => some (movIK sz dst imm).spec
  | .movI16 dst imm => some (movI16K dst imm).spec
  | .mov8 dst src => some (mov8K dst src).spec
  | .movI8 dst imm => some (movI8K dst imm).spec
  | .movI32 dst imm => some (movI32K dst imm).spec
  | .movabs dst imm => some (movabsK dst imm).spec
  | .load sz dst src => some (loadS sz dst src)
  | .store n dst src => some (storeS n dst src)
  | .movx sx sz n dst src => some (movxK sx sz n dst src).spec
  | .movsxd dst src => some (movsxdK dst src).spec
  | .lea sz dst src => some (leaK sz dst src).spec
  | .alu sz op dst src => some (aluK sz op dst (fun c => sz.read c src)).spec
  | .aluR sz op dst src => some (aluRK sz op dst src).spec
  | .aluI sz op dst imm => some (aluK sz op dst (fun _ => imm.signExtend sz.bits)).spec
  | .aluI8 sz op dst imm => some (aluK sz op dst (fun _ => imm.signExtend sz.bits)).spec
  | .aluA sz op imm => some (aluK sz op (.reg .rax) (fun _ => imm.signExtend sz.bits)).spec
  | .test sz dst src =>
    some (flagRMK sz.bits sz.bytes dst (fun c x => logicFlagsN (x &&& sz.read c src))).spec
  | .test8 dst src =>
    some (flagRMK 8 1 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 8))).spec
  | .testI8 dst imm => some (flagRMK 8 1 dst (fun _ x => logicFlagsN (x &&& imm))).spec
  | .testA8 imm => some (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 8 &&& imm))).spec
  | .cmpI8 dst imm => some (flagRMK 8 1 dst (fun _ x => subFlagsN x imm)).spec
  | .cmpA8 imm => some (flagRegK (fun c => subFlagsN ((c.read .rax).setWidth 8) imm)).spec
  | .testA sz imm =>
    some (flagRegK (fun c => logicFlagsN (sz.read c .rax &&& imm.signExtend sz.bits))).spec
  | .incdec sz dec dst => some (incdecK sz dec dst).spec
  | .unary sz .neg dst => some (negK sz dst).spec
  | .unary sz .not dst => some (notK sz dst).spec
  | .shift sz op dst count => some (shiftK sz op dst count).spec
  | .bswap sz dst => some (bswapK sz dst).spec
  | .cxd sz => some (cxdK sz).spec
  | .cxe sz => some (cxeK sz).spec
  | .nop _ => some nopK.spec
  | .endbr64 => some nopK.spec
  | _ => none

/-- **The `Ext8` byte forms of `Int`.** `setcc` belongs to `Ctl`. -/
def specNew8 : Silmaril.X86.Ext8.New → Option EffSpec
  | .alu op dst src => some (alu8K op dst src.read).spec
  | .aluR op dst src => some (alu8RK op dst src).spec
  | .aluA op imm => some (alu8K op (.reg (.low .rax)) (fun _ => imm)).spec
  | .aluI op dst imm => some (alu8K op dst (fun _ => imm)).spec
  | .test dst src => some (test8K dst src.read).spec
  | .shift op dst count => some (shift8K op dst count).spec
  | .mov dst src => some (mov8bK dst src).spec
  | .movR dst src => some (mov8RK dst src).spec
  | .movx sx sz dst src => some (movx8K sx sz dst src).spec
  | .setcc _ _ => none

/-- **The `Ext9` forms of `Int`**: 16-bit ALU and TEST, and the immediate TESTs. The others
belong to `MulDiv` or `Ctl`. -/
def specNew9 : Silmaril.X86.Ext9.New → Option EffSpec
  | .alu16 op dst src => some (alu16K op dst (fun c => (c.read src).setWidth 16)).spec
  | .alu16R op dst src => some (alu16RK op dst src).spec
  | .alu16I op dst imm => some (alu16K op dst (fun _ => imm)).spec
  | .alu16A op imm => some (alu16K op (.reg .rax) (fun _ => imm)).spec
  | .test16 dst src =>
    some (flagRMK 16 2 dst (fun c x => logicFlagsN (x &&& (c.read src).setWidth 16))).spec
  | .test16I dst imm => some (flagRMK 16 2 dst (fun _ x => logicFlagsN (x &&& imm))).spec
  | .test16A imm =>
    some (flagRegK (fun c => logicFlagsN ((c.read .rax).setWidth 16 &&& imm))).spec
  | .testI sz dst imm =>
    some (flagRMK sz.bits sz.bytes dst (fun _ x => logicFlagsN (x &&& imm.signExtend sz.bits))).spec
  | .testI8 dst imm => some (test8K dst (fun _ => imm)).spec
  | _ => none

/-- The `Ext8` forms of `Int`. -/
def specExt8 : Silmaril.X86.Ext8.Instr → Option EffSpec
  | .base i => specExt i
  | .new i => specNew8 i

/-- **The `Ext9` forms of `Int`.** -/
def spec9 : Silmaril.X86.Ext9.Instr → Option EffSpec
  | .ext8 i => specExt8 i
  | .new i => specNew9 i

end Silmaril.X86.Loose.Forms
