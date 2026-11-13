module

public import Silmaril.X86.Ext9.Defs

/-!
# `Narrow9`: the 8- and 16-bit shift, rotate and carry forms that no lower decoder reads

`Ext` has shifts and rotates at 32 and 64 bits, `Ext8` has `shl`/`shr`/`sar` at 8 bits and
the 8-bit ALU forms without ADC/SBB, and `Ext9` has ADC/SBB at 32 and 64 bits and the 16-bit
ADD/OR/AND/SUB/XOR/CMP/TEST forms. Compiled C code that works on `unsigned short` and
`unsigned char` values uses the forms in between. zlib's `deflate` is an example: `d_code`
shifts a 16-bit distance (`66 C1 E8 07`, `shr ax, 7`), `_tr_flush_bits` shifts the 16-bit
`bi_buf` field in memory (`66 C1 6B 10 08`), and the gzip header code computes level flags
with `sbb cl, 0xff` (`80 D9 FF`). `Narrow9` decodes and executes these forms. It defines
the forms only; `Str9FsXN` puts them at the end of `Str9FsX`'s fetch chain.

| Form | Bytes (Intel SDM Vol. 2) | `New` |
| --- | --- | --- |
| `rol`/`ror`/`shl`/`shr`/`sar r/m16` by imm8, 1, CL | `66 REX? C1 /d ib`, `66 REX? D1 /d`, `66 REX? D3 /d` (`d` = 0 1 4 5 7) | `shift16` |
| `rol`/`ror r/m8` by imm8, 1, CL | `REX? C0 /0 /1 ib`, `REX? D0 /0 /1`, `REX? D2 /0 /1` | `rot8` |
| `adc`/`sbb r/m8, r8` | `REX? 10 /r`, `REX? 18 /r` | `adc8` |
| `adc`/`sbb r8, r/m8` | `REX? 12 /r`, `REX? 1A /r` | `adc8R` |
| `adc`/`sbb al, imm8` | `14 ib`, `1C ib` | `adc8A` |
| `adc`/`sbb r/m8, imm8` | `REX? 80 /2 /3 ib` | `adc8I` |
| `adc`/`sbb r/m16, r16` | `66 REX? 11 /r`, `66 REX? 19 /r` | `adc16` |
| `adc`/`sbb r16, r/m16` | `66 REX? 13 /r`, `66 REX? 1B /r` | `adc16R` |
| `adc`/`sbb ax, imm16` | `66 15 iw`, `66 1D iw` | `adc16A` |
| `adc`/`sbb r/m16, imm16` / `imm8` | `66 REX? 81 /2 /3 iw`, `66 REX? 83 /2 /3 ib` | `adc16I` |

The 8-bit forms take every byte register, AH..BH without REX (`Ext8.RM8`, `Ext8.BReg`).
Rejected (`none`), never misread: the FS override, `F2`, `F3`, REX.W (on the 16-bit forms it
would select 64 bits; on the 8-bit forms it is meaningless), `66` on the 8-bit forms, a REX
prefix on `adc`/`sbb al`/`ax, imm`, `RCL`/`RCR` (`/2`, `/3`) and the `/6` alias of `SHL`.

## Semantics (Intel SDM Vol. 2), and the documented choices

* **Shifts and rotates**: the count is masked to five bits (`& 1FH`) for 8- and 16-bit
  operands, so it can exceed the width. A masked count of zero changes nothing: no write, no
  flag (the operand is read, so an unreadable operand still faults). Otherwise the result is
  `ShiftOp.result` (a rotate is taken modulo the width; a shift by at least the width gives
  `0`, or copies of the sign bit for SAR). Flags: `shiftFlagsN`. Below the width they are
  `Ext.ShiftOp.flags`, the SDM's formulas: SHL/SHR/SAR set CF to the last bit shifted out,
  SF, ZF, PF from the result, leave AF undefined, and define OF only for a count of 1.
  ROL/ROR set CF to the bit rotated into bit 0 (ROL) or the top bit (ROR), define OF only for
  a count of 1, and keep SF, ZF, AF, PF. At or above the width, SHL/SHR leave CF undefined
  (SDM: "CF is undefined for SHL and SHR where the count is greater than or equal to the
  size of the destination"), SAR sets CF to the sign bit, OF and AF are undefined, and SF,
  ZF, PF follow the result, as `Ext8.shift8Flags` does at 8 bits. Rotates follow the SDM
  pseudo-code at every masked count: the rotation is by the count modulo the width and CF is
  read off the result, so a rotate by exactly the width keeps the value and still sets CF.
* **ADC/SBB**: `Ext9.carryResult`/`Ext9.carryFlags` at width 8 or 16: all six flags defined.
  If CF is undefined the step reports `.undefinedCondition .b` and does not retire. The
  source operand is read first, so a data fault wins.
* **Narrow writes**: a 16-bit register destination keeps bits 63:16 (`Ext.writeNarrow .w`);
  an 8-bit one keeps the other 56 bits (`Ext8.BReg.write`).

This is a handwritten model of the SDM. It is **trusted**. The vectors in
`Str9FsXN/Vectors.lean` compare it with an Intel Core i7-8700 on random inputs; they are
evidence, not a proof.
-/

@[expose] public section

namespace Silmaril.X86.Narrow9

open Silmaril.X86 (Reg Word State Flags Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz ShiftOp Count Result retire readNarrow writeNarrow
  Rex Opc Pfx ModrmPart ByteParser pHead pImm16)
open Silmaril.X86.Ext8 (pM optP RM8 BReg rm8Of reg8Of)
open Silmaril.X86.Ext9 (rmOf regOf pIb16 carryResult carryFlags)
open Silmaril.Process (Memory)

/-! ## Instructions -/

/-- The forms of `Narrow9`. `sub` selects SBB over ADC. -/
inductive New where
  /-- `rol`/`ror`/`shl`/`shr`/`sar r/m16` (`66 C1 /d ib`, `66 D1 /d`, `66 D3 /d`). -/
  | shift16 (op : ShiftOp) (dst : RM) (count : Count)
  /-- `rol`/`ror r/m8` (`C0 /0 /1 ib`, `D0 /0 /1`, `D2 /0 /1`). -/
  | rot8 (op : ShiftOp) (dst : RM8) (count : Count)
  /-- `adc`/`sbb r/m8, r8` (`10 /r`, `18 /r`). -/
  | adc8 (sub : Bool) (dst : RM8) (src : BReg)
  /-- `adc`/`sbb r8, r/m8` (`12 /r`, `1A /r`). -/
  | adc8R (sub : Bool) (dst : BReg) (src : RM8)
  /-- `adc`/`sbb al, imm8` (`14 ib`, `1C ib`). -/
  | adc8A (sub : Bool) (imm : BitVec 8)
  /-- `adc`/`sbb r/m8, imm8` (`80 /2 /3 ib`). -/
  | adc8I (sub : Bool) (dst : RM8) (imm : BitVec 8)
  /-- `adc`/`sbb r/m16, r16` (`66 11 /r`, `66 19 /r`). -/
  | adc16 (sub : Bool) (dst : RM) (src : Reg)
  /-- `adc`/`sbb r16, r/m16` (`66 13 /r`, `66 1B /r`). -/
  | adc16R (sub : Bool) (dst : Reg) (src : RM)
  /-- `adc`/`sbb ax, imm16` (`66 15 iw`, `66 1D iw`). -/
  | adc16A (sub : Bool) (imm : BitVec 16)
  /-- `adc`/`sbb r/m16, imm16` (`66 81 /2 /3 iw`; `66 83 /2 /3 ib`, sign-extended). -/
  | adc16I (sub : Bool) (dst : RM) (imm : BitVec 16)
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- The shift or rotate of group-2 digit `d` (`/0 /1 /4 /5 /7`). -/
def shiftOfDigit (d : BitVec 3) : Option ShiftOp :=
  match d.toNat with
  | 0 => some .rol | 1 => some .ror | 4 => some .shl | 5 => some .shr | 7 => some .sar
  | _ => none

/-- The rotate of group-2 digit `d` (`/0 /1`). -/
def rotOfDigit (d : BitVec 3) : Option ShiftOp :=
  match d.toNat with
  | 0 => some .rol | 1 => some .ror | _ => none

/-- ADC (`/2`) or SBB (`/3`): whether the digit is SBB, or reject. -/
def carryOfDigit (d : BitVec 3) : Option Bool :=
  match d.toNat with
  | 2 => some false | 3 => some true | _ => none

/-- The body of an 8-bit form (no legacy prefix, no REX.W), after REX and opcode. -/
def pBody8 (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    if b = 0x10#8 ∨ b = 0x18#8 then
      ByteParser.map (fun mp => .adc8 (b = 0x18#8) (rm8Of rex mp) (reg8Of rex mp)) pM
    else if b = 0x12#8 ∨ b = 0x1A#8 then
      ByteParser.map (fun mp => .adc8R (b = 0x1A#8) (reg8Of rex mp) (rm8Of rex mp)) pM
    else if (b = 0x14#8 ∨ b = 0x1C#8) ∧ rex = none then
      ByteParser.map (fun v => .adc8A (b = 0x1C#8) v) ByteParser.byte
    else if b = 0x80#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (carryOfDigit mp.1.reg)) fun sub =>
          ByteParser.map (fun v => .adc8I sub (rm8Of rex mp) v) ByteParser.byte
    else if b = 0xC0#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (rotOfDigit mp.1.reg)) fun op =>
          ByteParser.map (fun v => .rot8 op (rm8Of rex mp) (.imm v)) ByteParser.byte
    else if b = 0xD0#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun op => .rot8 op (rm8Of rex mp) .one) (optP (rotOfDigit mp.1.reg))
    else if b = 0xD2#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun op => .rot8 op (rm8Of rex mp) .cl) (optP (rotOfDigit mp.1.reg))
    else ByteParser.fail
  | .two _ => ByteParser.fail

/-- The body of a `66`-prefixed (16-bit) form (no REX.W), after REX and opcode. -/
def pBody16 (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    if b = 0x11#8 ∨ b = 0x19#8 then
      ByteParser.map (fun mp => .adc16 (b = 0x19#8) (rmOf rex mp) (regOf rex mp)) pM
    else if b = 0x13#8 ∨ b = 0x1B#8 then
      ByteParser.map (fun mp => .adc16R (b = 0x1B#8) (regOf rex mp) (rmOf rex mp)) pM
    else if (b = 0x15#8 ∨ b = 0x1D#8) ∧ rex = none then
      ByteParser.map (fun v => .adc16A (b = 0x1D#8) v) pImm16
    else if b = 0x81#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (carryOfDigit mp.1.reg)) fun sub =>
          ByteParser.map (fun v => .adc16I sub (rmOf rex mp) v) pImm16
    else if b = 0x83#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (carryOfDigit mp.1.reg)) fun sub =>
          ByteParser.map (fun v => .adc16I sub (rmOf rex mp) v) pIb16
    else if b = 0xC1#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (shiftOfDigit mp.1.reg)) fun op =>
          ByteParser.map (fun v => .shift16 op (rmOf rex mp) (.imm v)) ByteParser.byte
    else if b = 0xD1#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun op => .shift16 op (rmOf rex mp) .one) (optP (shiftOfDigit mp.1.reg))
    else if b = 0xD3#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun op => .shift16 op (rmOf rex mp) .cl) (optP (shiftOfDigit mp.1.reg))
    else ByteParser.fail
  | .two _ => ByteParser.fail

/-- The parser of a form: no FS override, no REX.W, and either no legacy prefix (the 8-bit
forms) or a single `66` (the 16-bit forms). -/
def pNew : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = true ∨ (h.2.2.1.getD Rex.zero).w = true then ByteParser.fail
    else
      match h.2.1 with
      | .none => pBody8 h.2.2.1 h.2.2.2
      | .opsize => pBody16 h.2.2.1 h.2.2.2
      | _ => ByteParser.fail

/-- Decode a form; the instruction and the number of bytes consumed. -/
def decodeNew (bytes : List Byte) : Option (New × Nat) :=
  match pNew bytes with
  | .ok i rest => some (i, bytes.length - rest.length)
  | _ => none

/-! ## Semantics -/

/-- The flags after a shift or rotate of `x` by the nonzero masked count `c < 32` (the
SDM, as described in the module documentation). -/
def shiftFlagsN {n : Nat} (op : ShiftOp) (x : BitVec n) (c : Nat) (old : Flags) : Flags :=
  if c < n ∨ op = .rol ∨ op = .ror then op.flags x c old
  else
    let r := op.result x c
    ⟨if op = .sar then some x.msb else none, some (Silmaril.X86.Ext.parityN r), none,
      some (Silmaril.X86.Ext.isZeroN r), some r.msb, none⟩

/-- The masked count of an 8- or 16-bit shift or rotate (`& 1FH`). -/
def maskedCount (count : Count) (s : State) : Nat := (count.raw s).toNat % 32

/-- A 16-bit shift or rotate. -/
def shift16Step (op : ShiftOp) (dst : RM) (count : Count) (s : State) (memory : Memory)
    (next : Word) : Result :=
  let c := maskedCount count s
  match readNarrow .w dst s memory next with
  | none => .dataFault
  | some x =>
    if c = 0 then retire next (some (s, memory))
    else retire next ((writeNarrow .w dst (op.result x c) s memory next).map fun r =>
      ({ r.1 with flags := shiftFlagsN op x c s.flags }, r.2))

/-- An 8-bit rotate. -/
def rot8Step (op : ShiftOp) (dst : RM8) (count : Count) (s : State) (memory : Memory)
    (next : Word) : Result :=
  let c := maskedCount count s
  match dst.read s memory next with
  | none => .dataFault
  | some x =>
    if c = 0 then retire next (some (s, memory))
    else retire next ((dst.write (op.result x c) s memory next).map fun r =>
      ({ r.1 with flags := shiftFlagsN op x c s.flags }, r.2))

/-- An 8-bit ADC/SBB with destination `dst` and second operand `y`. -/
def carry8Step (sub : Bool) (dst : RM8) (y : BitVec 8) (s : State) (memory : Memory)
    (next : Word) : Result :=
  match dst.read s memory next with
  | none => .dataFault
  | some x =>
    match s.flags.carry with
    | none => .undefinedCondition .b
    | some c =>
      retire next ((dst.write (carryResult sub x y c) s memory next).map fun r =>
        ({ r.1 with flags := carryFlags sub x y c }, r.2))

/-- A 16-bit ADC/SBB with destination `dst` and second operand `y`. -/
def carry16Step (sub : Bool) (dst : RM) (y : BitVec 16) (s : State) (memory : Memory)
    (next : Word) : Result :=
  match readNarrow .w dst s memory next with
  | none => .dataFault
  | some x =>
    match s.flags.carry with
    | none => .undefinedCondition .b
    | some c =>
      retire next ((writeNarrow .w dst (carryResult sub x y c) s memory next).map fun r =>
        ({ r.1 with flags := carryFlags sub x y c }, r.2))

/-- **Execute a form**, given the address of the next instruction. -/
def execNew (i : New) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .shift16 op dst count => shift16Step op dst count s memory next
  | .rot8 op dst count => rot8Step op dst count s memory next
  | .adc8 sub dst src => carry8Step sub dst (src.read s) s memory next
  | .adc8R sub dst src =>
    match src.read s memory next with
    | none => .dataFault
    | some y => carry8Step sub (.reg dst) y s memory next
  | .adc8A sub imm => carry8Step sub (.reg (.low .rax)) imm s memory next
  | .adc8I sub dst imm => carry8Step sub dst imm s memory next
  | .adc16 sub dst src => carry16Step sub dst ((s.read src).setWidth 16) s memory next
  | .adc16R sub dst src =>
    match readNarrow .w src s memory next with
    | none => .dataFault
    | some y => carry16Step sub (.reg dst) y s memory next
  | .adc16A sub imm => carry16Step sub (.reg .rax) imm s memory next
  | .adc16I sub dst imm => carry16Step sub dst imm s memory next

/-! ## Fetch -/

/-- Fetch a form: `decodeNew` reads the fetch window and the bytes it consumed are
executable. `none` if not decodable as a form; `some none` if not fetchable. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (New × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

end Silmaril.X86.Narrow9
