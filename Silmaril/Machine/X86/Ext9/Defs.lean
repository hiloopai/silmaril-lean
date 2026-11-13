module

public import Silmaril.X86.Ext8.Basic

/-!
# `Ext9`: a conservative extension of `Ext8` with integer forms gcc emits

`Silmaril.X86.Ext8` (public silmaril-lean, rev `35a6f60`) decodes the `X86.Ext` forms and the
8-bit forms. The census of an earlier design note lists the integer forms it
still rejects that gate whole blocks: three-operand `imul`, `bsr`/`bsf`, `sbb`, indirect
`call`/`jmp`, `push imm` and the 16-bit (`66`-prefixed) ALU, CMP and TEST forms. `Ext9` adds
them, in the way `Ext8` extends `Ext`: `Instr` is `ext8 (i : Ext8.Instr)` or `new (i : New)`,
and `decode` tries `Ext8.decode` first, so every `Ext8` decode, execution and step is
unchanged (`decode_of_ext8`, `exec_ext8`, `step_eq_of_ne_undecodable`, `returns_of_ext8` in
`Ext9/Thms.lean`).

| Form | Bytes (Intel SDM Vol. 2) | `New` |
| --- | --- | --- |
| `imul r, r/m, imm32` / `imm8` | `REX? 69 /r id`, `REX? 6B /r ib` | `imulI` |
| `imul r/m` (one operand, signed `RDX:RAX`) | `REX? F7 /5` | `imul1` |
| `bsf r, r/m`, `bsr r, r/m` (no `F3`) | `REX? 0F BC /r`, `REX? 0F BD /r` | `bsf`, `bsr` |
| `adc`/`sbb r/m, r` | `REX? 11 /r`, `REX? 19 /r` | `adc` |
| `adc`/`sbb r, r/m` | `REX? 13 /r`, `REX? 1B /r` | `adcR` |
| `adc`/`sbb r/m, imm32` / `imm8` | `REX? 81 /2 /3 id`, `REX? 83 /2 /3 ib` | `adcI` |
| `call r/m64` | `REX? FF /2` | `callInd` |
| `jmp r/m64` | `REX? FF /4` | `jmpInd` |
| `notrack jmp r/m64` (F9) | `3E REX? FF /4` | `jmpInd` |
| `push imm8` / `imm32` (sign-extended to 64) | `6A ib`, `68 id` | `pushI` |
| `op r/m16, r16` (ADD OR AND SUB XOR CMP) | `66 REX? 01 09 21 29 31 39 /r` | `alu16` |
| `op r16, r/m16` | `66 REX? 03 0B 23 2B 33 3B /r` | `alu16R` |
| `op r/m16, imm16` / `imm8` | `66 REX? 81 /d iw`, `66 REX? 83 /d ib` | `alu16I` |
| `op ax, imm16` | `66 05 0D 25 2D 35 3D iw` | `alu16A` |
| `test r/m16, r16`, `test r/m16, imm16`, `test ax, imm16` | `66 REX? 85 /r`, `66 REX? F7 /0 iw`, `66 A9 iw` | `test16`, `test16I`, `test16A` |
| `test r/m32/64, imm32` | `REX? F7 /0 id` | `testI` |
| `test r/m8, imm8` (all byte registers, AH..BH without REX) | `REX? F6 /0 ib` | `testI8` |
| `bt r32/64, r32/64` (register destination) | `REX? 0F A3 /r`, `mod = 11` | `bt` |
| `rep ret` (`ret` with an `F3` prefix) | `F3 C3` (no REX) | `repRet` |

Rejected (`none`), never misread: the FS override, `F2`, `F3` on every form but `C3`, a `66` prefix with REX.W or on
a form not listed, `66` on `call`/`jmp`/`push`, a REX prefix on `push imm`, and every other
ModRM digit.

## Semantics (Intel SDM Vol. 2), and the documented choices

* **IMUL (three operand, `imulI`)**: `dst := trunc(src * sext(imm))`. CF = OF = the signed
  product does not fit (`Ext.imulFlags`, as for the two-operand `Ext` form). SF, ZF, AF, PF
  are undefined (`none`).
* **IMUL (one operand, `imul1`)**: `RDX:RAX := sext(RAX) * sext(src)` (32-bit: `EDX:EAX`,
  both zero-extended into the 64-bit registers). CF = OF = the high half is not the sign
  extension of the low half; SF, ZF, AF, PF undefined.
* **BSF/BSR**: for a nonzero source, `dst` is the index of the lowest / highest set bit and
  ZF is cleared; CF, OF, SF, AF and PF are undefined. For a **zero source the SDM leaves the
  destination undefined** (and sets ZF). The model does not pick a value: it reports
  `.undefinedCondition .e` (the condition `ZF = 1` under which the result is undefined) and
  does not retire. A proof can therefore never use a run through a zero-source BSF/BSR.
* **ADC/SBB**: `dst := x + y + CF` / `x - (y + CF)`, all six flags defined by the result:
  CF the unsigned carry / borrow, OF the signed overflow, AF the carry / borrow out of bit 3,
  SF, ZF, PF from the result (PF of the low byte). If CF is undefined (`none`) the result
  depends on an undefined flag and the model reports `.undefinedCondition .b` (the
  condition that reads CF). The source operand is read first, so a data fault wins.
* **NOTRACK JMP r/m64** (`3E FF /4`): the same semantics as `jmp r/m64`, at the longer length.
  In 64-bit mode `3E` (the DS override) is ignored for addressing (SDM Vol. 1 §3.4.2.1;
  Vol. 2A §2.1.1, "use with any branch instruction is reserved", except as the CET `notrack`
  prefix on near indirect `jmp`/`call`, SDM Vol. 1 §18.3.1.1). With CET indirect branch
  tracking enabled, `notrack` waives the `endbr64` check at the target. The model has no IBT
  state, so `jmp` and `notrack jmp` both jump without that check: for the plain form this is
  the pre-existing assumption that IBT is disabled (or every target is an `endbr64`); for the
  `notrack` form it is the hardware behaviour. The FS override is still refused, also after
  `3E` (`3E 64 FF …` is rejected). `3E FF /2` (`notrack call`) is not decoded.
* **CALL r/m64**: the target is read first (`[rsp+…]` is addressed with the old `rsp`), then
  the address of the next instruction is pushed and `rip` is the target. **JMP r/m64**:
  `rip` is the target. **PUSH imm**: the sign-extended immediate is pushed (64-bit push).
* **TEST r/m, imm**: the logical flags of `dst & sext(imm)` (`logicFlagsN`; AF undefined).
* **BT r, r**: CF is bit `src mod size` of `dst`; OF, SF, AF and PF are undefined (SDM).
  **ZF is undefined too**: the Intel SDM leaves ZF unaffected, but the AMD APM
  lists it as undefined, so a vendor-neutral model must not promise it (`zero := none`). The
  memory form (bit string addressing) is rejected.
* **REP RET** (`F3 C3`, the "two-byte return" that OpenSSL's `x86_64-xlate.pl` emits for every
  `ret`, and GCC emitted for AMD K8/K10 branch prediction): executed as `RET` (`Ext.exec .ret`:
  pop the return address into `rip`). **Documented choice, not an SDM rule.** The Intel SDM
  (Vol. 2A §2.1.1, group 1 prefixes) says to use the repeat prefixes only with the string and
  I/O instructions, and that their use with other instructions is reserved and may cause
  unpredictable behaviour; it does not say that `F3` is ignored on `RET`. AMD's software
  optimisation guides for K8 and family 10h recommend `REP RET` as a two-byte near return,
  and GCC and OpenSSL have emitted it for that reason; it runs as `RET` on the processors that
  execute that code. The model adopts this reading. The difftest does not exercise it (it
  compares straight-line forms, not control transfer).
  `F3` with a REX prefix or before any other opcode stays rejected. The sentinel machine
  `step exit` executes `rep ret` as an ordinary pop and jump (a retired step, never
  `returned`): functions ending in `rep ret` are run on the open machine (`Open9`), where
  having returned is a property of the state.
* **16-bit forms**: operands are the low 16 bits; a register destination keeps bits 63:16
  (`Ext.writeNarrow .w`, no zero extension); CMP and TEST write nothing. Flags are the
  `Ext` formulas at width 16 (`AluOp.flagsN`, `logicFlagsN`; AF is undefined after the
  logical forms).

This is a handwritten local model, written from the SDM text with `Ext`'s own helpers. It
is differentially tested against the x86-64 host in `tools/ext9-difftest` (register operands
and `[base+disp8]`, SIB, RIP-relative and FS-segment memory operands, random inputs, all
defined flags; CI runs a fixed-seed sample on every pull request, `ext9-difftest --ci`); see
an earlier design note and `round4/f5-trust.md`. **Vendor
assumption:** where Intel and AMD document different flag behaviour (BT's ZF), the flag is
undefined (`none`); every other defined flag is documented identically by both (not
re-checked against AMD hardware: the difftest has run on Intel hosts only).
-/

@[expose] public section

namespace Silmaril.Machine.X86.Ext9

open Silmaril.X86 (Reg Word State Flags AluOp Byte MState fetchWindow maxInstrLength pushWord)
open Silmaril.X86.Ext (Mem RM Sz Cond Result retire readRM writeRM readNarrow writeNarrow
  Rex Opc Pfx ModrmPart PResult ByteParser mkReg decodeRM pHead pImm16 pImm32)
open Silmaril.X86.Ext8 (pM optP aluOfDigit)
open Silmaril.Process (Memory)

/-! ## Instructions -/

/-- The forms added by the variant. Immediates are stored sign-extended to the width the
instruction uses them at (`imm8` forms are decoded into the `imm32`/`imm16` constructor). -/
inductive New where
  /-- `imul r, r/m, imm` (`69 /r id`, `6B /r ib`). -/
  | imulI (sz : Sz) (dst : Reg) (src : RM) (imm : BitVec 32)
  /-- `imul r/m` (`F7 /5`): `RDX:RAX := RAX * r/m`, signed. -/
  | imul1 (sz : Sz) (src : RM)
  /-- `bsf r, r/m` (`0F BC /r`). -/
  | bsf (sz : Sz) (dst : Reg) (src : RM)
  /-- `bsr r, r/m` (`0F BD /r`). -/
  | bsr (sz : Sz) (dst : Reg) (src : RM)
  /-- `adc r/m, r` (`11 /r`), or `sbb r/m, r` (`19 /r`) when `sub`. -/
  | adc (sz : Sz) (sub : Bool) (dst : RM) (src : Reg)
  /-- `adc r, r/m` (`13 /r`), or `sbb r, r/m` (`1B /r`) when `sub`. -/
  | adcR (sz : Sz) (sub : Bool) (dst : Reg) (src : RM)
  /-- `adc`/`sbb r/m, imm` (`81 /2 /3 id`, `83 /2 /3 ib`). -/
  | adcI (sz : Sz) (sub : Bool) (dst : RM) (imm : BitVec 32)
  /-- `call r/m64` (`FF /2`). -/
  | callInd (src : RM)
  /-- `jmp r/m64` (`FF /4`). -/
  | jmpInd (src : RM)
  /-- `push imm` (`6A ib`, `68 id`). -/
  | pushI (imm : BitVec 32)
  /-- `op r/m16, r16` (`66 01 09 21 29 31 39 /r`). -/
  | alu16 (op : AluOp) (dst : RM) (src : Reg)
  /-- `op r16, r/m16` (`66 03 0B 23 2B 33 3B /r`). -/
  | alu16R (op : AluOp) (dst : Reg) (src : RM)
  /-- `op r/m16, imm` (`66 81 /d iw`, `66 83 /d ib`). -/
  | alu16I (op : AluOp) (dst : RM) (imm : BitVec 16)
  /-- `op ax, imm16` (`66 05 0D 25 2D 35 3D iw`). -/
  | alu16A (op : AluOp) (imm : BitVec 16)
  /-- `test r/m16, r16` (`66 85 /r`). -/
  | test16 (dst : RM) (src : Reg)
  /-- `test r/m16, imm16` (`66 F7 /0 iw`). -/
  | test16I (dst : RM) (imm : BitVec 16)
  /-- `test ax, imm16` (`66 A9 iw`). -/
  | test16A (imm : BitVec 16)
  /-- `test r/m, imm32` (`F7 /0 id`; sign-extended at 64 bits). -/
  | testI (sz : Sz) (dst : RM) (imm : BitVec 32)
  /-- `test r/m8, imm8` (`F6 /0 ib`) over every byte register (`Ext8.RM8`). -/
  | testI8 (dst : Silmaril.X86.Ext8.RM8) (imm : BitVec 8)
  /-- `bt r, r` (`0F A3 /r`, register destination only). -/
  | bt (sz : Sz) (dst src : Reg)
  /-- `rep ret` (`F3 C3`): `ret`, the `F3` prefix ignored. -/
  | repRet
  deriving DecidableEq, Repr

/-- Instructions of the variant: those of `Ext8`, and the new forms. -/
inductive Instr where
  | ext8 (i : Silmaril.X86.Ext8.Instr)
  | new (i : New)
  deriving DecidableEq, Repr

/-! ## Decoding the new forms -/

/-- The `r/m` operand of a ModRM part (no FS override). -/
def rmOf (rex : Option Rex) (mp : ModrmPart) : RM :=
  let r := rex.getD Rex.zero
  decodeRM false r.x r.b mp.1 mp.2.1 mp.2.2

/-- The register of the ModRM `reg` field. -/
def regOf (rex : Option Rex) (mp : ModrmPart) : Reg :=
  mkReg (rex.getD Rex.zero).r mp.1.reg

/-- A 32-bit immediate from a sign-extended byte. -/
def pIb32 : ByteParser (BitVec 32) := ByteParser.map (fun v => v.signExtend 32) ByteParser.byte

/-- A 16-bit immediate from a sign-extended byte. -/
def pIb16 : ByteParser (BitVec 16) := ByteParser.map (fun v => v.signExtend 16) ByteParser.byte

/-- After a `3E` (`notrack`) prefix: a second head with no FS override, no legacy prefix and
opcode `FF`, then a ModRM with digit `/4`. Only `notrack jmp r/m64` is read; every other form
after `3E` (including `3E FF /2`, a repeated `3E`, `3E 64`, `3E 66`) is rejected. -/
def pNotrack : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = false ∧ h.2.1 = .none ∧ h.2.2.2 = .one 0xFF#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 4#3 then ByteParser.pure (.jmpInd (rmOf h.2.2.1 mp)) else ByteParser.fail
    else ByteParser.fail

/-- The body of a form without a legacy prefix, after REX and opcode. -/
def pBody (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    let sz := Sz.ofW (rex.getD Rex.zero).w
    if b = 0x69#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun v => .imulI sz (regOf rex mp) (rmOf rex mp) v) pImm32
    else if b = 0x6B#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun v => .imulI sz (regOf rex mp) (rmOf rex mp) v) pIb32
    else if b = 0x11#8 ∨ b = 0x19#8 then
      ByteParser.map (fun mp => .adc sz (b = 0x19#8) (rmOf rex mp) (regOf rex mp)) pM
    else if b = 0x13#8 ∨ b = 0x1B#8 then
      ByteParser.map (fun mp => .adcR sz (b = 0x1B#8) (regOf rex mp) (rmOf rex mp)) pM
    else if b = 0x81#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 2#3 ∨ mp.1.reg = 3#3 then
          ByteParser.map (fun v => .adcI sz (mp.1.reg = 3#3) (rmOf rex mp) v) pImm32
        else ByteParser.fail
    else if b = 0x83#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 2#3 ∨ mp.1.reg = 3#3 then
          ByteParser.map (fun v => .adcI sz (mp.1.reg = 3#3) (rmOf rex mp) v) pIb32
        else ByteParser.fail
    else if b = 0xF7#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 5#3 then ByteParser.pure (.imul1 sz (rmOf rex mp))
        else if mp.1.reg = 0#3 then ByteParser.map (fun v => .testI sz (rmOf rex mp) v) pImm32
        else ByteParser.fail
    else if b = 0xF6#8 ∧ (rex.getD Rex.zero).w = false then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 0#3 then
          ByteParser.map (fun v => .testI8 (Silmaril.X86.Ext8.rm8Of rex mp) v) ByteParser.byte
        else ByteParser.fail
    else if b = 0xFF#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 2#3 then ByteParser.pure (.callInd (rmOf rex mp))
        else if mp.1.reg = 4#3 then ByteParser.pure (.jmpInd (rmOf rex mp))
        else ByteParser.fail
    else if b = 0x3E#8 ∧ rex = none then pNotrack
    else if b = 0x6A#8 ∧ rex = none then ByteParser.map .pushI pIb32
    else if b = 0x68#8 ∧ rex = none then ByteParser.map .pushI pImm32
    else ByteParser.fail
  | .two b =>
    let sz := Sz.ofW (rex.getD Rex.zero).w
    if b = 0xBC#8 then ByteParser.map (fun mp => .bsf sz (regOf rex mp) (rmOf rex mp)) pM
    else if b = 0xBD#8 then ByteParser.map (fun mp => .bsr sz (regOf rex mp) (rmOf rex mp)) pM
    else if b = 0xA3#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.mod = 3#2 then
          ByteParser.pure (.bt sz (mkReg (rex.getD Rex.zero).b mp.1.rm) (regOf rex mp))
        else ByteParser.fail
    else ByteParser.fail

/-- The body of a `66`-prefixed (16-bit) form, after REX and opcode. -/
def pBody16 (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    let lo := b.toNat % 8
    let digit : BitVec 3 := BitVec.ofNat 3 (b.toNat / 8)
    if b.toNat < 0x40 ∧ lo = 1 then
      ByteParser.bind (optP (aluOfDigit digit)) fun op =>
        ByteParser.map (fun mp => .alu16 op (rmOf rex mp) (regOf rex mp)) pM
    else if b.toNat < 0x40 ∧ lo = 3 then
      ByteParser.bind (optP (aluOfDigit digit)) fun op =>
        ByteParser.map (fun mp => .alu16R op (regOf rex mp) (rmOf rex mp)) pM
    else if b.toNat < 0x40 ∧ lo = 5 ∧ rex = none then
      ByteParser.bind (optP (aluOfDigit digit)) fun op =>
        ByteParser.map (fun v => .alu16A op v) pImm16
    else if b = 0x81#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (aluOfDigit mp.1.reg)) fun op =>
          ByteParser.map (fun v => .alu16I op (rmOf rex mp) v) pImm16
    else if b = 0x83#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (aluOfDigit mp.1.reg)) fun op =>
          ByteParser.map (fun v => .alu16I op (rmOf rex mp) v) pIb16
    else if b = 0x85#8 then
      ByteParser.map (fun mp => .test16 (rmOf rex mp) (regOf rex mp)) pM
    else if b = 0xF7#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 0#3 then ByteParser.map (fun v => .test16I (rmOf rex mp) v) pImm16
        else ByteParser.fail
    else if b = 0xA9#8 ∧ rex = none then ByteParser.map .test16A pImm16
    else ByteParser.fail
  | .two _ => ByteParser.fail

/-- The parser of a new form: no FS override; no legacy prefix, a single `66` without
REX.W for the 16-bit forms, or `F3` without REX on `C3` (`rep ret`). -/
def pNew : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = true then ByteParser.fail
    else
      match h.2.1 with
      | .none => pBody h.2.2.1 h.2.2.2
      | .opsize =>
        if (h.2.2.1.getD Rex.zero).w = true then ByteParser.fail else pBody16 h.2.2.1 h.2.2.2
      | .rep =>
        if h.2.2.1 = none ∧ h.2.2.2 = .one 0xC3#8 then ByteParser.pure .repRet
        else ByteParser.fail
      | _ => ByteParser.fail

/-- Decode a new form; returns the instruction and the number of bytes consumed. -/
def decodeNew (bytes : List Byte) : Option (New × Nat) :=
  match pNew bytes with
  | .ok i rest => some (i, bytes.length - rest.length)
  | _ => none

/-- The variant's decoder: `Ext8.decode` first, then the new forms. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Silmaril.X86.Ext8.decode bytes with
  | some (i, n) => some (.ext8 i, n)
  | none => (decodeNew bytes).map fun (i, n) => (.new i, n)

/-! ## Semantics of the new forms -/

/-- The flags of BSF/BSR on a nonzero source: ZF clear, the rest undefined. -/
def scanFlags : Flags := ⟨none, none, none, some false, none, none⟩

/-- The index of the highest set bit (for a nonzero `x`). -/
def bsrIndex {n : Nat} (x : BitVec n) : Nat := n - 1 - Silmaril.X86.Ext.lzcntN x

/-- The index of the lowest set bit (for a nonzero `x`). -/
def bsfIndex {n : Nat} (x : BitVec n) : Nat := Silmaril.X86.Ext.tzcntN x

/-- The result of ADC (`sub = false`) or SBB (`sub = true`) with carry-in `c`. -/
def carryResult {n : Nat} (sub : Bool) (x y : BitVec n) (c : Bool) : BitVec n :=
  if sub then x - y - (BitVec.ofBool c).setWidth n
  else x + y + (BitVec.ofBool c).setWidth n

/-- The flags of ADC/SBB (SDM: "The OF, SF, ZF, AF, CF, and PF flags are set according to the
result"). -/
def carryFlags {n : Nat} (sub : Bool) (x y : BitVec n) (c : Bool) : Flags :=
  let r := carryResult sub x y c
  { carry := some (if sub then decide (x.toNat < y.toNat + c.toNat)
      else decide (2 ^ n ≤ x.toNat + y.toNat + c.toNat))
    parity := some (Silmaril.X86.Ext.parityN r)
    adjust := some ((x ^^^ y ^^^ r).getLsbD 4)
    zero := some (Silmaril.X86.Ext.isZeroN r)
    sign := some r.msb
    overflow := some (if sub then ((x ^^^ y) &&& (x ^^^ r)).msb
      else ((x ^^^ r) &&& (y ^^^ r)).msb) }

/-- An ADC/SBB step with destination `dst` and second operand `y`. -/
def carryStep (sz : Sz) (sub : Bool) (dst : RM) (y : BitVec sz.bits) (s : State)
    (memory : Memory) (next : Word) : Result :=
  match readRM sz dst s memory next with
  | none => .dataFault
  | some x =>
    match s.flags.carry with
    | none => .undefinedCondition .b
    | some c =>
      retire next ((writeRM sz dst (carryResult sub x y c) s memory next).map fun r =>
        ({ r.1 with flags := carryFlags sub x y c }, r.2))

/-- The signed double-width product of IMUL (one operand): low and high halves. -/
def imulWide {n : Nat} (x y : BitVec n) : BitVec n × BitVec n :=
  let p : BitVec (n + n) := x.signExtend (n + n) * y.signExtend (n + n)
  (p.setWidth n, p.extractLsb' n n)

/-- The flags of IMUL (one operand): CF = OF = the high half is not the sign extension of
the low half; the rest undefined. -/
def imul1Flags {n : Nat} (x y : BitVec n) : Flags :=
  let p := imulWide x y
  let v := decide (p.2 ≠ (if p.1.msb then BitVec.allOnes n else 0#n))
  ⟨some v, none, none, none, none, some v⟩

/-- A 16-bit two-operand ALU step. CMP writes nothing. -/
def alu16 (op : AluOp) (dst : RM) (y : BitVec 16) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readNarrow .w dst s memory next with
  | none => none
  | some x =>
    if op = .cmp then some ({ s with flags := Silmaril.X86.Ext.AluOp.flagsN op x y }, memory)
    else (writeNarrow .w dst (Silmaril.X86.Ext.AluOp.resultN op x y) s memory next).map fun r =>
      ({ r.1 with flags := Silmaril.X86.Ext.AluOp.flagsN op x y }, r.2)

/-- A 16-bit TEST step. -/
def test16 (dst : RM) (y : BitVec 16) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  (readNarrow .w dst s memory next).map fun x =>
    ({ s with flags := Silmaril.X86.Ext.logicFlagsN (x &&& y) }, memory)

/-- Execute a new form, given the address of the next instruction. -/
def execNew (i : New) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .imulI sz dst src imm =>
    retire next ((readRM sz src s memory next).map fun x =>
      ({ sz.write s dst (x * imm.signExtend sz.bits) with
          flags := Silmaril.X86.Ext.imulFlags x (imm.signExtend sz.bits) }, memory))
  | .imul1 sz src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some y =>
      let x := sz.read s .rax
      let p := imulWide x y
      retire next (some ({ sz.write (sz.write s .rax p.1) .rdx p.2 with
        flags := imul1Flags x y }, memory))
  | .bsf sz dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some x =>
      if x = 0#sz.bits then .undefinedCondition .e
      else retire next (some ({ sz.write s dst (BitVec.ofNat sz.bits (bsfIndex x)) with
        flags := scanFlags }, memory))
  | .bsr sz dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some x =>
      if x = 0#sz.bits then .undefinedCondition .e
      else retire next (some ({ sz.write s dst (BitVec.ofNat sz.bits (bsrIndex x)) with
        flags := scanFlags }, memory))
  | .adc sz sub dst src => carryStep sz sub dst (sz.read s src) s memory next
  | .adcR sz sub dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some y => carryStep sz sub (.reg dst) y s memory next
  | .adcI sz sub dst imm => carryStep sz sub dst (imm.signExtend sz.bits) s memory next
  | .callInd src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some v =>
      match pushWord s memory next with
      | none => .dataFault
      | some (t, m) => .ok { t with rip := v } m
  | .jmpInd src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some v => .ok { s with rip := v } memory
  | .pushI imm => retire next (pushWord s memory (imm.signExtend 64))
  | .alu16 op dst src => retire next (alu16 op dst ((s.read src).setWidth 16) s memory next)
  | .alu16R op dst src =>
    match readNarrow .w src s memory next with
    | none => .dataFault
    | some y => retire next (alu16 op (.reg dst) y s memory next)
  | .alu16I op dst imm => retire next (alu16 op dst imm s memory next)
  | .alu16A op imm => retire next (alu16 op (.reg .rax) imm s memory next)
  | .test16 dst src => retire next (test16 dst ((s.read src).setWidth 16) s memory next)
  | .test16I dst imm => retire next (test16 dst imm s memory next)
  | .test16A imm => retire next (test16 (.reg .rax) imm s memory next)
  | .testI sz dst imm =>
    retire next ((readRM sz dst s memory next).map fun x =>
      ({ s with flags := Silmaril.X86.Ext.logicFlagsN (x &&& imm.signExtend sz.bits) }, memory))
  | .testI8 dst imm =>
    retire next ((dst.read s memory next).map fun x =>
      ({ s with flags := Silmaril.X86.Ext.logicFlagsN (x &&& imm) }, memory))
  | .bt sz dst src =>
    let bit := (sz.read s dst).getLsbD ((sz.read s src).toNat % sz.bits)
    retire next (some ({ s with flags := { s.flags with
      carry := some bit, zero := none, overflow := none, sign := none, adjust := none,
      parity := none } },
      memory))
  | .repRet => Silmaril.X86.Ext.exec .ret s memory 2

/-- Execute a variant instruction with its consumed byte length. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .ext8 i => Silmaril.X86.Ext8.exec i s memory length
  | .new i => execNew i s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Fetch and step -/

/-- Fetch a new form at an address: the bytes are not an `Ext8` form, `decodeNew` reads
the fetch window, and the bytes it consumed are executable. `none` if not decodable as a new
form; `some none` if decodable but not fetchable. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (New × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- The outcome of one variant step. -/
inductive Outcome where
  | ext8 (o : Silmaril.X86.Ext8.Outcome)
  /-- A new form retired. -/
  | retired (next : MState)
  /-- A new form faulted on data, depended on an undefined flag or value. -/
  | newFault (r : Result)

/-- Fetch, decode and execute one instruction: `Ext8.step`, and on bytes `Ext8` cannot
decode, the new forms. -/
def step (exit : Word) (m : MState) : Outcome :=
  match Silmaril.X86.Ext8.step exit m with
  | .ext .undecodable =>
    match fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      match execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n) with
      | .ok core memory => .retired ⟨core, memory⟩
      | r => .newFault r
    | some none => .ext8 (.ext .fetchFault)
    | none => .ext8 (.ext .undecodable)
  | o => .ext8 o

/-- Retirement only. -/
def stepOpt (exit : Word) (m : MState) : Option MState :=
  match step exit m with
  | .ext8 (.ext (.retired next)) => some next
  | .ext8 (.retired next) => some next
  | .retired next => some next
  | _ => none

/-- A run to the return to `exit`. -/
def Returns (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Silmaril.Machine.Execution.run (stepOpt exit) n initial = some mid ∧
    step exit mid = .ext8 (.ext (.returned final))

end Silmaril.Machine.X86.Ext9
