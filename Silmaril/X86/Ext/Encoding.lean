module

public import Silmaril.X86.Ext.Raw

/-!
# Canonical byte encoding of the extended x86-64 model

`toRaw` gives each `Ext.Instr` its raw fields (`Raw.lean`) and `encode` their
bytes. The encodings follow the Intel SDM opcode tables:

| Instruction | Bytes |
| --- | --- |
| `mov r/m, reg` | `REX? 89 /r` |
| `mov r/m, imm32` | `REX? C7 /0 id` |
| `mov r64, imm64` | `REX.W B8+r io` |
| `mov reg, m` | `REX? 8B /r` |
| `mov m8, r8` / `mov m16, r16` | `REX? 88 /r` / `66 REX? 89 /r` |
| `movzx`/`movsx reg, r/m8`/`r/m16` | `REX? 0F B6/B7/BE/BF /r` |
| `movsxd r64, r/m32` | `REX.W 63 /r` |
| `lea r32/r64, m` | `8D /r`, `REX.W 8D /r` |
| `op r/m, reg` | `REX? 01/09/21/29/31/39 /r` |
| `op reg, r/m` | `REX? 03/0B/23/2B/33/3B /r` |
| `op r/m, imm32` | `REX? 81 /digit id` |
| `op r/m, imm8` | `REX? 83 /digit ib` |
| `test r/m, reg` | `REX? 85 /r` |
| `test r/m8, r8` | `REX? 84 /r` (REX required for SPL/BPL/SIL/DIL) |
| `cmp r/m8, imm8`; `cmp al, imm8` | `REX? 80 /7 ib`; `3C ib` |
| `not`/`neg`/`div`/`idiv r/m` | `REX? F7 /2 /3 /6 /7` |
| `imul reg, r/m` | `REX? 0F AF /r` |
| shift/rotate by CL / imm8 | `REX? D3 /digit`, `REX? C1 /digit ib` (ROL 0, ROR 1, SHL 4, SHR 5, SAR 7) |
| `cdq` / `cqo` | `99` / `REX.W 99` |
| `cwde` / `cdqe` | `98` / `REX.W 98` |
| `setcc r/m8` | `REX? 0F 90+cc /0` |
| `jmp rel32` / `jcc rel32` | `E9 cd` / `0F 80+cc cd` |
| `call rel32` / `ret` | `E8 cd` / `C3` |
| `push r64` / `pop r64` | `REX.B? 50+r` / `REX.B? 58+r` |
| `ud2` | `0F 0B` |
| `lzcnt`/`tzcnt`/`popcnt reg, r/m` | `F3 REX? 0F BD/BC/B8 /r` |

REX.W is set exactly for 64-bit operand size, and a REX prefix is emitted
exactly when one of W, R, X, B is set or a byte-register field names SPL, BPL,
SIL or DIL (`mkRex`). Memory operands with a base register (`encodeMem`) use
`mod = 00` without displacement when the displacement is zero and the base is
not RBP or R13, a disp8 when the displacement fits in a signed byte, and a
disp32 otherwise. A SIB byte is emitted when there is an index or the base is
RSP or R12; with no index its index field is `100` and its scale `00`. RBP and
R13 as a base with a zero displacement use `mod = 01` with a zero disp8, because
`mod = 00` with that base field means RIP-relative (without SIB) or base-less
(with SIB). These are the choices made by the GNU and LLVM assemblers for these
instruction forms; `Examples.lean` checks representative encodings byte for
byte.

The two base-free shapes have exactly one encoding each, so they are canonical
by construction: `[rip + disp32]` is `mod = 00, r/m = 101` with a disp32 and no
SIB byte, and `[index * 2^scale + disp32]` and `[disp32]` are `mod = 00,
r/m = 100` with a SIB byte whose `base` field is `101` and a disp32. Neither
reads REX.B (and `[rip + disp32]` does not read REX.X either), so the encoder
clears those bits and a set bit makes the bytes non-canonical. Because a base
register whose low field is `101` never uses `mod = 00`, and a SIB `base` field
of `101` with `mod = 00` is never produced for a base register, the three
shapes do not collide.

`decode` runs the length decoder `parseRaw`, gives the fields their meaning with
`ofRaw`, and then accepts only if the input begins with the canonical
encoding of the result. It therefore accepts exactly the canonical encodings
(`decode_eq_some_iff`); other valid encodings of the same instruction, for
example a redundant REX prefix, the `8B` form of a register move, the `83` imm8
forms, or a disp32 that would fit in a disp8, are rejected. `none` means
"outside this canonical subset", not "invalid on hardware".

`Raw.Canonical` names the raw fields the decoder accepts, and
`decode_eq_some_iff_canonical` is the completeness statement: `decode` succeeds
exactly on byte strings whose length-decoded raw fields have a meaning and are
the canonical encoding of it. `canonical_opcode` lists, as an explicit table,
the prefix/opcode combinations that can be canonical.

`encode_ofInstr` and `encode_ofInsn` prove that the embedded subsets keep their
bytes, and `decode_ofInsn_iff` that decoding agrees on them.
The proofs are about this handwritten codec only; they do not show agreement
with the Sail, ACL2 or hardware decoders.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Byte Reg Word AluOp imm32Bytes)

/-! ## Operand encoding -/

/-- The fields contributed by an `r/m` operand: REX.X, REX.B, ModRM `mod` and
`r/m`, the SIB byte and the displacement. -/
structure EncRM where
  x : Bool
  b : Bool
  mod : BitVec 2
  rm : BitVec 3
  sib : Option SIB
  disp : Disp

/-- A displacement fits in a sign-extended byte. -/
def fits8 (d : BitVec 32) : Bool := (d.setWidth 8).signExtend 32 == d

/-- `mod` and displacement: none for a zero displacement (unless the base field
is `101`), disp8 if it fits, disp32 otherwise. -/
def dispChoice (base : Reg) (d : BitVec 32) : BitVec 2 × Disp :=
  if d = 0#32 ∧ base.lo ≠ 5#3 then (0#2, .none)
  else if fits8 d then (1#2, .d8 (d.setWidth 8))
  else (2#2, .d32 d)

def encodeMem (m : Mem) : EncRM :=
  match m.base with
  | .rip => ⟨false, false, 0#2, 5#3, Option.none, .d32 m.disp⟩
  | .none =>
    match m.index with
    | Option.none => ⟨false, false, 0#2, 4#3, some ⟨0#2, 4#3, 5#3⟩, .d32 m.disp⟩
    | some i => ⟨hiBit i.reg, false, 0#2, 4#3, some ⟨i.scale, i.reg.lo, 5#3⟩, .d32 m.disp⟩
  -- `fs:` is the base-less form under a `64` prefix, so the ModRM, SIB and
  -- displacement bytes are exactly those of `.none`; the override is carried by
  -- `Raw.fs` (see `rmRaw`), which is what distinguishes the two.
  | .fs =>
    match m.index with
    | Option.none => ⟨false, false, 0#2, 4#3, some ⟨0#2, 4#3, 5#3⟩, .d32 m.disp⟩
    | some i => ⟨hiBit i.reg, false, 0#2, 4#3, some ⟨i.scale, i.reg.lo, 5#3⟩, .d32 m.disp⟩
  | .reg base =>
    match m.index with
    | Option.none =>
      if base.lo = 4#3 then
        ⟨false, hiBit base, (dispChoice base m.disp).1, 4#3, some ⟨0#2, 4#3, 4#3⟩,
          (dispChoice base m.disp).2⟩
      else
        ⟨false, hiBit base, (dispChoice base m.disp).1, base.lo, Option.none,
          (dispChoice base m.disp).2⟩
    | some i =>
      ⟨hiBit i.reg, hiBit base, (dispChoice base m.disp).1, 4#3,
        some ⟨i.scale, i.reg.lo, base.lo⟩, (dispChoice base m.disp).2⟩

def encodeRM : RM → EncRM
  | .reg r => ⟨false, hiBit r, 3#2, r.lo, none, .none⟩
  | .mem m => encodeMem m

/-- Whether an `r/m` operand carries the FS segment override. Only a memory
operand based on `Base.fs` does, so `rmRaw` can read the `64` prefix off its
operand and every `toRaw` equation stays as it was. -/
def RM.isFs : RM → Bool
  | .reg _ => false
  | .mem m => match m.base with | .fs => true | _ => false

@[simp] theorem RM.isFs_reg (r : Reg) : RM.isFs (.reg r) = false := rfl

@[simp] theorem RM.isFs_ofRip (d : BitVec 32) : (RM.mem (Mem.ofRip d)).isFs = false := rfl

@[simp] theorem RM.isFs_ofReg (b : Reg) (i : Option Index) (d : BitVec 32) :
    (RM.mem (Mem.ofReg b i d)).isFs = false := rfl

@[simp] theorem RM.isFs_ofFs (i : Option Index) (d : BitVec 32) :
    (RM.mem (Mem.ofFs i d)).isFs = true := rfl

/-- The sign-extended displacement value. -/
def Disp.value : Disp → BitVec 32
  | .none => 0#32
  | .d8 v => v.signExtend 32
  | .d32 v => v

theorem mkReg_eq_rsp_iff (x : Bool) (l : BitVec 3) : mkReg x l = .rsp ↔ x = false ∧ l = 4#3 := by
  revert x l; decide

def decodeIndex (x : Bool) (s : SIB) : Option Index :=
  if h : x = false ∧ s.index = 4#3 then none
  else some ⟨mkReg x s.index, s.scale, fun e => h ((mkReg_eq_rsp_iff _ _).mp e)⟩

/-- The memory operand of a ModRM/SIB/displacement triple with `mod ≠ 11`.
`mod = 00, r/m = 101` without a SIB byte is RIP-relative, and a SIB `base`
field of `101` with `mod = 00` has no base register. -/
def decodeMem (fs x b : Bool) (m : ModRM) (sib : Option SIB) (d : Disp) : Mem :=
  match sib with
  | Option.none =>
    if m.mod = 0#2 ∧ m.rm = 5#3 then ⟨.rip, Option.none, d.value, fun _ => rfl⟩
    else ⟨.reg (mkReg b m.rm), Option.none, d.value, by simp⟩
  | some t =>
    if m.mod = 0#2 ∧ t.base = 5#3 then
      ⟨if fs then .fs else .none, decodeIndex x t, d.value, by cases fs <;> simp⟩
    else ⟨.reg (mkReg b t.base), decodeIndex x t, d.value, by simp⟩

def decodeRM (fs x b : Bool) (m : ModRM) (sib : Option SIB) (d : Disp) : RM :=
  if m.mod = 3#2 then .reg (mkReg b m.rm) else .mem (decodeMem fs x b m sib d)

theorem mkReg_hiBit_of_lo {r : Reg} {l : BitVec 3} (h : r.lo = l) : mkReg (hiBit r) l = r := by
  rw [← h, mkReg_hiBit_lo]

theorem hiBit_lo_eq_rsp (r : Reg) : (hiBit r = false ∧ r.lo = 4#3) ↔ r = .rsp := by
  cases r <;> decide

private theorem dispChoice_cases (base : Reg) (d : BitVec 32) :
    (dispChoice base d = (0#2, .none) ∧ d = 0#32 ∧ base.lo ≠ 5#3) ∨
    (dispChoice base d = (1#2, .d8 (d.setWidth 8)) ∧ (d.setWidth 8).signExtend 32 = d) ∨
    (dispChoice base d = (2#2, .d32 d)) := by
  unfold dispChoice fits8
  split_ifs with h1 h2
  · exact .inl ⟨rfl, h1⟩
  · exact .inr (.inl ⟨rfl, by simpa using h2⟩)
  · exact .inr (.inr rfl)

/-- Decoding the fields of an encoded operand recovers it, for any ModRM `reg`
field. -/
theorem decodeRM_encodeRM (op : RM) (reg : BitVec 3) :
    decodeRM op.isFs (encodeRM op).x (encodeRM op).b ⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩
      (encodeRM op).sib (encodeRM op).disp = op := by
  cases op with
  | reg r => simp [encodeRM, decodeRM]
  | mem m =>
    obtain ⟨base, index, disp, hwf⟩ := m
    cases base with
    | rip =>
      obtain rfl : index = Option.none := hwf rfl
      simp [encodeRM, encodeMem, decodeRM, decodeMem, Disp.value]
    | none =>
      cases index <;>
        simp [encodeRM, encodeMem, decodeRM, decodeMem, decodeIndex, Disp.value,
          hiBit_lo_eq_rsp, Index.ne_rsp, RM.isFs]
    | fs =>
      cases index <;>
        simp [encodeRM, encodeMem, decodeRM, decodeMem, decodeIndex, Disp.value,
          hiBit_lo_eq_rsp, Index.ne_rsp, RM.isFs]
    | reg base =>
      rcases dispChoice_cases base disp with ⟨hc, rfl, h5⟩ | ⟨hc, hfit⟩ | hc <;>
      cases index <;>
      simp only [encodeRM, encodeMem, hc] <;>
      (try split_ifs) <;>
      simp_all [decodeRM, decodeMem, decodeIndex, Disp.value, hiBit_lo_eq_rsp, mkReg_hiBit_of_lo,
        Index.ne_rsp]

/-- The SIB byte and displacement of an encoded operand are those its ModRM
byte announces. -/
theorem encodeRM_ok (op : RM) (reg : BitVec 3) :
    ModrmOk true (some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩, (encodeRM op).sib,
      (encodeRM op).disp)) := by
  cases op with
  | reg r => simp [encodeRM, ModrmOk, needsSib, dispKind, Disp.kind]
  | mem m =>
    obtain ⟨base, index, disp, hwf⟩ := m
    cases base with
    | rip => simp [encodeRM, encodeMem, ModrmOk, needsSib, dispKind, Disp.kind]
    | none => cases index <;> simp [encodeRM, encodeMem, ModrmOk, needsSib, dispKind, Disp.kind]
    | fs => cases index <;> simp [encodeRM, encodeMem, ModrmOk, needsSib, dispKind, Disp.kind]
    | reg base =>
      rcases dispChoice_cases base disp with ⟨hc, rfl, h5⟩ | ⟨hc, hfit⟩ | hc <;>
      cases index <;>
      simp only [encodeRM, encodeMem, hc] <;>
      (try split_ifs) <;>
      simp_all [ModrmOk, needsSib, dispKind, Disp.kind]

theorem encodeRM_disp_length (op : RM) : (encodeRM op).disp.bytes.length ≤ 4 := by
  cases op with
  | reg r => simp [encodeRM, Disp.bytes]
  | mem m =>
    obtain ⟨base, index, disp, hwf⟩ := m
    cases base with
    | rip => simp [encodeRM, encodeMem, Disp.bytes, imm32Bytes]
    | none => cases index <;> simp [encodeRM, encodeMem, Disp.bytes, imm32Bytes]
    | fs => cases index <;> simp [encodeRM, encodeMem, Disp.bytes, imm32Bytes]
    | reg base =>
      rcases dispChoice_cases base disp with ⟨hc, -, -⟩ | ⟨hc, -⟩ | hc <;>
      cases index <;>
      simp only [encodeRM, encodeMem, hc] <;>
      (try split_ifs) <;>
      simp [Disp.bytes, imm32Bytes]

theorem encodeRM_sib_length (op : RM) : (sibBytes (encodeRM op).sib).length ≤ 1 := by
  cases op with
  | reg r => simp [encodeRM, sibBytes]
  | mem m =>
    obtain ⟨base, index, disp, hwf⟩ := m
    cases base <;> cases index <;> simp only [encodeRM, encodeMem] <;> (try split_ifs) <;>
      simp [sibBytes]

/-! ## Opcode fields -/

/-- The `OP r64, r/m64` opcode: the direction-1 form of `AluOp.opcode`. -/
def aluOpcodeR : AluOp → Byte
  | .add => 0x03 | .or => 0x0B | .and => 0x23 | .sub => 0x2B | .xor => 0x33 | .cmp => 0x3B

def aluOfOpcodeR (b : Byte) : Option AluOp :=
  if b = 0x03 then some .add else if b = 0x0B then some .or
  else if b = 0x23 then some .and else if b = 0x2B then some .sub
  else if b = 0x33 then some .xor else if b = 0x3B then some .cmp else none

@[simp] theorem aluOfOpcodeR_aluOpcodeR (op : AluOp) : aluOfOpcodeR (aluOpcodeR op) = some op := by
  cases op <;> decide

/-- The direction-0 and direction-1 ALU opcodes are disjoint. -/
theorem aluOfOpcode_aluOpcodeR (op : AluOp) : AluOp.ofOpcode (aluOpcodeR op) = none := by
  cases op <;> decide

/-- The `OP eAX/rAX, imm32` opcode (the accumulator form). -/
def aluOpcodeA : AluOp → Byte
  | .add => 0x05 | .or => 0x0D | .and => 0x25 | .sub => 0x2D | .xor => 0x35 | .cmp => 0x3D

def aluOfOpcodeA (b : Byte) : Option AluOp :=
  if b = 0x05 then some .add else if b = 0x0D then some .or
  else if b = 0x25 then some .and else if b = 0x2D then some .sub
  else if b = 0x35 then some .xor else if b = 0x3D then some .cmp else none

@[simp] theorem aluOfOpcodeA_aluOpcodeA (op : AluOp) : aluOfOpcodeA (aluOpcodeA op) = some op := by
  cases op <;> decide

def UnOp.digit : UnOp → BitVec 3
  | .not => 2 | .neg => 3

def ShiftOp.digit : ShiftOp → BitVec 3
  | .rol => 0 | .ror => 1 | .shl => 4 | .shr => 5 | .sar => 7

def ShiftOp.ofDigit (d : BitVec 3) : Option ShiftOp :=
  if d = 0#3 then some .rol else if d = 1#3 then some .ror else if d = 4#3 then some .shl
  else if d = 5#3 then some .shr else if d = 7#3 then some .sar else none

@[simp] theorem ShiftOp.ofDigit_digit (op : ShiftOp) : ShiftOp.ofDigit op.digit = some op := by
  cases op <;> decide

/-- The second opcode byte of LZCNT/TZCNT/POPCNT (after `F3 0F`). -/
def BitCountOp.opcode : BitCountOp → Byte
  | .lzcnt => 0xBD | .tzcnt => 0xBC | .popcnt => 0xB8

/-- The second opcode byte of MOVZX/MOVSX. -/
def movxOpcode (sx : Bool) (n : Narrow) : Byte :=
  match sx, n with
  | false, .b => 0xB6 | false, .w => 0xB7 | true, .b => 0xBE | true, .w => 0xBF

/-- The byte-register operand needs a REX prefix. -/
def RM.needsRexByte : RM → Bool
  | .reg r => Ext.needsRexByte r
  | .mem _ => false

def RM.mem? : RM → Option Mem
  | .reg _ => none
  | .mem m => some m

/-! ## Raw fields of an instruction -/

/-- An instruction with a ModRM operand. -/
def rmRaw (pfx : Pfx) (w : Bool) (opc : Opc) (reg : BitVec 3) (rHi : Bool) (op : RM)
    (force : Bool) (imm : Imm) : Raw :=
  ⟨op.isFs, pfx, mkRex w rHi (encodeRM op).x (encodeRM op).b force, opc,
    some (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩, (encodeRM op).sib, (encodeRM op).disp), imm⟩

/-- The ModRM parts of the `0F 1F` NOP forms. The assemblers reach a target
length by widening the displacement, so these are *not* the shortest encoding
of their operand; `encodeMem` would never produce them. -/
def nopM0 : ModrmPart := (⟨0#2, 0#3, 0#3⟩, Option.none, .none)
def nopM1 : ModrmPart := (⟨1#2, 0#3, 0#3⟩, Option.none, .d8 0)
def nopM2 : ModrmPart := (⟨1#2, 0#3, 4#3⟩, some ⟨0#2, 0#3, 0#3⟩, .d8 0)
def nopM3 : ModrmPart := (⟨2#2, 0#3, 0#3⟩, Option.none, .d32 0)
def nopM4 : ModrmPart := (⟨2#2, 0#3, 4#3⟩, some ⟨0#2, 0#3, 0#3⟩, .d32 0)

/-- A `0F 1F /0` NOP with the given legacy prefix and ModRM part. -/
def nop1FRaw (p : Pfx) (mp : ModrmPart) : Raw :=
  ⟨false, p, Option.none, .two 0x1F, some mp, .none⟩

/-- The canonical NOP of `len + 1` bytes: `90`, `66 90`, `0F 1F 00`,
`0F 1F 40 00`, `0F 1F 44 00 00`, `66 0F 1F 44 00 00`, `0F 1F 80 00000000`,
`0F 1F 84 00 00000000`, `66 0F 1F 84 00 00000000`, and then that last form with
one to six `66` prefixes and a `2E` in front. -/
def nopRaw (len : Fin 15) : Raw :=
  match len.val with
  | 0 => ⟨false, .none, Option.none, .one 0x90, Option.none, .none⟩
  | 1 => ⟨false, .opsize, Option.none, .one 0x90, Option.none, .none⟩
  | 2 => nop1FRaw .none nopM0
  | 3 => nop1FRaw .none nopM1
  | 4 => nop1FRaw .none nopM2
  | 5 => nop1FRaw .opsize nopM2
  | 6 => nop1FRaw .none nopM3
  | 7 => nop1FRaw .none nopM4
  | 8 => nop1FRaw .opsize nopM4
  | 9 => nop1FRaw (.nopPad 0) nopM4
  | 10 => nop1FRaw (.nopPad 1) nopM4
  | 11 => nop1FRaw (.nopPad 2) nopM4
  | 12 => nop1FRaw (.nopPad 3) nopM4
  | 13 => nop1FRaw (.nopPad 4) nopM4
  | _ => nop1FRaw (.nopPad 5) nopM4

/-- The length of the `0F 1F` NOP with this prefix and ModRM part, if it is one
of the canonical forms. -/
def nop1FIndex (p : Pfx) (mp : ModrmPart) : Option (Fin 15) :=
  (List.finRange 15).find? fun i => nopRaw i == nop1FRaw p mp

/-- An instruction without a ModRM byte; `bHi` is REX.B. -/
def plainRaw (w bHi : Bool) (opc : Opc) (imm : Imm) : Raw :=
  ⟨false, .none, mkRex w false false bHi false, opc, none, imm⟩

def toRaw : Instr → Raw
  | .mov sz dst src => rmRaw .none sz.w (.one 0x89) src.lo (hiBit src) dst false .none
  | .movI sz dst imm => rmRaw .none sz.w (.one 0xC7) 0 false dst false (.i32 imm)
  | .movI16 dst imm => rmRaw .opsize false (.one 0xC7) 0 false dst false (.i16 imm)
  | .mov8 dst src =>
    rmRaw .none false (.one 0x8A) dst.lo (hiBit dst) src
      (needsRexByte dst || src.needsRexByte) .none
  | .movI8 dst imm => rmRaw .none false (.one 0xC6) 0 false dst dst.needsRexByte (.i8 imm)
  | .movI32 dst imm => plainRaw false (hiBit dst) (.one (0b10111#5 ++ dst.lo)) (.i32 imm)
  | .movabs dst imm => plainRaw true (hiBit dst) (.one (0b10111#5 ++ dst.lo)) (.i64 imm)
  | .load sz dst src => rmRaw .none sz.w (.one 0x8B) dst.lo (hiBit dst) (.mem src) false .none
  | .store .b dst src =>
    rmRaw .none false (.one 0x88) src.lo (hiBit src) dst
      (needsRexByte src || dst.needsRexByte) .none
  | .store .w dst src => rmRaw .opsize false (.one 0x89) src.lo (hiBit src) dst false .none
  | .movx sx sz n dst src =>
    rmRaw .none sz.w (.two (movxOpcode sx n)) dst.lo (hiBit dst) src
      (n = .b && src.needsRexByte) .none
  | .movsxd dst src => rmRaw .none true (.one 0x63) dst.lo (hiBit dst) src false .none
  | .lea sz dst src => rmRaw .none sz.w (.one 0x8D) dst.lo (hiBit dst) (.mem src) false .none
  | .alu sz op dst src => rmRaw .none sz.w (.one op.opcode) src.lo (hiBit src) dst false .none
  | .aluR sz op dst src =>
    rmRaw .none sz.w (.one (aluOpcodeR op)) dst.lo (hiBit dst) src false .none
  | .aluI sz op dst imm => rmRaw .none sz.w (.one 0x81) op.digit false dst false (.i32 imm)
  | .aluI8 sz op dst imm => rmRaw .none sz.w (.one 0x83) op.digit false dst false (.i8 imm)
  | .aluA sz op imm => plainRaw sz.w false (.one (aluOpcodeA op)) (.i32 imm)
  | .test sz dst src => rmRaw .none sz.w (.one 0x85) src.lo (hiBit src) dst false .none
  | .test8 dst src =>
    rmRaw .none false (.one 0x84) src.lo (hiBit src) dst
      (needsRexByte src || dst.needsRexByte) .none
  | .testI8 dst imm => rmRaw .none false (.one 0xF6) 0 false dst dst.needsRexByte (.i8 imm)
  | .testA8 imm => plainRaw false false (.one 0xA8) (.i8 imm)
  | .cmpI8 dst imm => rmRaw .none false (.one 0x80) 7 false dst dst.needsRexByte (.i8 imm)
  | .cmpA8 imm => plainRaw false false (.one 0x3C) (.i8 imm)
  | .testA sz imm => plainRaw sz.w false (.one 0xA9) (.i32 imm)
  | .incdec sz dec dst =>
    rmRaw .none sz.w (.one 0xFF) (if dec then 1 else 0) false dst false .none
  | .pushRM src => rmRaw .none false (.one 0xFF) 6 false src false .none
  | .bswap sz dst => plainRaw sz.w (hiBit dst) (.two (0b11001#5 ++ dst.lo)) .none
  | .unary sz op dst => rmRaw .none sz.w (.one 0xF7) op.digit false dst false .none
  | .imul sz dst src => rmRaw .none sz.w (.two 0xAF) dst.lo (hiBit dst) src false .none
  | .mul sz src => rmRaw .none sz.w (.one 0xF7) 4 false src false .none
  | .shift sz op dst .cl => rmRaw .none sz.w (.one 0xD3) op.digit false dst false .none
  | .shift sz op dst .one => rmRaw .none sz.w (.one 0xD1) op.digit false dst false .none
  | .shift sz op dst (.imm n) => rmRaw .none sz.w (.one 0xC1) op.digit false dst false (.i8 n)
  | .cxd sz => plainRaw sz.w false (.one 0x99) .none
  | .cxe sz => plainRaw sz.w false (.one 0x98) .none
  | .div sz signed src =>
    rmRaw .none sz.w (.one 0xF7) (if signed then 7 else 6) false src false .none
  | .cmov sz c dst src =>
    rmRaw .none sz.w (.two (4#4 ++ c.code)) dst.lo (hiBit dst) src false .none
  | .setcc c dst => rmRaw .none false (.two (9#4 ++ c.code)) 0 false dst dst.needsRexByte .none
  | .jmp rel => plainRaw false false (.one 0xE9) (.i32 rel)
  | .jmp8 rel => plainRaw false false (.one 0xEB) (.i8 rel)
  | .jcc c rel => plainRaw false false (.two (8#4 ++ c.code)) (.i32 rel)
  | .jcc8 c rel => plainRaw false false (.one (7#4 ++ c.code)) (.i8 rel)
  | .call rel => plainRaw false false (.one 0xE8) (.i32 rel)
  | .ret => plainRaw false false (.one 0xC3) .none
  | .leave => plainRaw false false (.one 0xC9) .none
  | .endbr64 =>
    ⟨false, .rep, Option.none, .two 0x1E, some (⟨3#2, 7#3, 2#3⟩, Option.none, .none), .none⟩
  | .push r => plainRaw false (hiBit r) (.one (0b01010#5 ++ r.lo)) .none
  | .pop r => plainRaw false (hiBit r) (.one (0b01011#5 ++ r.lo)) .none
  | .ud2 => plainRaw false false (.two 0x0B) .none
  | .nop len => nopRaw len
  | .bitcount op sz dst src =>
    rmRaw .rep sz.w (.two op.opcode) dst.lo (hiBit dst) src false .none

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-! ## RIP-relative encodings as a function of the displacement

A RIP-relative operand carries the displacement a relocation writes, so the
bytes of such an instruction depend on where the section lands. Every closed
`decide` is therefore out of reach for them, and reduction does not help
either: the ModRM byte is assembled with `BitVec` append, whose `Nat.lor` does
not unfold, so `rfl` cannot see through it with the displacement symbolic.

The way out is to split the byte string once and for all. `encodeMem` for a
`.rip` base does not branch on the displacement -- unlike a register base, where
`dispChoice` picks between no displacement, a disp8 and a disp32 -- so the
encoding is *uniformly* some fixed bytes, then the four bytes of the
displacement, then the immediate. `rmRaw_bytes_rip` states that, and
`rmRaw_bytes_rip_congr` is the consequence a relocation argument needs:
**changing the displacement changes exactly those four bytes and nothing else.**

This holds for every ModRM form, so it serves `lea`, `load`, `mov`, the ALU
forms and the rest alike; `encode_lea_rip` and `encode_load_rip` are the two
spelled out, being the ones the pilot images use. To use them with a concrete
register, instantiate and then discharge the fixed head by `decide`, which is
closed and settles instantly -- see `Examples.lean`. -/

/-- A RIP-relative operand fixes every encoder field except the displacement:
`mod = 00`, `r/m = 101`, no SIB byte, no REX.X or REX.B, and a disp32. -/
theorem encodeMem_rip {m : Mem} (h : m.base = .rip) :
    encodeMem m = ⟨false, false, 0#2, 5#3, Option.none, .d32 m.disp⟩ := by
  obtain ⟨base, index, disp, hwf⟩ := m
  cases h
  rfl

@[simp] theorem encodeMem_ofRip (d : BitVec 32) :
    encodeMem (Mem.ofRip d) = ⟨false, false, 0#2, 5#3, Option.none, .d32 d⟩ :=
  encodeMem_rip rfl

/-- **The bytes of any ModRM instruction with a RIP-relative operand**, split at
the displacement: a fixed head that does not mention it, its four little-endian
bytes, then the immediate. -/
theorem rmRaw_bytes_rip (pfx : Pfx) (w : Bool) (opc : Opc) (reg : BitVec 3) (rHi force : Bool)
    (imm : Imm) (d : BitVec 32) :
    (rmRaw pfx w opc reg rHi (.mem (Mem.ofRip d)) force imm).bytes =
      (pfx.bytes ++ rexBytes (mkRex w rHi false false force) ++ opc.bytes ++
        [ModRM.byte ⟨0#2, reg, 5#3⟩]) ++ (imm32Bytes d ++ imm.bytes) := by
  simp [rmRaw, Raw.bytes, encodeRM, modrmBytes, sibBytes, Disp.bytes]

/-- **Relocation is a local edit.** Two RIP-relative operands differing only in
their displacement encode to byte strings that share a head and a tail and
differ exactly in the four displacement bytes. -/
theorem rmRaw_bytes_rip_congr (pfx : Pfx) (w : Bool) (opc : Opc) (reg : BitVec 3)
    (rHi force : Bool) (imm : Imm) (d e : BitVec 32) :
    ∃ head tail : List Byte,
      (rmRaw pfx w opc reg rHi (.mem (Mem.ofRip d)) force imm).bytes
          = head ++ imm32Bytes d ++ tail ∧
      (rmRaw pfx w opc reg rHi (.mem (Mem.ofRip e)) force imm).bytes
          = head ++ imm32Bytes e ++ tail := by
  refine ⟨pfx.bytes ++ rexBytes (mkRex w rHi false false force) ++ opc.bytes ++
      [ModRM.byte ⟨0#2, reg, 5#3⟩], imm.bytes, ?_, ?_⟩ <;>
    simp [rmRaw_bytes_rip, List.append_assoc]

/-- `lea r64, [rip + disp]`: three fixed bytes and the displacement. This is
the form that materialises a `.rodata` address, and the only layout-dependent
instruction in `sha256_compress` at either optimisation level.

Stated for `Sz.q`, which is what `lea` meant before the 32-bit form was added;
the bytes and the length-7 claim are REX.W-specific, since `lea r32, [rip+d]`
needs no REX prefix for RAX-RDI and is six bytes. Every pilot image uses the
64-bit form. -/
theorem encode_lea_rip (dst : Reg) (d : BitVec 32) :
    encode (.lea .q dst (Mem.ofRip d)) =
      [Rex.byte ⟨true, hiBit dst, false, false⟩, 0x8D, ModRM.byte ⟨0#2, dst.lo, 5#3⟩] ++
        imm32Bytes d := by
  simp [encode, toRaw, rmRaw_bytes_rip, mkRex, Pfx.bytes, rexBytes, Opc.bytes, Imm.bytes, Sz.w]

/-- `mov reg, [rip + disp]` at either operand size, likewise. -/
theorem encode_load_rip (sz : Sz) (dst : Reg) (d : BitVec 32) :
    encode (.load sz dst (Mem.ofRip d)) =
      (rexBytes (mkRex sz.w (hiBit dst) false false false) ++
        [0x8B, ModRM.byte ⟨0#2, dst.lo, 5#3⟩]) ++ imm32Bytes d := by
  simp [encode, toRaw, rmRaw_bytes_rip, Pfx.bytes, Opc.bytes, Imm.bytes]

/-- The length of a RIP-relative `lea` does not depend on the displacement
either, which is what makes an instruction-boundary argument
layout-independent. -/
@[simp] theorem length_encode_lea_rip (dst : Reg) (d : BitVec 32) :
    (encode (.lea .q dst (Mem.ofRip d))).length = 7 := by
  rw [encode_lea_rip]
  simp [imm32Bytes]

/-! ## Meaning of raw fields -/

/-- Instructions with a ModRM byte, given the operand size bit, REX.R, the
opcode, the ModRM `reg` field, the decoded `r/m` operand and the immediate. -/
def ofModrm (pfx : Pfx) (w rHi : Bool) (opc : Opc) (reg : BitVec 3) (op : RM) (imm : Imm)
    (part : ModrmPart) : Option Instr :=
  match opc with
  | .one b =>
    if pfx = .opsize then
      if b = 0x89#8 then some (.store .w op (mkReg rHi reg))
      else if b = 0xC7#8 then
        match imm with
        | .i16 v => some (.movI16 op v)
        | _ => none
      else none
    else if b = 0x89#8 then some (.mov (Sz.ofW w) op (mkReg rHi reg))
    else if b = 0xC7#8 then
      match imm with
      | .i32 v => some (.movI (Sz.ofW w) op v)
      | _ => none
    else if b = 0x8B#8 then op.mem?.map fun m => .load (Sz.ofW w) (mkReg rHi reg) m
    else if b = 0x88#8 then some (.store .b op (mkReg rHi reg))
    else if b = 0x8A#8 then some (.mov8 (mkReg rHi reg) op)
    else if b = 0xC6#8 then
      match reg, imm with
      | 0, .i8 v => some (.movI8 op v)
      | _, _ => none
    else if b = 0x63#8 then some (.movsxd (mkReg rHi reg) op)
    else if b = 0x8D#8 then op.mem?.map fun m => .lea (Sz.ofW w) (mkReg rHi reg) m
    else if b = 0x81#8 then
      match AluOp.ofDigit reg, imm with
      | some aop, .i32 v => some (.aluI (Sz.ofW w) aop op v)
      | _, _ => none
    else if b = 0x80#8 then
      match reg, imm with
      | 7, .i8 v => some (.cmpI8 op v)
      | _, _ => none
    else if b = 0x84#8 then some (.test8 op (mkReg rHi reg))
    else if b = 0xF6#8 then
      match reg, imm with
      | 0, .i8 v => some (.testI8 op v)
      | _, _ => none
    else if b = 0x85#8 then some (.test (Sz.ofW w) op (mkReg rHi reg))
    else if b = 0xF7#8 then
      if reg = 2#3 then some (.unary (Sz.ofW w) .not op)
      else if reg = 3#3 then some (.unary (Sz.ofW w) .neg op)
      else if reg = 4#3 then some (.mul (Sz.ofW w) op)
      else if reg = 6#3 then some (.div (Sz.ofW w) false op)
      else if reg = 7#3 then some (.div (Sz.ofW w) true op)
      else none
    else if b = 0xD3#8 then (ShiftOp.ofDigit reg).map fun sop => .shift (Sz.ofW w) sop op .cl
    else if b = 0xD1#8 then (ShiftOp.ofDigit reg).map fun sop => .shift (Sz.ofW w) sop op .one
    else if b = 0xFF#8 then
      if reg = 0#3 then some (.incdec (Sz.ofW w) false op)
      else if reg = 1#3 then some (.incdec (Sz.ofW w) true op)
      else if reg = 6#3 then some (.pushRM op)
      else none
    else if b = 0xC1#8 then
      match ShiftOp.ofDigit reg, imm with
      | some sop, .i8 n => some (.shift (Sz.ofW w) sop op (.imm n))
      | _, _ => none
    else if b = 0x83#8 then
      match AluOp.ofDigit reg, imm with
      | some aop, .i8 v => some (.aluI8 (Sz.ofW w) aop op v)
      | _, _ => none
    else
      match AluOp.ofOpcode b with
      | some aop => some (.alu (Sz.ofW w) aop op (mkReg rHi reg))
      | none => (aluOfOpcodeR b).map fun aop => .aluR (Sz.ofW w) aop (mkReg rHi reg) op
  | .two b =>
    if pfx = .rep then
      if b = 0x1E#8 then
        (if reg = 7#3 ∧ op = .reg .rdx ∧ w = false then some .endbr64 else none)
      else if b = 0xBD#8 then some (.bitcount .lzcnt (Sz.ofW w) (mkReg rHi reg) op)
      else if b = 0xBC#8 then some (.bitcount .tzcnt (Sz.ofW w) (mkReg rHi reg) op)
      else if b = 0xB8#8 then some (.bitcount .popcnt (Sz.ofW w) (mkReg rHi reg) op)
      else none
    else if b = 0x1F#8 then (nop1FIndex pfx part).map Instr.nop
    else if b = 0xAF#8 then some (.imul (Sz.ofW w) (mkReg rHi reg) op)
    else if b = 0xB6#8 then some (.movx false (Sz.ofW w) .b (mkReg rHi reg) op)
    else if b = 0xB7#8 then some (.movx false (Sz.ofW w) .w (mkReg rHi reg) op)
    else if b = 0xBE#8 then some (.movx true (Sz.ofW w) .b (mkReg rHi reg) op)
    else if b = 0xBF#8 then some (.movx true (Sz.ofW w) .w (mkReg rHi reg) op)
    else if b.extractLsb' 4 4 = 4#4 then
      some (.cmov (Sz.ofW w) (Cond.ofCode (b.extractLsb' 0 4)) (mkReg rHi reg) op)
    else if b.extractLsb' 4 4 = 9#4 then some (.setcc (Cond.ofCode (b.extractLsb' 0 4)) op)
    else none

/-- Instructions without a ModRM byte, given REX.W, REX.B, the opcode and the
immediate. -/
def ofPlain (pfx : Pfx) (w bHi : Bool) (opc : Opc) (imm : Imm) : Option Instr :=
  match opc with
  | .one b =>
    if b = 0x90#8 then
      (match pfx with
       | .none => some (.nop 0)
       | .opsize => some (.nop 1)
       | _ => none)
    else if b = 0x99#8 then some (.cxd (Sz.ofW w))
    else if b = 0x98#8 then some (.cxe (Sz.ofW w))
    else if b = 0xC3#8 then some .ret
    else if b = 0xC9#8 then some .leave
    else if b = 0xEB#8 then
      match imm with
      | .i8 v => some (.jmp8 v)
      | _ => none
    else if b = 0xA9#8 then
      match imm with
      | .i32 v => some (.testA (Sz.ofW w) v)
      | _ => none
    else if b = 0xE8#8 then
      match imm with
      | .i32 v => some (.call v)
      | _ => none
    else if b = 0xE9#8 then
      match imm with
      | .i32 v => some (.jmp v)
      | _ => none
    else if b.extractLsb' 3 5 = 0b01010#5 then some (.push (mkReg bHi (b.extractLsb' 0 3)))
    else if b.extractLsb' 3 5 = 0b01011#5 then some (.pop (mkReg bHi (b.extractLsb' 0 3)))
    else if b.extractLsb' 3 5 = 0b10111#5 then
      match imm with
      | .i64 v => some (.movabs (mkReg bHi (b.extractLsb' 0 3)) v)
      | .i32 v => some (.movI32 (mkReg bHi (b.extractLsb' 0 3)) v)
      | _ => none
    else if b.extractLsb' 4 4 = 7#4 then
      match imm with
      | .i8 v => some (.jcc8 (Cond.ofCode (b.extractLsb' 0 4)) v)
      | _ => none
    else if b = 0x3C#8 then
      match imm with
      | .i8 v => some (.cmpA8 v)
      | _ => none
    else if b = 0xA8#8 then
      match imm with
      | .i8 v => some (.testA8 v)
      | _ => none
    else
      match aluOfOpcodeA b, imm with
      | some aop, .i32 v => some (.aluA (Sz.ofW w) aop v)
      | _, _ => none
  | .two b =>
    if b = 0x0B#8 then some .ud2
    else if b.extractLsb' 3 5 = 0b11001#5 then
      some (.bswap (Sz.ofW w) (mkReg bHi (b.extractLsb' 0 3)))
    else if b.extractLsb' 4 4 = 8#4 then
      match imm with
      | .i32 v => some (.jcc (Cond.ofCode (b.extractLsb' 0 4)) v)
      | _ => none
    else none

def ofRaw (r : Raw) : Option Instr :=
  match r.modrm with
  | some (m, sib, d) =>
    ofModrm r.pfx (r.rex.getD Rex.zero).w (r.rex.getD Rex.zero).r r.opc m.reg
      (decodeRM r.fs (r.rex.getD Rex.zero).x (r.rex.getD Rex.zero).b m sib d) r.imm (m, sib, d)
  | none => ofPlain r.pfx (r.rex.getD Rex.zero).w (r.rex.getD Rex.zero).b r.opc r.imm

theorem ofRaw_rmRaw (pfx : Pfx) (w : Bool) (opc : Opc) (reg : BitVec 3) (rHi : Bool) (op : RM)
    (force : Bool) (imm : Imm) :
    ofRaw (rmRaw pfx w opc reg rHi op force imm) = ofModrm pfx w rHi opc reg op imm
      (⟨(encodeRM op).mod, reg, (encodeRM op).rm⟩, (encodeRM op).sib, (encodeRM op).disp) := by
  simp only [ofRaw, rmRaw, mkRex_getD]
  rw [decodeRM_encodeRM]

theorem ofRaw_plainRaw (w bHi : Bool) (opc : Opc) (imm : Imm) :
    ofRaw (plainRaw w bHi opc imm) = ofPlain .none w bHi opc imm := by
  simp [ofRaw, plainRaw]

private theorem setcc_opcode (c : Cond) :
    (9#4 ++ c.code) ≠ 0x1F#8 ∧ (9#4 ++ c.code) ≠ 0xAF#8 ∧ (9#4 ++ c.code) ≠ 0xB6#8 ∧
      (9#4 ++ c.code) ≠ 0xB7#8 ∧
      (9#4 ++ c.code) ≠ 0xBE#8 ∧ (9#4 ++ c.code) ≠ 0xBF#8 ∧
      (9#4 ++ c.code).extractLsb' 4 4 = 9#4 ∧ (9#4 ++ c.code).extractLsb' 0 4 = c.code := by
  cases c <;> decide

private theorem jcc_opcode (c : Cond) :
    (8#4 ++ c.code) ≠ 0x0B#8 ∧ (8#4 ++ c.code).extractLsb' 3 5 ≠ 0b11001#5 ∧
      (8#4 ++ c.code).extractLsb' 4 4 = 8#4 ∧ (8#4 ++ c.code).extractLsb' 0 4 = c.code := by
  cases c <;> decide

private theorem jcc8_opcode (c : Cond) :
    (7#4 ++ c.code) ≠ 0x90#8 ∧ (7#4 ++ c.code) ≠ 0x99#8 ∧ (7#4 ++ c.code) ≠ 0x98#8 ∧
      (7#4 ++ c.code) ≠ 0xC3#8 ∧ (7#4 ++ c.code) ≠ 0xC9#8 ∧
      (7#4 ++ c.code) ≠ 0xEB#8 ∧ (7#4 ++ c.code) ≠ 0xA9#8 ∧ (7#4 ++ c.code) ≠ 0xE8#8 ∧
      (7#4 ++ c.code) ≠ 0xE9#8 ∧ (7#4 ++ c.code).extractLsb' 3 5 ≠ 0b01010#5 ∧
      (7#4 ++ c.code).extractLsb' 3 5 ≠ 0b01011#5 ∧
      (7#4 ++ c.code).extractLsb' 3 5 ≠ 0b10111#5 ∧
      (7#4 ++ c.code).extractLsb' 4 4 = 7#4 ∧ (7#4 ++ c.code).extractLsb' 0 4 = c.code := by
  cases c <;> decide

private theorem bswap_opcode (lo : BitVec 3) :
    (0b11001#5 ++ lo) ≠ 0x0B#8 ∧ (0b11001#5 ++ lo).extractLsb' 3 5 = 0b11001#5 ∧
      (0b11001#5 ++ lo).extractLsb' 0 3 = lo := by
  revert lo; decide

private theorem regOpcode_fields (p : BitVec 5) (lo : BitVec 3) :
    (p ++ lo).extractLsb' 3 5 = p ∧ (p ++ lo).extractLsb' 0 3 = lo := by
  revert p lo; decide

private theorem push_opcode (lo : BitVec 3) :
    (0b01010#5 ++ lo) ≠ 0x90#8 ∧ (0b01010#5 ++ lo) ≠ 0x99#8 ∧ (0b01010#5 ++ lo) ≠ 0x98#8 ∧
      (0b01010#5 ++ lo) ≠ 0xC3#8 ∧ (0b01010#5 ++ lo) ≠ 0xC9#8 ∧
      (0b01010#5 ++ lo) ≠ 0xE8#8 ∧ (0b01010#5 ++ lo) ≠ 0xE9#8 ∧ (0b01010#5 ++ lo) ≠ 0xEB#8 ∧
      (0b01010#5 ++ lo) ≠ 0xA9#8 ∧ (0b01010#5 ++ lo).extractLsb' 4 4 ≠ 7#4 := by
  revert lo; decide

private theorem pop_opcode (lo : BitVec 3) :
    (0b01011#5 ++ lo) ≠ 0x90#8 ∧ (0b01011#5 ++ lo) ≠ 0x99#8 ∧ (0b01011#5 ++ lo) ≠ 0x98#8 ∧
      (0b01011#5 ++ lo) ≠ 0xC3#8 ∧ (0b01011#5 ++ lo) ≠ 0xC9#8 ∧
      (0b01011#5 ++ lo) ≠ 0xE8#8 ∧ (0b01011#5 ++ lo) ≠ 0xE9#8 ∧ (0b01011#5 ++ lo) ≠ 0xEB#8 ∧
      (0b01011#5 ++ lo) ≠ 0xA9#8 ∧ (0b01011#5 ++ lo).extractLsb' 4 4 ≠ 7#4 := by
  revert lo; decide

private theorem movabs_opcode (lo : BitVec 3) :
    (0b10111#5 ++ lo) ≠ 0x90#8 ∧ (0b10111#5 ++ lo) ≠ 0x99#8 ∧ (0b10111#5 ++ lo) ≠ 0x98#8 ∧
      (0b10111#5 ++ lo) ≠ 0xC3#8 ∧ (0b10111#5 ++ lo) ≠ 0xC9#8 ∧
      (0b10111#5 ++ lo) ≠ 0xE8#8 ∧ (0b10111#5 ++ lo) ≠ 0xE9#8 ∧ (0b10111#5 ++ lo) ≠ 0xEB#8 ∧
      (0b10111#5 ++ lo) ≠ 0xA9#8 ∧ (0b10111#5 ++ lo).extractLsb' 4 4 ≠ 7#4 := by
  revert lo; decide

/-- The NOP forms without a ModRM byte are well formed. -/
private theorem wf_nop90 (p : Pfx) (hs : shape p false (.one 0x90) = some ⟨false, .none⟩) :
    (⟨false, p, Option.none, .one 0x90, Option.none, .none⟩ : Raw).WF :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide⟩, ⟨false, .none⟩, hs,
    trivial, rfl⟩

/-- The `0F 1F` NOP forms are well formed. -/
private theorem wf_nop1F (p : Pfx) (mp : ModrmPart)
    (hs : shape p false (.two 0x1F) = some ⟨true, .none⟩) (hm : ModrmOk true (some mp)) :
    (nop1FRaw p mp).WF :=
  ⟨trivial, ⟨true, .none⟩, hs, hm, rfl⟩

/-- Lengths of the NOP encodings, stated so that `decide` sees a closed term. -/
private abbrev LenOk (r : Raw) : Prop := 0 < r.bytes.length ∧ r.bytes.length ≤ 15

/-- The meaning of the raw fields of an instruction is the instruction. -/
theorem ofRaw_toRaw (i : Instr) : ofRaw (toRaw i) = some i := by
  cases i with
  | movabs dst imm =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := movabs_opcode dst.lo
    simp [ofPlain, h1, h2, h3, h4, h5, h6, h7, h8, h9, regOpcode_fields]
  | cxd sz => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | cxe sz => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | jmp8 rel => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | testA sz imm => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | jcc8 c rel =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := jcc8_opcode c
    simp [ofPlain, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  | aluA sz op imm =>
    rw [toRaw, ofRaw_plainRaw]
    cases op <;> simp [ofPlain, aluOpcodeA, aluOfOpcodeA]
  | bswap sz dst =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3⟩ := bswap_opcode dst.lo
    simp [ofPlain, h1, h2, h3]
  | movI32 dst imm =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := movabs_opcode dst.lo
    simp [ofPlain, h1, h2, h3, h4, h5, h6, h7, h8, h9, regOpcode_fields]
  | movI16 dst imm => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | incdec sz dec dst =>
    rw [toRaw, ofRaw_rmRaw]
    cases dec <;> simp [ofModrm]
  | pushRM src => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | jmp rel => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | jcc c rel =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3, h4⟩ := jcc_opcode c
    simp [ofPlain, h1, h2, h3, h4]
  | call rel => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | ret => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | push r =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := push_opcode r.lo
    simp [ofPlain, h1, h2, h3, h4, h5, h6, h7, h8, h9, regOpcode_fields]
  | pop r =>
    rw [toRaw, ofRaw_plainRaw]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := pop_opcode r.lo
    simp [ofPlain, h1, h2, h3, h4, h5, h6, h7, h8, h9, regOpcode_fields]
  | ud2 => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | leave => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | endbr64 => rfl
  | mov8 dst src => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | movI8 dst imm => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | test8 dst src => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | testI8 dst imm => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | testA8 imm => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | cmpI8 dst imm => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm]
  | cmpA8 imm => rw [toRaw, ofRaw_plainRaw]; simp [ofPlain]
  | cmov sz c dst src =>
    rw [toRaw, ofRaw_rmRaw]
    cases c <;> simp [ofModrm, Cond.code, Cond.ofCode]
  | nop len =>
    obtain ⟨v, hv⟩ := len
    match v, hv with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | 9, _ => rfl
    | 10, _ => rfl
    | 11, _ => rfl
    | 12, _ => rfl
    | 13, _ => rfl
    | 14, _ => rfl
    | (k + 15), hk => exact absurd hk (by omega)
  | store n dst src =>
    cases n <;> rw [toRaw, ofRaw_rmRaw] <;> simp [ofModrm]
  | setcc c dst =>
    rw [toRaw, ofRaw_rmRaw]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := setcc_opcode c
    simp [ofModrm, h0, h1, h2, h3, h4, h5, h6, h7]
  | shift sz op dst count =>
    cases count <;> rw [toRaw, ofRaw_rmRaw] <;> simp [ofModrm]
  | alu sz op dst src =>
    rw [toRaw, ofRaw_rmRaw]
    cases op <;> simp [ofModrm, AluOp.opcode, AluOp.ofOpcode]
  | aluR sz op dst src =>
    rw [toRaw, ofRaw_rmRaw]
    cases op <;> simp [ofModrm, aluOpcodeR, AluOp.ofOpcode, aluOfOpcodeR]
  | aluI sz op dst imm =>
    rw [toRaw, ofRaw_rmRaw]
    simp [ofModrm]
  | aluI8 sz op dst imm =>
    rw [toRaw, ofRaw_rmRaw]
    simp [ofModrm]
  | unary sz op dst =>
    rw [toRaw, ofRaw_rmRaw]
    cases op <;> simp [ofModrm, UnOp.digit]
  | div sz signed src =>
    rw [toRaw, ofRaw_rmRaw]
    cases signed <;> simp [ofModrm]
  | movx sx sz n dst src =>
    rw [toRaw, ofRaw_rmRaw]
    cases sx <;> cases n <;> simp [ofModrm, movxOpcode]
  | bitcount op sz dst src =>
    rw [toRaw, ofRaw_rmRaw]
    cases op <;> simp [ofModrm, BitCountOp.opcode]
  | _ => rw [toRaw, ofRaw_rmRaw]; simp [ofModrm, RM.mem?]

/-! ## Well-formedness of the raw fields -/

theorem wf_rmRaw {pfx : Pfx} {w : Bool} {opc : Opc} {reg : BitVec 3} {rHi : Bool} {op : RM}
    {force : Bool} {imm : Imm} (h : shape pfx w opc = some ⟨true, imm.kind⟩) :
    (rmRaw pfx w opc reg rHi op force imm).WF := by
  refine ⟨opcOk_of_shape h, ⟨true, imm.kind⟩, ?_, encodeRM_ok op reg, rfl⟩
  simpa [rmRaw] using h

theorem wf_plainRaw {w bHi : Bool} {opc : Opc} {imm : Imm}
    (h : shape .none w opc = some ⟨false, imm.kind⟩) : (plainRaw w bHi opc imm).WF := by
  refine ⟨opcOk_of_shape h, ⟨false, imm.kind⟩, ?_, trivial, rfl⟩
  simpa [plainRaw] using h

private theorem shape_setcc (w : Bool) (c : Cond) :
    shape .none w (.two (9#4 ++ c.code)) = some ⟨true, .none⟩ := by
  revert w; cases c <;> decide

private theorem shape_jcc (c : Cond) :
    shape .none false (.two (8#4 ++ c.code)) = some ⟨false, .i32⟩ := by
  cases c <;> decide

private theorem shape_push (lo : BitVec 3) :
    shape .none false (.one (0b01010#5 ++ lo)) = some ⟨false, .none⟩ := by
  revert lo; decide

private theorem shape_pop (lo : BitVec 3) :
    shape .none false (.one (0b01011#5 ++ lo)) = some ⟨false, .none⟩ := by
  revert lo; decide

private theorem shape_movabs (lo : BitVec 3) :
    shape .none true (.one (0b10111#5 ++ lo)) = some ⟨false, .i64⟩ := by
  revert lo; decide

private theorem shape_jmp8 : shape .none false (.one 0xEB) = some ⟨false, .i8⟩ := by decide

private theorem shape_jcc8 (c : Cond) :
    shape .none false (.one (7#4 ++ c.code)) = some ⟨false, .i8⟩ := by
  cases c <;> decide

private theorem shape_testA (w : Bool) : shape .none w (.one 0xA9) = some ⟨false, .i32⟩ := by
  revert w; decide

private theorem shape_aluA (w : Bool) (op : AluOp) :
    shape .none w (.one (aluOpcodeA op)) = some ⟨false, .i32⟩ := by
  revert w; cases op <;> decide

private theorem shape_bswap (w : Bool) (lo : BitVec 3) :
    shape .none w (.two (0b11001#5 ++ lo)) = some ⟨false, .none⟩ := by
  revert w lo; decide

private theorem shape_movI32 (lo : BitVec 3) :
    shape .none false (.one (0b10111#5 ++ lo)) = some ⟨false, .i32⟩ := by
  revert lo; decide

private theorem shape_movI16 : shape .opsize false (.one 0xC7) = some ⟨true, .i16⟩ := by decide

private theorem shape_mov8 : shape .none false (.one 0x8A) = some ⟨true, .none⟩ := by decide

private theorem shape_movI8 : shape .none false (.one 0xC6) = some ⟨true, .i8⟩ := by decide

private theorem shape_endbr : shape .rep false (.two 0x1E) = some ⟨true, .none⟩ := by decide

theorem wf_toRaw (i : Instr) : (toRaw i).WF := by
  cases i with
  | movabs dst imm => exact wf_plainRaw (shape_movabs _)
  | cxd sz => exact wf_plainRaw (by cases sz <;> decide)
  | cxe sz => exact wf_plainRaw (by cases sz <;> decide)
  | jmp8 rel => exact wf_plainRaw shape_jmp8
  | jcc8 c rel => exact wf_plainRaw (shape_jcc8 c)
  | testA sz imm => exact wf_plainRaw (shape_testA _)
  | aluA sz op imm => exact wf_plainRaw (shape_aluA _ op)
  | bswap sz dst => exact wf_plainRaw (shape_bswap _ _)
  | movI32 dst imm => exact wf_plainRaw (shape_movI32 _)
  | movI16 dst imm => exact wf_rmRaw shape_movI16
  | incdec sz dec dst => exact wf_rmRaw (by cases sz <;> rfl)
  | pushRM src => exact wf_rmRaw (by decide)
  | jmp rel => exact wf_plainRaw rfl
  | jcc c rel => exact wf_plainRaw (shape_jcc c)
  | call rel => exact wf_plainRaw rfl
  | ret => exact wf_plainRaw rfl
  | push r => exact wf_plainRaw (shape_push _)
  | pop r => exact wf_plainRaw (shape_pop _)
  | ud2 => exact wf_plainRaw rfl
  | leave => exact wf_plainRaw rfl
  | endbr64 => exact ⟨trivial, ⟨true, .none⟩, shape_endbr, ⟨rfl, rfl⟩, rfl⟩
  | mov8 dst src => exact wf_rmRaw shape_mov8
  | movI8 dst imm => exact wf_rmRaw shape_movI8
  | nop len =>
    obtain ⟨v, hv⟩ := len
    match v, hv with
    | 0, _ => exact wf_nop90 .none (by decide)
    | 1, _ => exact wf_nop90 .opsize (by decide)
    | 2, _ => exact wf_nop1F .none nopM0 (by decide) ⟨rfl, rfl⟩
    | 3, _ => exact wf_nop1F .none nopM1 (by decide) ⟨rfl, rfl⟩
    | 4, _ => exact wf_nop1F .none nopM2 (by decide) ⟨rfl, rfl⟩
    | 5, _ => exact wf_nop1F .opsize nopM2 (by decide) ⟨rfl, rfl⟩
    | 6, _ => exact wf_nop1F .none nopM3 (by decide) ⟨rfl, rfl⟩
    | 7, _ => exact wf_nop1F .none nopM4 (by decide) ⟨rfl, rfl⟩
    | 8, _ => exact wf_nop1F .opsize nopM4 (by decide) ⟨rfl, rfl⟩
    | 9, _ => exact wf_nop1F (.nopPad 0) nopM4 (by decide) ⟨rfl, rfl⟩
    | 10, _ => exact wf_nop1F (.nopPad 1) nopM4 (by decide) ⟨rfl, rfl⟩
    | 11, _ => exact wf_nop1F (.nopPad 2) nopM4 (by decide) ⟨rfl, rfl⟩
    | 12, _ => exact wf_nop1F (.nopPad 3) nopM4 (by decide) ⟨rfl, rfl⟩
    | 13, _ => exact wf_nop1F (.nopPad 4) nopM4 (by decide) ⟨rfl, rfl⟩
    | 14, _ => exact wf_nop1F (.nopPad 5) nopM4 (by decide) ⟨rfl, rfl⟩
    | (k + 15), hk => exact absurd hk (by omega)
  | store n dst src => cases n <;> exact wf_rmRaw (by decide)
  | setcc c dst => exact wf_rmRaw (shape_setcc _ c)
  | cmov sz c dst src => exact wf_rmRaw (by cases sz <;> cases c <;> decide)
  | shift sz op dst count =>
    cases count <;> exact wf_rmRaw (by cases sz <;> rfl)
  | alu sz op dst src => exact wf_rmRaw (by cases sz <;> cases op <;> decide)
  | aluR sz op dst src => exact wf_rmRaw (by cases sz <;> cases op <;> decide)
  | aluI8 sz op dst imm => exact wf_rmRaw (by cases sz <;> rfl)
  | movx sx sz n dst src => exact wf_rmRaw (by cases sx <;> cases sz <;> cases n <;> decide)
  | div sz signed src => exact wf_rmRaw (by cases sz <;> rfl)
  | movI sz dst imm => exact wf_rmRaw (by cases sz <;> rfl)
  | aluI sz op dst imm => exact wf_rmRaw (by cases sz <;> rfl)
  | mov sz dst src => exact wf_rmRaw (by cases sz <;> rfl)
  | load sz dst src => exact wf_rmRaw (by cases sz <;> rfl)
  | test sz dst src => exact wf_rmRaw (by cases sz <;> rfl)
  | test8 dst src => exact wf_rmRaw (by decide)
  | testI8 dst imm => exact wf_rmRaw (by rfl)
  | testA8 imm => exact wf_plainRaw (by rfl)
  | cmpI8 dst imm => exact wf_rmRaw (by rfl)
  | cmpA8 imm => exact wf_plainRaw (by rfl)
  | unary sz op dst => exact wf_rmRaw (by cases sz <;> rfl)
  | imul sz dst src => exact wf_rmRaw (by cases sz <;> rfl)
  | mul sz src => exact wf_rmRaw (by cases sz <;> rfl)
  | movsxd dst src => exact wf_rmRaw (by decide)
  | lea sz dst src => exact wf_rmRaw (by cases sz <;> rfl)
  | bitcount op sz dst src => exact wf_rmRaw (by cases op <;> cases sz <;> rfl)

/-- The length decoder recovers the raw fields of an encoding. -/
theorem parseRaw_encode (i : Instr) (rest : List Byte) :
    parseRaw (encode i ++ rest) = .ok (toRaw i) rest :=
  parseRaw_bytes (wf_toRaw i) rest

/-! ## Decoding -/

/-- Decode one instruction from the start of `bytes`, with the number of bytes
consumed. Only canonical encodings are accepted. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match parseRaw bytes with
  | .ok r _ =>
    match ofRaw r with
    | some i => if bytes.take (encode i).length = encode i then some (i, (encode i).length) else none
    | none => none
  | _ => none

/-- Decoding an encoding consumes exactly its bytes, whatever follows it. -/
@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  simp [decode, parseRaw_encode, ofRaw_toRaw]

@[simp] theorem decode_encode (i : Instr) : decode (encode i) = some (i, (encode i).length) := by
  simpa using decode_encode_append i []

theorem encode_injective : Function.Injective encode := by
  intro i j h
  have := decode_encode i
  rw [h, decode_encode] at this
  exact (Prod.mk.inj (Option.some.inj this)).1.symm

/-- A successful decode consumes exactly the canonical encoding of its result,
which is a prefix of the input. -/
theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ bytes = encode i ++ bytes.drop n := by
  unfold decode at h
  split at h
  · split at h
    · rename_i j _
      split_ifs at h with hp
      have key : ∀ (l p : List Byte), l.take p.length = p → l = p ++ l.drop p.length :=
        fun l p hp => by
          conv_lhs => rw [← List.take_append_drop p.length l]
          rw [hp]
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      subst h1 h2
      exact ⟨rfl, key _ _ hp⟩
    · cases h
  all_goals cases h

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

/-! ## What the decoder accepts

`decode_eq_some_iff` says that `decode` accepts exactly the byte strings
beginning with a canonical encoding. The statements here say the same thing in
the terms the length decoder works in, and make the test *decidable*:
`Raw.Canonical` is a `Bool` on the raw fields, so for any concrete byte string
one can compute whether it is in the subset. `canonical_shape` records that
everything accepted has an opcode in `shape`'s table, which is the opcode table
of the model, and `canonical_wf` that it obeys `Raw.WF`, which is the layout
discipline (ModRM, SIB, displacement and immediate sizes). -/

/-- The raw fields the decoder accepts: they have a meaning, and they are the
encoding the model would have produced for that meaning. -/
def Raw.Canonical (r : Raw) : Bool :=
  match ofRaw r with
  | some i => toRaw i == r
  | none => false

/-- The canonical raw fields are exactly the image of `toRaw`. -/
theorem canonical_iff_range {r : Raw} : r.Canonical = true ↔ ∃ i, toRaw i = r := by
  unfold Raw.Canonical
  constructor
  · intro h
    cases hr : ofRaw r with
    | none => rw [hr] at h; simp at h
    | some i => rw [hr] at h; exact ⟨i, by simpa using h⟩
  · rintro ⟨i, rfl⟩
    rw [ofRaw_toRaw]
    simp

@[simp] theorem canonical_toRaw (i : Instr) : (toRaw i).Canonical = true :=
  canonical_iff_range.mpr ⟨i, rfl⟩

/-- **The subset the decoder is complete for.** `decode` succeeds exactly on the
byte strings that begin with the bytes of some canonical raw instruction, and it
then returns that instruction's meaning and the length of those bytes.

Everything else is rejected: an opcode outside `shape`'s table, a ModRM `reg`
digit the model does not use (`F7 /0`, `FF /2`, `D1 /2`), a byte-register field
that would name AH, CH, DH or BH, a redundant REX prefix, a displacement wider
than it needs to be, a `mod = 01` displacement of zero where `mod = 00` would
do, and any other legal-but-not-preferred spelling of the same instruction.
`none` therefore means "outside this canonical subset", not "invalid on
hardware". -/
theorem decode_eq_some_iff_canonical {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔
      ∃ r : Raw, r.Canonical = true ∧ ofRaw r = some i ∧ r.bytes <+: bytes ∧
        n = r.bytes.length := by
  constructor
  · intro h
    obtain ⟨hn, hpre⟩ := decode_eq_some_iff.mp h
    exact ⟨toRaw i, canonical_toRaw i, ofRaw_toRaw i, hpre, hn⟩
  · rintro ⟨r, hcanon, hmean, hpre, rfl⟩
    obtain ⟨j, rfl⟩ := canonical_iff_range.mp hcanon
    rw [ofRaw_toRaw] at hmean
    obtain rfl : j = i := Option.some.inj hmean
    exact decode_eq_some_iff.mpr ⟨rfl, hpre⟩

/-- The same, as a membership test: deciding whether a byte string starts an
instruction of the subset is a computation on raw fields. -/
theorem decode_isSome_iff {bytes : List Byte} :
    (decode bytes).isSome = true ↔ ∃ r : Raw, r.Canonical = true ∧ r.bytes <+: bytes := by
  constructor
  · intro h
    obtain ⟨⟨i, n⟩, hd⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨r, hc, -, hp, -⟩ := decode_eq_some_iff_canonical.mp hd
    exact ⟨r, hc, hp⟩
  · rintro ⟨r, hc, hp⟩
    obtain ⟨i, rfl⟩ := canonical_iff_range.mp hc
    have : decode bytes = some (i, (encode i).length) :=
      decode_eq_some_iff.mpr ⟨rfl, hp⟩
    rw [this]
    rfl

/-- Everything the decoder accepts is a well-formed raw instruction: its ModRM,
SIB, displacement and immediate follow the layout its opcode announces. -/
theorem canonical_wf {r : Raw} (h : r.Canonical = true) : r.WF := by
  obtain ⟨i, rfl⟩ := canonical_iff_range.mp h
  exact wf_toRaw i

/-- Consequently its opcode is one of those in `shape`, the opcode table of the
model: no other prefix, REX.W and opcode combination can be decoded. -/
theorem canonical_shape {r : Raw} (h : r.Canonical = true) :
    (shape r.pfx (r.rex.getD Rex.zero).w r.opc).isSome = true := by
  obtain ⟨-, sh, hs, -⟩ := canonical_wf h
  simp [hs]

/-- And every accepted byte string's leading bytes are read back by the length
decoder exactly as they were written. -/
theorem parseRaw_of_canonical {r : Raw} (h : r.Canonical = true) (rest : List Byte) :
    parseRaw (r.bytes ++ rest) = .ok r rest :=
  parseRaw_bytes (canonical_wf h) rest

/-- Decoding reads no byte beyond the instruction. -/
theorem decode_append {bytes : List Byte} (more : List Byte) {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

/-- Two encodings cannot both be prefixes of one byte string. -/
theorem decode_unique {bytes : List Byte} {i j : Instr} (hi : encode i <+: bytes)
    (hj : encode j <+: bytes) : i = j := by
  obtain ⟨ri, rfl⟩ := hi
  obtain ⟨rj, hj⟩ := hj
  have h := decode_encode_append i ri
  rw [← hj, decode_encode_append] at h
  exact (Prod.mk.inj (Option.some.inj h)).1.symm

/-- Every proper prefix of an encoding is rejected. -/
theorem decode_take_of_lt (i : Instr) {k : Nat} (hk : k < (encode i).length) :
    decode ((encode i).take k) = none := by
  cases hd : decode ((encode i).take k) with
  | none => rfl
  | some res =>
    obtain ⟨j, n⟩ := res
    obtain ⟨hn, hb⟩ := decode_sound hd
    have hji : j = i := decode_unique (bytes := encode i)
      ⟨_, (by rw [← List.append_assoc, ← hb, List.take_append_drop] :
        encode j ++ (((encode i).take k).drop n ++ (encode i).drop k) = encode i)⟩
      (List.prefix_refl _)
    subst hji
    have := congrArg List.length hb
    simp only [List.length_take, List.length_append, List.length_drop] at this
    omega

/-! ## Lengths -/

private theorem rmRaw_length (pfx : Pfx) (hpfx : pfx.bytes.length ≤ 1) (w : Bool) (opc : Opc)
    (reg : BitVec 3) (rHi : Bool) (op : RM) (force : Bool) (imm : Imm)
    (himm : imm.bytes.length ≤ 4) :
    0 < (rmRaw pfx w opc reg rHi op force imm).bytes.length ∧
      (rmRaw pfx w opc reg rHi op force imm).bytes.length ≤ 15 := by
  have hd := encodeRM_disp_length op
  have hs := encodeRM_sib_length op
  have hp : pfx.bytes.length ≤ 1 := hpfx
  have hr : ∀ x : Option Rex, (rexBytes x).length ≤ 1 := by
    intro x; cases x <;> simp [rexBytes]
  have ho : opc.bytes.length ≤ 2 := by cases opc <;> simp [Opc.bytes]
  have := hr (mkRex w rHi (encodeRM op).x (encodeRM op).b force)
  have hseg : (segBytes op.isFs).length ≤ 1 := by cases op.isFs <;> simp [segBytes]
  simp only [rmRaw, Raw.bytes, modrmBytes, List.length_append, List.length_cons]
  omega

private theorem plainRaw_length (w bHi : Bool) (opc : Opc) (imm : Imm) :
    0 < (plainRaw w bHi opc imm).bytes.length ∧ (plainRaw w bHi opc imm).bytes.length ≤ 12 := by
  have hr : ∀ x : Option Rex, (rexBytes x).length ≤ 1 := by
    intro x; cases x <;> simp [rexBytes]
  have := hr (mkRex w false false bHi false)
  have ho : 0 < opc.bytes.length ∧ opc.bytes.length ≤ 2 := by cases opc <;> simp [Opc.bytes]
  have hi : imm.bytes.length ≤ 8 := by
    cases imm <;> simp [Imm.bytes, imm64Bytes, imm32Bytes, imm16Bytes]
  simp only [plainRaw, Raw.bytes, modrmBytes, Pfx.bytes, segBytes, List.length_append,
    List.length_nil, Bool.false_eq_true, reduceIte]
  omega

/-- Every encoding has between one and fifteen bytes: the architectural limit,
reached only by the longest NOP padding. Every other form fits in fourteen. -/
theorem encode_length (i : Instr) : 0 < (encode i).length ∧ (encode i).length ≤ 15 := by
  have p := plainRaw_length
  have r : ∀ (pfx : Pfx), pfx.bytes.length ≤ 1 → ∀ w opc reg rHi op force (imm : Imm),
      imm.bytes.length ≤ 4 →
      0 < (rmRaw pfx w opc reg rHi op force imm).bytes.length ∧
        (rmRaw pfx w opc reg rHi op force imm).bytes.length ≤ 15 :=
    fun a ha b c d e f g h hi =>
      ⟨(rmRaw_length a ha b c d e f g h hi).1,
        by have := (rmRaw_length a ha b c d e f g h hi).2; omega⟩
  have p' : ∀ w bHi opc imm, 0 < (plainRaw w bHi opc imm).bytes.length ∧
      (plainRaw w bHi opc imm).bytes.length ≤ 15 := fun w bHi opc imm =>
    ⟨(p w bHi opc imm).1, by have := (p w bHi opc imm).2; omega⟩
  have h0 : (Imm.none).bytes.length ≤ 4 := by simp [Imm.bytes]
  have h8 : ∀ v, (Imm.i8 v).bytes.length ≤ 4 := by simp [Imm.bytes]
  have h32 : ∀ v, (Imm.i32 v).bytes.length ≤ 4 := by simp [Imm.bytes, imm32Bytes]
  unfold encode
  cases i with
  | movabs | cxd | cxe | jmp | jmp8 | jcc | jcc8 | call | ret | leave | push | pop | ud2 | movI32
  | aluA | testA | cmpA8 | testA8 | bswap => exact p' _ _ _ _
  | store n =>
    cases n
    · exact r _ (by decide) _ _ _ _ _ _ _ h0
    · exact r _ (by decide) _ _ _ _ _ _ _ h0
  | shift sz op dst count =>
    cases count
    · exact r _ (by decide) _ _ _ _ _ _ _ h0
    · exact r _ (by decide) _ _ _ _ _ _ _ h0
    · exact r _ (by decide) _ _ _ _ _ _ _ (h8 _)
  | nop len =>
    obtain ⟨v, hv⟩ := len
    match v, hv with
    | 0, _ => exact (by decide : LenOk ⟨false, .none, Option.none, .one 0x90, Option.none, .none⟩)
    | 1, _ =>
      exact (by decide : LenOk ⟨false, .opsize, Option.none, .one 0x90, Option.none, .none⟩)
    | 2, _ => exact (by decide : LenOk (nop1FRaw .none nopM0))
    | 3, _ => exact (by decide : LenOk (nop1FRaw .none nopM1))
    | 4, _ => exact (by decide : LenOk (nop1FRaw .none nopM2))
    | 5, _ => exact (by decide : LenOk (nop1FRaw .opsize nopM2))
    | 6, _ => exact (by decide : LenOk (nop1FRaw .none nopM3))
    | 7, _ => exact (by decide : LenOk (nop1FRaw .none nopM4))
    | 8, _ => exact (by decide : LenOk (nop1FRaw .opsize nopM4))
    | 9, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 0) nopM4))
    | 10, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 1) nopM4))
    | 11, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 2) nopM4))
    | 12, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 3) nopM4))
    | 13, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 4) nopM4))
    | 14, _ => exact (by decide : LenOk (nop1FRaw (.nopPad 5) nopM4))
    | (k + 15), hk => exact absurd hk (by omega)
  | movI | aluI => exact r _ (by decide) _ _ _ _ _ _ _ (h32 _)
  | aluI8 => exact r _ (by decide) _ _ _ _ _ _ _ (h8 _)
  | movI16 => exact r _ (by decide) _ _ _ _ _ _ _ (by simp [Imm.bytes, imm16Bytes])
  | movI8 => exact r _ (by decide) _ _ _ _ _ _ _ (h8 _)
  | cmpI8 => exact r _ (by decide) _ _ _ _ _ _ _ (h8 _)
  | testI8 => exact r _ (by decide) _ _ _ _ _ _ _ (h8 _)
  | endbr64 => exact (by decide : LenOk ⟨false, .rep, Option.none, .two 0x1E,
      some (⟨3#2, 7#3, 2#3⟩, Option.none, .none), .none⟩)
  | _ => exact r _ (by decide) _ _ _ _ _ _ _ h0

/-- A successful decode consumes between one and fourteen bytes of its input. -/
theorem decode_length {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ 0 < n ∧ n ≤ 15 ∧ n ≤ bytes.length := by
  obtain ⟨hn, hb⟩ := decode_sound h
  have hlen := congrArg List.length hb
  simp only [List.length_append, List.length_drop] at hlen
  have := encode_length i
  exact ⟨hn, by omega, by omega, by omega⟩

/-- Decoding depends only on the consumed bytes. -/
theorem decode_take {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes.take n) = some (i, n) := by
  obtain ⟨hn, hb⟩ := decode_sound h
  have : bytes.take n = encode i := by rw [hb, hn, List.take_left]
  rw [this, decode_encode, hn]

/-- The extended codec as a shared `Machine.Decoder`. It accepts exactly the
canonical encodings (`decode_eq_some_iff`). -/
def byteDecoder : Machine.Decoder Instr where
  decode := decode
  encode := encode
  decode_length_pos h := (decode_length h).2.1
  decode_length_le h := (decode_length h).2.2.2
  decode_append extra h := decode_append extra h
  decode_take h := decode_take h
  decode_encode_append instr rest := decode_encode_append instr rest

@[simp] theorem byteDecoder_decode : byteDecoder.decode = decode := rfl
@[simp] theorem byteDecoder_encode : byteDecoder.encode = encode := rfl

/-! ## Agreement with the embedded subsets -/

private theorem rex_eq_byte (a b : BitVec 1) :
    X86.rex a b = Rex.byte ⟨true, a == 1#1, false, b == 1#1⟩ := by
  revert a b; decide

private theorem hiBit_eq_hi (r : Reg) : hiBit r = (r.hi == 1#1) := by
  cases r <;> rfl

private theorem modrm_eq_byte (reg rm : BitVec 3) : X86.modrm reg rm = ModRM.byte ⟨3#2, reg, rm⟩ :=
  rfl

private theorem encode_rr (opc : Byte) (reg : BitVec 3) (rHi : Bool) (r : Reg) (imm : Imm) :
    (rmRaw .none true (.one opc) reg rHi (.reg r) false imm).bytes =
      [Rex.byte ⟨true, rHi, false, hiBit r⟩, opc, ModRM.byte ⟨3#2, reg, r.lo⟩] ++ imm.bytes := by
  simp [rmRaw, mkRex, encodeRM, Raw.bytes, Pfx.bytes, rexBytes, Opc.bytes, modrmBytes, sibBytes,
    Disp.bytes]

/-- The register subset keeps its bytes. -/
theorem encode_ofInstr (i : X86.Instr) : encode (ofInstr i) = X86.encode i := by
  cases i <;>
    simp only [encode, ofInstr, toRaw, Sz.w, encode_rr, X86.encode, rex_eq_byte, hiBit_eq_hi,
      modrm_eq_byte, Imm.bytes, List.append_nil, List.cons_append, List.nil_append,
      UnOp.digit] <;>
    simp

/-- The stack subset keeps its bytes. -/
theorem encode_ofInsn (i : X86.Insn) : encode (ofInsn i) = X86.Insn.encode i := by
  cases i with
  | base i => exact encode_ofInstr i
  | push r => cases r <;> decide
  | pop r => cases r <;> decide
  | call rel =>
    simp [encode, ofInsn, toRaw, plainRaw, mkRex, Raw.bytes, Pfx.bytes, rexBytes, Opc.bytes,
      modrmBytes, Imm.bytes, X86.Insn.encode]
  | ret => decide

/-- Decoding agrees with the register-subset decoder on its instructions. -/
theorem decode_ofInstr_iff {bytes : List Byte} {i : X86.Instr} {n : Nat} :
    decode bytes = some (ofInstr i, n) ↔ X86.decode bytes = some (i, n) := by
  rw [decode_eq_some_iff, X86.decode_eq_some_iff, encode_ofInstr]

/-- Decoding agrees with the stack-subset decoder on its instructions. -/
theorem decode_ofInsn_iff {bytes : List Byte} {i : X86.Insn} {n : Nat} :
    decode bytes = some (ofInsn i, n) ↔ X86.Insn.decode bytes = some (i, n) := by
  rw [decode_eq_some_iff, X86.Insn.decode_eq_some_iff, encode_ofInsn]

/-- Whatever the stack-subset decoder accepts, this decoder accepts with the
embedded instruction. -/
theorem decode_of_insn {bytes : List Byte} {i : X86.Insn} {n : Nat}
    (h : X86.Insn.decode bytes = some (i, n)) : decode bytes = some (ofInsn i, n) :=
  decode_ofInsn_iff.mpr h

/-! ## Byte registers

The rule: a byte-register operand names the low byte of a general-purpose
register, and SPL, BPL, SIL and DIL are encoded with a REX prefix (`40` when no
other REX bit is set). Without a REX prefix the fields `100`-`111` name AH, CH,
DH and BH, which are outside the model, so such bytes do not decode. -/

/-- One byte-register field of an instruction, if it has any.

An instruction can have two (`84 /r`, `88 /r` and `8A /r` with `mod = 11` name both a
source and a destination byte register). The *encoder* forces a REX prefix when
**any** of them needs one — `toRaw` passes a disjunction as `rmRaw`'s `force`
argument — so no such instruction is ever encoded without one. The theorem
below is stated for the field this function names. -/
def Instr.byteReg? : Instr → Option Reg
  | .setcc _ (.reg r) => some r
  | .movx _ _ .b _ (.reg r) => some r
  | .store .b _ r => some r
  | .test8 _ r => some r
  | .testI8 (.reg r) _ => some r
  | .mov8 r _ => some r
  | .movI8 (.reg r) _ => some r
  | .cmpI8 (.reg r) _ => some r
  | _ => none

/-- **Every encoding that names SPL, BPL, SIL or DIL as a byte register carries
a REX prefix, immediately after its segment override.**

*This statement changed when the FS override was added.* It used to read
"the first byte ... is a REX prefix", which the override falsifies: `8A /r` and
`88 /r` take an `r/m` operand, so `mov %fs:0x28,%sil` encodes as `64 40 8A ...`
and begins with `64`. Dropping `segBytes` restores it. Since `segBytes` is `[]`
whenever there is no override, the old reading is the `fs = false` case, kept
verbatim as `encode_byteReg_head_of_no_seg`; nothing is weakened for any
instruction that existed before. -/
theorem encode_byteReg_head {i : Instr} {r : Reg} (hi : i.byteReg? = some r)
    (hr : needsRexByte r = true) :
    ∃ x : Rex, ((encode i).drop (segBytes (toRaw i).fs).length).head? = some x.byte := by
  have hmk : ∀ w rh xb bb, ∃ x, mkRex w rh xb bb true = some x :=
    fun w rh xb bb => ⟨⟨w, rh, xb, bb⟩, by simp [mkRex]⟩
  cases i <;> simp only [Instr.byteReg?, reduceCtorEq] at hi
  case setcc c dst =>
    cases dst with
    | mem => simp at hi
    | reg q =>
      obtain rfl : q = r := Option.some.inj hi
      obtain ⟨x, hx⟩ := hmk false false (encodeRM (.reg q)).x (encodeRM (.reg q)).b
      exact ⟨x, by simp [encode, toRaw, rmRaw, RM.needsRexByte, hr, hx, Raw.bytes, Pfx.bytes,
        rexBytes, segBytes]⟩
  case movx sx sz n dst src =>
    cases n <;> cases src <;> simp only [Option.some.injEq, reduceCtorEq] at hi
    rename_i q
    obtain rfl : q = r := hi
    obtain ⟨x, hx⟩ := hmk sz.w (hiBit dst) (encodeRM (.reg q)).x (encodeRM (.reg q)).b
    exact ⟨x, by simp [encode, toRaw, rmRaw, RM.needsRexByte, hr, hx, Raw.bytes, Pfx.bytes,
      rexBytes, segBytes]⟩
  case store n dst src =>
    cases n <;> simp only [Option.some.injEq, reduceCtorEq] at hi
    obtain rfl : src = r := hi
    obtain ⟨x, hx⟩ := hmk false (hiBit src) (encodeRM dst).x (encodeRM dst).b
    exact ⟨x, by simp [encode, toRaw, rmRaw, hr, hx, Raw.bytes, Pfx.bytes, rexBytes, segBytes]⟩
  case mov8 dst src =>
    obtain rfl : dst = r := Option.some.inj hi
    obtain ⟨x, hx⟩ := hmk false (hiBit dst) (encodeRM src).x (encodeRM src).b
    exact ⟨x, by simp [encode, toRaw, rmRaw, hr, hx, Raw.bytes, Pfx.bytes, rexBytes, segBytes]⟩
  case test8 dst src =>
    obtain rfl : src = r := Option.some.inj hi
    obtain ⟨x, hx⟩ := hmk false (hiBit src) (encodeRM dst).x (encodeRM dst).b
    exact ⟨x, by simp [encode, toRaw, rmRaw, hr, hx, Raw.bytes, Pfx.bytes, rexBytes, segBytes]⟩
  case movI8 dst imm =>
    cases dst with
    | mem => simp at hi
    | reg q =>
      obtain rfl : q = r := Option.some.inj hi
      obtain ⟨x, hx⟩ := hmk false false (encodeRM (.reg q)).x (encodeRM (.reg q)).b
      exact ⟨x, by simp [encode, toRaw, rmRaw, RM.needsRexByte, hr, hx, Raw.bytes, Pfx.bytes,
        rexBytes, segBytes]⟩
  case cmpI8 dst imm =>
    cases dst with
    | mem => simp at hi
    | reg q =>
      obtain rfl : q = r := Option.some.inj hi
      obtain ⟨x, hx⟩ := hmk false false (encodeRM (.reg q)).x (encodeRM (.reg q)).b
      exact ⟨x, by simp [encode, toRaw, rmRaw, RM.needsRexByte, hr, hx, Raw.bytes, Pfx.bytes,
        rexBytes, segBytes]⟩
  case testI8 dst imm =>
    cases dst with
    | mem => simp at hi
    | reg q =>
      obtain rfl : q = r := Option.some.inj hi
      obtain ⟨x, hx⟩ := hmk false false (encodeRM (.reg q)).x (encodeRM (.reg q)).b
      exact ⟨x, by simp [encode, toRaw, rmRaw, RM.needsRexByte, hr, hx, Raw.bytes, Pfx.bytes,
        rexBytes, segBytes]⟩

/-- The first byte of every encoding without a segment override that names SPL,
BPL, SIL or DIL as a byte register is a REX prefix. This is the statement
`encode_byteReg_head` had before the FS override; `segBytes false = []`, so the
two agree on every instruction that carries no override. -/
theorem encode_byteReg_head_of_no_seg {i : Instr} {r : Reg} (hi : i.byteReg? = some r)
    (hr : needsRexByte r = true) (hfs : (toRaw i).fs = false) :
    ∃ x : Rex, (encode i).head? = some x.byte := by
  obtain ⟨x, hx⟩ := encode_byteReg_head hi hr
  exact ⟨x, by simpa [hfs] using hx⟩

/-- Consequently, bytes that do not begin with a REX prefix -- after the segment
override, if any -- never decode to an instruction whose byte-register operand
is SPL, BPL, SIL or DIL. -/
theorem decode_byteReg_rex {bytes : List Byte} {i : Instr} {n : Nat} {r : Reg}
    (h : decode bytes = some (i, n)) (hi : i.byteReg? = some r) (hr : needsRexByte r = true) :
    ∃ x : Rex, (bytes.drop (segBytes (toRaw i).fs).length).head? = some x.byte := by
  obtain ⟨x, hx⟩ := encode_byteReg_head hi hr
  obtain ⟨-, rest, rfl⟩ := decode_eq_some_iff.mp h
  refine ⟨x, ?_⟩
  rw [List.drop_append]
  cases hd : (encode i).drop (segBytes (toRaw i).fs).length with
  | nil => rw [hd] at hx; simp at hx
  | cons b t =>
    rw [hd] at hx
    simpa using hx

end Silmaril.X86.Ext
