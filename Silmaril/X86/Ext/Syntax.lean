module

public import Silmaril.X86.Machine

/-!
# Syntax of the extended local x86-64 integer model

`Ext.Instr` is a handwritten local model of a larger 64-bit-mode user-level
integer subset than `X86.Instr`/`X86.Insn`, written from the Intel SDM
instruction and opcode descriptions. It is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware description.

It contains

* 32- and 64-bit operand-size MOV/ADD/OR/AND/SUB/XOR/CMP/TEST/NEG/NOT/IMUL/MUL,
  shifts and rotates, CDQ/CQO, CWDE/CDQE and DIV/IDIV, each with a register or
  memory `r/m` operand (`RM`); the ALU operations in both directions
  (`op r/m, reg` and `op reg, r/m`) and with a sign-extended imm8 as well as an
  imm32;
* loads (MOV r32/r64, MOV r8, MOVZX/MOVSX from 8/16 bits, MOVSXD), 8/16/32/64-bit
  moves to an `r/m` destination, LEA, MOV r64, imm64, MOV r32, imm32,
  MOV r/m16, imm16 and MOV r/m8, imm8;
* INC, DEC, BSWAP and the accumulator forms of the ALU immediates and TEST;
* 8-bit TEST (`84 /r`) over low-byte registers or a byte memory operand;
* 8-bit immediate TEST (`F6 /0 ib`, `A8 ib`), without a destination write;
* 8-bit immediate CMP (`80 /7 ib`, `3C ib`), with flags from byte subtraction;
* 32- and 64-bit CMOVcc, SETcc, JMP and Jcc at both rel8 and rel32, CALL rel32,
  RET, LEAVE, ENDBR64, PUSH (register and `r/m`), POP, UD2 and the fifteen
  canonical NOP paddings;
* LZCNT, TZCNT and POPCNT, whose meaning here assumes the CPUID features
  recorded by `Instr.requires` (the model does not check CPUID).

A memory operand (`Mem`) is `[base + index * 2^scale + disp32]`, where the base
(`Mem.Base`) is a register, absent (`[index * 2^scale + disp32]` and `[disp32]`,
SIB `base = 101` with `mod = 00`), RIP (`[rip + disp32]`, `mod = 00,
r/m = 101`) or the FS segment base (`fs:[disp32]`, the base-less form under a
`64` prefix). The index register is never RSP (its encoding means "no index").

## The segment subset

`Base.fs` is the **only** segmentation in the model, and it is deliberately
narrow. It exists for the two instructions gcc's `-fstack-protector-strong`
emits, `mov %fs:0x28,%rax` and `sub %fs:0x28,%rax`, which are the only
segment-overridden instructions anywhere in the pinned `xcompile/` x86-64
matrix. Modeled: the `64` prefix on a ModRM memory operand with **no base
register**, reading `State.fsBase`. Explicitly *not* modeled, and rejected by
the decoder rather than silently misread: GS (`65`); the CS, DS, ES and SS
overrides (`2E`, `3E`, `26`, `36`), which in 64-bit mode have base zero and are
inert — `2E` is accepted only as NOP padding, never as a segment override;
`fs:` on an operand that *does* have a base register (`fs:0x8(%rax)`), which is
encodable but does not occur; segment selectors, descriptors, limit and
present-bit checks, and the `#GP`/`#SS` faults they would raise; and the
instructions that load or store the segment base (`wrfsbase`, `MSR` writes), so
`fsBase` is only ever read.

Treating FS as a `Base` rather than as a separate `seg` field on `Mem` records
exactly that subset in the type: because the model admits the override only
without a base register, "FS" and "no base register" are the same choice, and
`Base.fs` names the FS base the way `Base.rip` names the next instruction's
address. `Mem` is therefore unchanged by segmentation.

`Mem` is kept a structure, with `base : Base` replacing `base : Reg`, rather
than split into a sum of three shapes: the index and displacement fields mean
the same thing in all three, so every function over `Mem` other than the base
contribution stays uniform, and the existing `⟨base, index, disp⟩` idiom keeps
working. The one combination the encoding cannot express, `[rip + index * 2^scale
+ disp32]`, is excluded by the proof field `Mem.rip_no_index`; this keeps
`encode` total and `decode (encode i) = some i` provable for *every* `Mem`,
which a plain structure with an unconstrained `Base` would not.

Byte-register operands (TEST8, SETcc, MOVZX/MOVSX from 8 bits, 8-bit stores) name the
low byte of one of the sixteen general-purpose registers: AL, CL, DL, BL, SPL,
BPL, SIL, DIL, R8B-R15B. The legacy high-byte registers AH, CH, DH and BH are
not part of the model. The encoder therefore emits a REX prefix whenever a
byte-register field names SPL, BPL, SIL or DIL (see `Encoding.lean`).

`ofInstr` and `ofInsn` embed the existing subsets; `Encoding.lean`,
`Semantics.lean` and `Machine.lean` prove that the embeddings preserve bytes,
decoding, execution and machine steps.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Reg Word AluOp)

/-! ## Register fields -/

/-- The REX extension bit of a register number, as a Boolean. -/
def hiBit (r : Reg) : Bool := r.toBitVec.getLsbD 3

/-- The register with REX extension bit `hi` and three-bit field `lo`. -/
def mkReg (hi : Bool) (lo : BitVec 3) : Reg := Reg.ofBitVec (BitVec.ofBool hi ++ lo)

@[simp] theorem mkReg_hiBit_lo (r : Reg) : mkReg (hiBit r) r.lo = r := by
  cases r <;> rfl

@[simp] theorem hiBit_mkReg (hi : Bool) (lo : BitVec 3) : hiBit (mkReg hi lo) = hi := by
  revert hi lo; decide

@[simp] theorem lo_mkReg (hi : Bool) (lo : BitVec 3) : (mkReg hi lo).lo = lo := by
  revert hi lo; decide

theorem hiBit_eq (r : Reg) : hiBit r = decide (r.hi = 1#1) := by
  cases r <;> rfl

/-- Registers whose low byte is only addressable with a REX prefix (without one,
the same field names AH, CH, DH or BH). -/
def needsRexByte (r : Reg) : Bool := !hiBit r && decide (4#3 ≤ r.lo)

theorem needsRexByte_iff (r : Reg) :
    needsRexByte r = true ↔ r = .rsp ∨ r = .rbp ∨ r = .rsi ∨ r = .rdi := by
  cases r <;> decide

/-! ## Operand sizes -/

/-- The operand sizes of the arithmetic instructions: 32 bits (no REX.W) or
64 bits (REX.W). -/
inductive Sz where
  | d | q
  deriving DecidableEq, Repr

namespace Sz

def bits : Sz → Nat
  | .d => 32 | .q => 64

def bytes : Sz → Nat
  | .d => 4 | .q => 8

/-- The REX.W bit selecting the size. -/
def w : Sz → Bool
  | .d => false | .q => true

def ofW (w : Bool) : Sz := if w then .q else .d

@[simp] theorem ofW_w (sz : Sz) : ofW sz.w = sz := by cases sz <;> rfl

@[simp] theorem bits_q : Sz.q.bits = 64 := rfl
@[simp] theorem bits_d : Sz.d.bits = 32 := rfl

theorem bits_eq (sz : Sz) : sz.bits = 8 * sz.bytes := by cases sz <;> rfl

theorem bits_pos (sz : Sz) : 0 < sz.bits := by cases sz <;> decide

end Sz

/-- The narrow access sizes: 8 and 16 bits. -/
inductive Narrow where
  | b | w
  deriving DecidableEq, Repr

namespace Narrow

def bits : Narrow → Nat
  | .b => 8 | .w => 16

def bytes : Narrow → Nat
  | .b => 1 | .w => 2

theorem bits_eq (n : Narrow) : n.bits = 8 * n.bytes := by cases n <;> rfl

end Narrow

/-! ## Memory operands -/

/-- A scaled index register. RSP cannot be an index: its SIB encoding means
"no index". `scale` is the SIB scale field; the multiplier is `2 ^ scale`. -/
structure Index where
  reg : Reg
  scale : BitVec 2
  ne_rsp : reg ≠ .rsp

instance : DecidableEq Index := fun a b =>
  if h : a.reg = b.reg ∧ a.scale = b.scale then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

instance : Repr Index where
  reprPrec i _ := "{ reg := " ++ repr i.reg ++ ", scale := " ++ repr i.scale ++ " }"

@[ext] theorem Index.ext {a b : Index} (h1 : a.reg = b.reg) (h2 : a.scale = b.scale) : a = b := by
  cases a; cases b; simp_all

/-- The base of a memory operand. -/
inductive Base where
  /-- A base register. -/
  | reg (r : Reg)
  /-- No base register: `[index * 2^scale + disp32]` or `[disp32]`, encoded with
  a SIB byte whose `base` field is `101` and `mod = 00`. -/
  | none
  /-- RIP-relative: `[rip + disp32]`, encoded as `mod = 00, r/m = 101`. The
  address is relative to the address of the *next* instruction. -/
  | rip
  /-- The FS segment base: `fs:[index * 2^scale + disp32]` and `fs:[disp32]`,
  encoded with a `64` segment-override prefix on the base-less form. The base
  is `State.fsBase`, not a register. -/
  | fs
  deriving DecidableEq, Repr

/-- `[base + index * 2^scale + disp]` with a sign-extended 32-bit displacement.
RIP-relative addressing has no SIB byte, so it admits no index. -/
structure Mem where
  base : Base
  index : Option Index
  disp : BitVec 32
  /-- `[rip + disp32]` is encoded without a SIB byte, so it cannot carry an index. -/
  rip_no_index : base = .rip → index = Option.none

instance : DecidableEq Mem := fun a b =>
  if h : a.base = b.base ∧ a.index = b.index ∧ a.disp = b.disp then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl⟩)

instance : Repr Mem where
  reprPrec m _ :=
    "{ base := " ++ repr m.base ++ ", index := " ++ repr m.index ++
      ", disp := " ++ repr m.disp ++ " }"

@[ext] theorem Mem.ext {a b : Mem} (hb : a.base = b.base) (hi : a.index = b.index)
    (hd : a.disp = b.disp) : a = b := by
  cases a; cases b; simp_all

/-- `[base + index * 2^scale + disp]` with a base register. -/
def Mem.ofReg (base : Reg) (index : Option Index) (disp : BitVec 32) : Mem :=
  ⟨.reg base, index, disp, by simp⟩

/-- `[index * 2^scale + disp32]` and `[disp32]`: no base register. -/
def Mem.ofIndex (index : Option Index) (disp : BitVec 32) : Mem :=
  ⟨.none, index, disp, by simp⟩

/-- `[rip + disp32]`. -/
def Mem.ofRip (disp : BitVec 32) : Mem := ⟨.rip, Option.none, disp, fun _ => rfl⟩

/-- `fs:[index * 2^scale + disp32]`: the FS segment base, with no base register. -/
def Mem.ofFs (index : Option Index) (disp : BitVec 32) : Mem :=
  ⟨.fs, index, disp, by simp⟩

/-- `fs:[disp32]`, the stack-protector canary operand. -/
def Mem.fsAt (disp : BitVec 32) : Mem := Mem.ofFs Option.none disp

/-- A ModRM `r/m` operand: a register or a memory location. -/
inductive RM where
  | reg (r : Reg)
  | mem (m : Mem)
  deriving DecidableEq, Repr

/-! ## Operations and conditions -/

/-- NEG and NOT (`F7 /3`, `F7 /2`). -/
inductive UnOp where
  | neg | not
  deriving DecidableEq, Repr

/-- The shift and rotate operations of `D3 /digit` and `C1 /digit ib`. -/
inductive ShiftOp where
  | rol | ror | shl | shr | sar
  deriving DecidableEq, Repr

/-- A shift count: CL, the implicit 1 of the `D1 /digit` form, or an 8-bit
immediate. The count is masked when executed. `one` and `imm 1` have the same
meaning and different encodings (`D1 /digit` and `C1 /digit 01`); they are
distinct instructions of the model so that each byte string has one reading. -/
inductive Count where
  | cl
  | one
  | imm (n : BitVec 8)
  deriving DecidableEq, Repr

/-- LZCNT, TZCNT and POPCNT (`F3 0F BD`, `F3 0F BC`, `F3 0F B8`). These need
CPU features (see `CpuFeatures`). -/
inductive BitCountOp where
  | lzcnt | tzcnt | popcnt
  deriving DecidableEq, Repr

/-- CPUID features an instruction of the model relies on. -/
structure CpuFeatures where
  /-- LZCNT (CPUID.80000001H:ECX.ABM[bit 5]); without it `F3 0F BD` is BSR. -/
  lzcnt : Bool
  /-- TZCNT (CPUID.(EAX=07H, ECX=0H):EBX.BMI1[bit 3]); without it `F3 0F BC` is BSF. -/
  bmi1 : Bool
  /-- POPCNT (CPUID.01H:ECX.POPCNT[bit 23]); without it `F3 0F B8` raises #UD. -/
  popcnt : Bool
  deriving DecidableEq, Repr

/-- The sixteen condition codes, in the order of their four-bit encoding
(Intel SDM, Vol. 1, Appendix B). -/
inductive Cond where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

namespace Cond

def code : Cond → BitVec 4
  | o => 0 | no => 1 | b => 2 | ae => 3 | e => 4 | ne => 5 | be => 6 | a => 7
  | s => 8 | ns => 9 | p => 10 | np => 11 | l => 12 | ge => 13 | le => 14 | g => 15

def ofCode (c : BitVec 4) : Cond :=
  match c.toNat with
  | 0 => o | 1 => no | 2 => b | 3 => ae | 4 => e | 5 => ne | 6 => be | 7 => a
  | 8 => s | 9 => ns | 10 => p | 11 => np | 12 => l | 13 => ge | 14 => le | _ => g

@[simp] theorem ofCode_code (c : Cond) : ofCode c.code = c := by cases c <;> rfl

@[simp] theorem code_ofCode (c : BitVec 4) : (ofCode c).code = c := by revert c; decide

end Cond

/-! ## Instructions -/

/-- Instructions of the extended model. -/
inductive Instr where
  /-- `mov r/m, reg` (`89 /r`). -/
  | mov (sz : Sz) (dst : RM) (src : Reg)
  /-- `mov r/m, imm32` (`C7 /0 id`); sign-extended for 64 bits. -/
  | movI (sz : Sz) (dst : RM) (imm : BitVec 32)
  /-- `mov r/m16, imm16` (`66 C7 /0 iw`). -/
  | movI16 (dst : RM) (imm : BitVec 16)
  /-- `mov r8, r/m8` (`8A /r`). -/
  | mov8 (dst : Reg) (src : RM)
  /-- `mov r/m8, imm8` (`C6 /0 ib`). -/
  | movI8 (dst : RM) (imm : BitVec 8)
  /-- `mov r32, imm32` (`B8+r id`), which zero-extends to 64 bits. -/
  | movI32 (dst : Reg) (imm : BitVec 32)
  /-- `mov r64, imm64` (`REX.W B8+r io`). -/
  | movabs (dst : Reg) (imm : BitVec 64)
  /-- `mov reg, m` (`8B /r` with a memory operand). -/
  | load (sz : Sz) (dst : Reg) (src : Mem)
  /-- `mov r/m8, r8` (`88 /r`) and `mov r/m16, r16` (`66 89 /r`). The
  destination is an `r/m`, so `mod = 11` is a register-to-register move at 8 or
  16 bits: `88 C2` is `mov %al, %dl`, which `clang -O0` emits in `MD5_memset`.
  `8A /r` (`mov8`) is the other direction and encodes the same 8-bit move the
  other way round; the two are distinct instructions of the model so that each
  byte string still has exactly one reading, as with `alu` and `aluR`. -/
  | store (n : Narrow) (dst : RM) (src : Reg)
  /-- MOVZX (`sx = false`) and MOVSX (`sx = true`) from 8 or 16 bits
  (`0F B6`, `0F B7`, `0F BE`, `0F BF`). -/
  | movx (sx : Bool) (sz : Sz) (n : Narrow) (dst : Reg) (src : RM)
  /-- `movsxd r64, r/m32` (`REX.W 63 /r`). -/
  | movsxd (dst : Reg) (src : RM)
  /-- `lea r32, m` (`8D /r`) and `lea r64, m` (`REX.W 8D /r`). At 32 bits the
  effective address is computed at 64 bits and then truncated, and the write
  zero-extends, as every 32-bit register write does; `gcc -O0` emits the
  32-bit form for index arithmetic. -/
  | lea (sz : Sz) (dst : Reg) (src : Mem)
  /-- `op r/m, reg` (`01 09 21 29 31 39 /r`). -/
  | alu (sz : Sz) (op : AluOp) (dst : RM) (src : Reg)
  /-- `op reg, r/m` (`03 0B 23 2B 33 3B /r`), the direction-1 form. -/
  | aluR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM)
  /-- `op r/m, imm32` (`81 /digit id`); sign-extended for 64 bits. -/
  | aluI (sz : Sz) (op : AluOp) (dst : RM) (imm : BitVec 32)
  /-- `op r/m, imm8` (`83 /digit ib`), sign-extended to the operand size. -/
  | aluI8 (sz : Sz) (op : AluOp) (dst : RM) (imm : BitVec 8)
  /-- `op eAX/rAX, imm32` (`05 0D 25 2D 35 3D id`), the accumulator form; the
  immediate is sign-extended for 64 bits. -/
  | aluA (sz : Sz) (op : AluOp) (imm : BitVec 32)
  /-- `test r/m, reg` (`85 /r`). -/
  | test (sz : Sz) (dst : RM) (src : Reg)
  /-- `test r/m8, r8` (`84 /r`): flags from the low-byte AND, without a write. -/
  | test8 (dst : RM) (src : Reg)
  /-- `test r/m8, imm8` (`F6 /0 ib`), without a destination write. -/
  | testI8 (dst : RM) (imm : BitVec 8)
  /-- `test al, imm8` (`A8 ib`), a distinct canonical accumulator spelling. -/
  | testA8 (imm : BitVec 8)
  /-- `cmp r/m8, imm8` (`80 /7 ib`), without a destination write. -/
  | cmpI8 (dst : RM) (imm : BitVec 8)
  /-- `cmp al, imm8` (`3C ib`), a distinct canonical accumulator spelling. -/
  | cmpA8 (imm : BitVec 8)
  /-- `test eAX/rAX, imm32` (`A9 id`), the accumulator form. -/
  | testA (sz : Sz) (imm : BitVec 32)
  /-- `inc r/m` (`FF /0`) and `dec r/m` (`FF /1`). Neither changes CF. -/
  | incdec (sz : Sz) (dec : Bool) (dst : RM)
  /-- `push r/m64` (`FF /6`). -/
  | pushRM (src : RM)
  /-- `bswap r32`/`r64` (`0F C8+r`): reverse the bytes of the register. -/
  | bswap (sz : Sz) (dst : Reg)
  /-- `neg r/m` / `not r/m` (`F7 /3`, `F7 /2`). -/
  | unary (sz : Sz) (op : UnOp) (dst : RM)
  /-- `imul reg, r/m` (`0F AF /r`). -/
  | imul (sz : Sz) (dst : Reg) (src : RM)
  /-- Unsigned `mul r/m32/rm64` (`F7 /4`): the full product in EDX:EAX or
  RDX:RAX. Both input operands are sampled before either output write. -/
  | mul (sz : Sz) (src : RM)
  /-- Shifts and rotates by CL (`D3 /digit`) or imm8 (`C1 /digit ib`). -/
  | shift (sz : Sz) (op : ShiftOp) (dst : RM) (count : Count)
  /-- CDQ (`99`) and CQO (`REX.W 99`). -/
  | cxd (sz : Sz)
  /-- CWDE (`98`) and CDQE (`REX.W 98`): sign-extend the low half of the
  accumulator into it (`cwtl` and `cltq` in AT&T syntax). -/
  | cxe (sz : Sz)
  /-- DIV (`F7 /6`, `signed = false`) and IDIV (`F7 /7`, `signed = true`). -/
  | div (sz : Sz) (signed : Bool) (src : RM)
  /-- `cmovcc r32/r64, r/m32/rm64` (`0F 40+cc /r`). The source is read even
  when the condition is false; a 32-bit destination always zero-extends. -/
  | cmov (sz : Sz) (c : Cond) (dst : Reg) (src : RM)
  /-- `setcc r/m8` (`0F 90+cc /0`). -/
  | setcc (c : Cond) (dst : RM)
  /-- `jmp rel32` (`E9 cd`). -/
  | jmp (rel : BitVec 32)
  /-- `jmp rel8` (`EB cb`). -/
  | jmp8 (rel : BitVec 8)
  /-- `jcc rel32` (`0F 80+cc cd`). -/
  | jcc (c : Cond) (rel : BitVec 32)
  /-- `jcc rel8` (`70+cc cb`). -/
  | jcc8 (c : Cond) (rel : BitVec 8)
  /-- `call rel32` (`E8 cd`). -/
  | call (rel : BitVec 32)
  /-- `ret` (`C3`). -/
  | ret
  /-- `leave` (`C9`): `mov rsp, rbp` followed by `pop rbp`. -/
  | leave
  /-- `endbr64` (`F3 0F 1E FA`), the CET indirect-branch landing pad. The model
  has no shadow stack or indirect-branch tracking, so it is a no-op here; gcc
  emits it because it defaults to `-fcf-protection=full`. -/
  | endbr64
  /-- `push r64` (`50+r`, with `41` for R8-R15). -/
  | push (src : Reg)
  /-- `pop r64` (`58+r`, with `41` for R8-R15). -/
  | pop (dst : Reg)
  /-- `ud2` (`0F 0B`), the designated trap instruction. -/
  | ud2
  /-- A NOP of `len + 1` bytes, in the canonical sequence the GNU and LLVM
  assemblers emit for padding: `90`, `66 90`, then the `0F 1F /0` forms, with
  `66`-and-`2E` padding from ten bytes on. The multi-byte forms deliberately
  use non-minimal displacements, so each length is its own instruction rather
  than a `0F 1F` with an operand. -/
  | nop (len : Fin 15)
  /-- `lzcnt`/`tzcnt`/`popcnt reg, r/m` (`F3 REX? 0F BD/BC/B8 /r`). The model
  gives their LZCNT/TZCNT/POPCNT meaning, which holds only on processors with
  the corresponding feature (`Instr.requires`). -/
  | bitcount (op : BitCountOp) (sz : Sz) (dst : Reg) (src : RM)
  deriving DecidableEq, Repr

/-- The CPU features the model's meaning of an instruction assumes. The model
itself does not check them: running code containing `bitcount` on a processor
without the feature is outside the model. -/
def Instr.requires : Instr → CpuFeatures → Bool
  | .bitcount .lzcnt .., f => f.lzcnt
  | .bitcount .tzcnt .., f => f.bmi1
  | .bitcount .popcnt .., f => f.popcnt
  | _, _ => true

/-! ## Embedding the existing subsets -/

/-- The register subset `X86.Instr`, as 64-bit register-direct instructions. -/
def ofInstr : X86.Instr → Instr
  | .movRR dst src => .mov .q (.reg dst) src
  | .movRI dst imm => .movI .q (.reg dst) imm
  | .alu op dst src => .alu .q op (.reg dst) src
  | .aluI op dst imm => .aluI .q op (.reg dst) imm
  | .neg dst => .unary .q .neg (.reg dst)
  | .not dst => .unary .q .not (.reg dst)

/-- The stack subset `X86.Insn`. -/
def ofInsn : X86.Insn → Instr
  | .base i => ofInstr i
  | .push r => .push r
  | .pop r => .pop r
  | .call rel => .call rel
  | .ret => .ret

/-- The left inverse of `ofInstr`. -/
def toInstr? : Instr → Option X86.Instr
  | .mov .q (.reg dst) src => some (.movRR dst src)
  | .movI .q (.reg dst) imm => some (.movRI dst imm)
  | .alu .q op (.reg dst) src => some (.alu op dst src)
  | .aluI .q op (.reg dst) imm => some (.aluI op dst imm)
  | .unary .q .neg (.reg dst) => some (.neg dst)
  | .unary .q .not (.reg dst) => some (.not dst)
  | _ => none

/-- The left inverse of `ofInsn`. -/
def toInsn? : Instr → Option X86.Insn
  | .push r => some (.push r)
  | .pop r => some (.pop r)
  | .call rel => some (.call rel)
  | .ret => some .ret
  | i => (toInstr? i).map .base

@[simp] theorem toInstr?_ofInstr (i : X86.Instr) : toInstr? (ofInstr i) = some i := by
  cases i <;> rfl

@[simp] theorem toInsn?_ofInsn (i : X86.Insn) : toInsn? (ofInsn i) = some i := by
  cases i with
  | base i => cases i <;> rfl
  | _ => rfl

theorem ofInstr_injective : Function.Injective ofInstr := by
  intro i j h
  have := toInstr?_ofInstr i
  rw [h, toInstr?_ofInstr] at this
  exact (Option.some.inj this).symm

theorem ofInsn_injective : Function.Injective ofInsn := by
  intro i j h
  have := toInsn?_ofInsn i
  rw [h, toInsn?_ofInsn] at this
  exact (Option.some.inj this).symm

end Silmaril.X86.Ext
