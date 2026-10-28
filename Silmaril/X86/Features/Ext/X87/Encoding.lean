module

public import Silmaril.X86.Features.Ext.X87.Syntax
public import Silmaril.X86.Ext.Encoding
public import Silmaril.Machine.Decoder

/-!
# x87 encoder and decoder

The byte codec of `Fpu.Instr` in 64-bit mode (SDM Vol. 2A, §A.2.7 "Escape
opcode instructions", Tables A-7 to A-22, and the instruction pages).

An x87 instruction is an optional `64` (FS) segment override, an optional REX
prefix (only REX.X and REX.B, for a memory operand's index and base), the escape
byte `D8`–`DF` (`11011 ooo`) and a ModRM byte: with `mod ≠ 11` the ModRM `reg`
field is the opcode digit `/r` and the operand is memory, read with the integer
machine's addressing layer (`Ext.encodeMem`, `Ext.decodeMem`, `Ext.pModrm`:
SIB, displacement, RIP-relative and base-less forms); with `mod = 11` the whole
ModRM byte is opcode, and `r/m` is the stack register ST(i). FWAIT is the single
byte `9B`.

`decode` reads the raw fields (`parse`), looks the instruction up in the
opcode tables (`candidate`) and accepts it only when the input begins with the
instruction's canonical encoding, so it accepts exactly the encoder's outputs
followed by arbitrary bytes (`decode_encode_append`, `decode_sound`). Outside
the subset (`none`): redundant or other legacy prefixes (`66`, `F2`, `F3`,
other segments), REX bits the instruction ignores, non-minimal displacements,
`9B` fused with the next instruction (FSTSW/FSTCW/FINIT/FCLEX are decoded as
`FWAIT` followed by the no-wait form), and the reserved or undocumented
aliases (`D9 D8+i` FSTP1, `DC D0+i` FCOM2, `DD C8+i` FXCH4, `DF C0+i` FFREEP,
`DB E0`/`E1`/`E4` FENI/FDISI/FSETPM, …).
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (Mem Rex ModRM SIB Disp ModrmPart ModrmOk modrmBytes rexBytes segBytes
  pModrm isRex mkRex encodeMem decodeMem RM encodeRM decodeRM PResult)

/-! ## Raw fields -/

/-- The raw fields of an x87 instruction: FWAIT, or an escape `D8+o` with its
prefixes and ModRM operand. -/
inductive Raw where
  | wait
  | esc (fs : Bool) (rex : Option Rex) (o : BitVec 3) (modrm : ModRM) (sib : Option SIB)
      (disp : Disp)
  deriving DecidableEq, Repr

/-- The escape byte `D8`–`DF`. -/
def escByte (o : BitVec 3) : Byte := 0b11011#5 ++ o

theorem escByte_hi (o : BitVec 3) : (escByte o).extractLsb' 3 5 = 0b11011#5 := by
  revert o; decide

theorem escByte_lo (o : BitVec 3) : (escByte o).extractLsb' 0 3 = o := by
  revert o; decide

theorem isRex_escByte (o : BitVec 3) : isRex (escByte o) = false := by
  revert o; decide

theorem escByte_ne_9B (o : BitVec 3) : escByte o ≠ 0x9B#8 := by
  revert o; decide

theorem escByte_ne_64 (o : BitVec 3) : escByte o ≠ 0x64#8 := by
  revert o; decide

theorem rexByte_ne_9B (x : Rex) : x.byte ≠ 0x9B#8 := by
  obtain ⟨w, r, x, b⟩ := x
  revert w r x b; decide

theorem rexByte_ne_64 (x : Rex) : x.byte ≠ 0x64#8 := Rex.byte_ne_64 x

def Raw.bytes : Raw → List Byte
  | .wait => [0x9B#8]
  | .esc fs rex o m sib d => segBytes fs ++ rexBytes rex ++ escByte o :: modrmBytes (some (m, sib, d))

/-! ## Parsing -/

def parseOpc (fs : Bool) (rex : Option Rex) (c : Byte) (rest : List Byte) : Option Raw :=
  if c.extractLsb' 3 5 = 0b11011#5 then
    match pModrm true rest with
    | .ok (some (m, sib, d)) _ => some (.esc fs rex (c.extractLsb' 0 3) m sib d)
    | _ => none
  else none

def parseEsc (fs : Bool) : List Byte → Option Raw
  | [] => none
  | b :: rest =>
    if isRex b then
      match rest with
      | [] => none
      | c :: rest => parseOpc fs (some (Rex.ofByte b)) c rest
    else parseOpc fs none b rest

/-- Read the raw fields of one instruction. -/
def parse : List Byte → Option Raw
  | [] => none
  | b :: rest =>
    if b = 0x9B#8 then some .wait
    else if b = 0x64#8 then parseEsc true rest
    else parseEsc false (b :: rest)

theorem parseOpc_bytes (fs : Bool) (rex : Option Rex) (o : BitVec 3) {mp : ModrmPart}
    (h : ModrmOk true (some mp)) (rest : List Byte) :
    parseOpc fs rex (escByte o) (modrmBytes (some mp) ++ rest) =
      some (.esc fs rex o mp.1 mp.2.1 mp.2.2) := by
  obtain ⟨m, sib, d⟩ := mp
  simp only [parseOpc, escByte_hi, ↓reduceIte, Ext.pModrm_bytes h rest, escByte_lo]

/-- The raw fields the encoder emits: the ModRM operand is consistent. -/
def Raw.WF : Raw → Prop
  | .wait => True
  | .esc _ _ _ m sib d => ModrmOk true (some (m, sib, d))

theorem parse_bytes (r : Raw) (wf : r.WF) (rest : List Byte) :
    parse (r.bytes ++ rest) = some r := by
  cases r with
  | wait => rfl
  | esc fs rex o m sib d =>
    have key := parseOpc_bytes fs rex o (mp := (m, sib, d)) wf rest
    cases fs <;> cases rex <;>
      simp [Raw.bytes, parse, parseEsc, segBytes, rexBytes, escByte_ne_9B, escByte_ne_64,
        isRex_escByte, rexByte_ne_9B, rexByte_ne_64, key]

/-! ## Opcode fields -/

/-- The opcode digit of an arithmetic operation in the `D8`, `DC` (memory) and
`D8` (register, ST(0) destination) tables. -/
def Arith.digit : Arith → BitVec 3
  | .add => 0 | .mul => 1 | .sub => 4 | .subr => 5 | .div => 6 | .divr => 7

/-- The digit in the `DC`/`DE` register tables (ST(i) destination), where the
SDM assigns SUB/SUBR and DIV/DIVR the other way round (`DC E8+i` is FSUB
ST(i), ST(0)). -/
def Arith.digitR : Arith → BitVec 3
  | .add => 0 | .mul => 1 | .sub => 5 | .subr => 4 | .div => 7 | .divr => 6

def Arith.ofDigit : Nat → Option Arith
  | 0 => some .add | 1 => some .mul | 4 => some .sub | 5 => some .subr | 6 => some .div
  | 7 => some .divr | _ => none

def Arith.ofDigitR : Nat → Option Arith
  | 0 => some .add | 1 => some .mul | 5 => some .sub | 4 => some .subr | 7 => some .div
  | 6 => some .divr | _ => none

@[simp] theorem Arith.ofDigit_digit (op : Arith) : Arith.ofDigit op.digit.toNat = some op := by
  cases op <;> rfl

@[simp] theorem Arith.ofDigitR_digitR (op : Arith) : Arith.ofDigitR op.digitR.toNat = some op := by
  cases op <;> rfl

def Cond.code : Cond → BitVec 3 × BitVec 3
  | .b => (2, 0) | .e => (2, 1) | .be => (2, 2) | .u => (2, 3)
  | .nb => (3, 0) | .ne => (3, 1) | .nbe => (3, 2) | .nu => (3, 3)

/-- The escape low bits and ModRM byte fields of each no-operand instruction
(`(o, reg, rm)` of `D8+o, 11 reg rm`); FWAIT is `9B`. -/
def Nullary.code : Nullary → BitVec 3 × BitVec 3 × BitVec 3
  | .fnop => (1, 2, 0)
  | .fchs => (1, 4, 0) | .fabs => (1, 4, 1) | .ftst => (1, 4, 4) | .fxam => (1, 4, 5)
  | .fld1 => (1, 5, 0) | .fldl2t => (1, 5, 1) | .fldl2e => (1, 5, 2) | .fldpi => (1, 5, 3)
  | .fldlg2 => (1, 5, 4) | .fldln2 => (1, 5, 5) | .fldz => (1, 5, 6)
  | .f2xm1 => (1, 6, 0) | .fyl2x => (1, 6, 1) | .fptan => (1, 6, 2) | .fpatan => (1, 6, 3)
  | .fxtract => (1, 6, 4) | .fprem1 => (1, 6, 5) | .fdecstp => (1, 6, 6) | .fincstp => (1, 6, 7)
  | .fprem => (1, 7, 0) | .fyl2xp1 => (1, 7, 1) | .fsqrt => (1, 7, 2) | .fsincos => (1, 7, 3)
  | .frndint => (1, 7, 4) | .fscale => (1, 7, 5) | .fsin => (1, 7, 6) | .fcos => (1, 7, 7)
  | .fcompp => (6, 3, 1) | .fucompp => (2, 5, 1)
  | .fnclex => (3, 4, 2) | .fninit => (3, 4, 3)
  | .fnstswAx => (7, 4, 0)
  | .fwait => (0, 0, 0)

def stBits (i : Fin 8) : BitVec 3 := BitVec.ofNat 3 i.val

def stOf (b : BitVec 3) : Fin 8 := ⟨b.toNat, by have := b.isLt; simpa using this⟩

@[simp] theorem stOf_stBits (i : Fin 8) : stOf (stBits i) = i := by
  apply Fin.ext
  simp only [stOf, stBits, BitVec.toNat_ofNat]
  omega

/-! ## The encoder -/

/-- A memory form `D8+o /r`. -/
def memRaw (o r : BitVec 3) (m : Mem) : Raw :=
  let e := encodeMem m
  .esc (RM.isFs (.mem m)) (mkRex false false e.x e.b false) o ⟨e.mod, r, e.rm⟩ e.sib e.disp

/-- A register form `D8+o, 11 r rm`. -/
def regRaw (o r rm : BitVec 3) : Raw := .esc false none o ⟨3#2, r, rm⟩ none .none

def FFmt.ldCode : FFmt → BitVec 3 × BitVec 3
  | .f32 => (1, 0) | .f64 => (5, 0) | .f80 => (3, 5)
def FFmt.stpCode : FFmt → BitVec 3 × BitVec 3
  | .f32 => (1, 3) | .f64 => (5, 3) | .f80 => (3, 7)
def SFmt.esc : SFmt → BitVec 3
  | .f32 => 1 | .f64 => 5
/-- `D8` (m32fp) or `DC` (m64fp) for the arithmetic and compare forms. -/
def SFmt.arithEsc : SFmt → BitVec 3
  | .f32 => 0 | .f64 => 4
def IFmt.ldCode : IFmt → BitVec 3 × BitVec 3
  | .i16 => (7, 0) | .i32 => (3, 0) | .i64 => (7, 5)
def IFmt.stpCode : IFmt → BitVec 3 × BitVec 3
  | .i16 => (7, 3) | .i32 => (3, 3) | .i64 => (7, 7)
def IFmt.ttpCode : IFmt → BitVec 3 × BitVec 3
  | .i16 => (7, 1) | .i32 => (3, 1) | .i64 => (5, 1)
def WFmt.esc : WFmt → BitVec 3
  | .i16 => 7 | .i32 => 3
/-- `DE` (m16int) or `DA` (m32int) for the integer arithmetic and compare forms. -/
def WFmt.arithEsc : WFmt → BitVec 3
  | .i16 => 6 | .i32 => 2

def popDigit (pop : Bool) (base : BitVec 3) : BitVec 3 := if pop then base + 1 else base

def toRaw : Instr → Raw
  | .fld f m => memRaw f.ldCode.1 f.ldCode.2 m
  | .fst f m => memRaw f.esc 2 m
  | .fstp f m => memRaw f.stpCode.1 f.stpCode.2 m
  | .fild f m => memRaw f.ldCode.1 f.ldCode.2 m
  | .fist f m => memRaw f.esc 2 m
  | .fistp f m => memRaw f.stpCode.1 f.stpCode.2 m
  | .fisttp f m => memRaw f.ttpCode.1 f.ttpCode.2 m
  | .arithMem op f m => memRaw f.arithEsc op.digit m
  | .arithInt op f m => memRaw f.arithEsc op.digit m
  | .comMem f pop m => memRaw f.arithEsc (popDigit pop 2) m
  | .comInt f pop m => memRaw f.arithEsc (popDigit pop 2) m
  | .arithSt0 op i => regRaw 0 op.digit (stBits i)
  | .arithSti op i pop => regRaw (if pop then 6 else 4) op.digitR (stBits i)
  | .fldSt i => regRaw 1 0 (stBits i)
  | .fstSt i pop => regRaw 5 (popDigit pop 2) (stBits i)
  | .fxch i => regRaw 1 1 (stBits i)
  | .ffree i => regRaw 5 0 (stBits i)
  | .fcom i pop => regRaw 0 (popDigit pop 2) (stBits i)
  | .fucom i pop => regRaw 5 (popDigit pop 4) (stBits i)
  | .fcomi u pop i => regRaw (if pop then 7 else 3) (if u then 5 else 6) (stBits i)
  | .fcmov c i => regRaw c.code.1 c.code.2 (stBits i)
  | .fldcw m => memRaw 1 5 m
  | .fnstcw m => memRaw 1 7 m
  | .fnstsw m => memRaw 5 7 m
  | .fldenv m => memRaw 1 4 m
  | .fnstenv m => memRaw 1 6 m
  | .frstor m => memRaw 5 4 m
  | .fnsave m => memRaw 5 6 m
  | .fbld m => memRaw 7 4 m
  | .fbstp m => memRaw 7 6 m
  | .nullary .fwait => .wait
  | .nullary op => regRaw op.code.1 op.code.2.1 op.code.2.2

/-- The canonical encoding. -/
def encode (i : Instr) : List Byte := (toRaw i).bytes

/-! ## The opcode tables -/

/-- The memory forms `D8+o /r`. -/
def memTable (o r : Nat) (m : Mem) : Option Instr :=
  match o, r with
  | 0, 2 => some (.comMem .f32 false m) | 0, 3 => some (.comMem .f32 true m)
  | 0, r => (Arith.ofDigit r).map fun op => .arithMem op .f32 m
  | 1, 0 => some (.fld .f32 m) | 1, 2 => some (.fst .f32 m) | 1, 3 => some (.fstp .f32 m)
  | 1, 4 => some (.fldenv m) | 1, 5 => some (.fldcw m) | 1, 6 => some (.fnstenv m)
  | 1, 7 => some (.fnstcw m)
  | 2, 2 => some (.comInt .i32 false m) | 2, 3 => some (.comInt .i32 true m)
  | 2, r => (Arith.ofDigit r).map fun op => .arithInt op .i32 m
  | 3, 0 => some (.fild .i32 m) | 3, 1 => some (.fisttp .i32 m) | 3, 2 => some (.fist .i32 m)
  | 3, 3 => some (.fistp .i32 m) | 3, 5 => some (.fld .f80 m) | 3, 7 => some (.fstp .f80 m)
  | 4, 2 => some (.comMem .f64 false m) | 4, 3 => some (.comMem .f64 true m)
  | 4, r => (Arith.ofDigit r).map fun op => .arithMem op .f64 m
  | 5, 0 => some (.fld .f64 m) | 5, 1 => some (.fisttp .i64 m) | 5, 2 => some (.fst .f64 m)
  | 5, 3 => some (.fstp .f64 m) | 5, 4 => some (.frstor m) | 5, 6 => some (.fnsave m)
  | 5, 7 => some (.fnstsw m)
  | 6, 2 => some (.comInt .i16 false m) | 6, 3 => some (.comInt .i16 true m)
  | 6, r => (Arith.ofDigit r).map fun op => .arithInt op .i16 m
  | 7, 0 => some (.fild .i16 m) | 7, 1 => some (.fisttp .i16 m) | 7, 2 => some (.fist .i16 m)
  | 7, 3 => some (.fistp .i16 m) | 7, 4 => some (.fbld m) | 7, 5 => some (.fild .i64 m)
  | 7, 6 => some (.fbstp m) | 7, 7 => some (.fistp .i64 m)
  | _, _ => none

/-- The no-operand forms of `D9`, `DA`, `DB`, `DE` and `DF`. -/
def nullaryTable (o r i : Nat) : Option Nullary :=
  match o, r, i with
  | 1, 2, 0 => some .fnop
  | 1, 4, 0 => some .fchs | 1, 4, 1 => some .fabs | 1, 4, 4 => some .ftst | 1, 4, 5 => some .fxam
  | 1, 5, 0 => some .fld1 | 1, 5, 1 => some .fldl2t | 1, 5, 2 => some .fldl2e
  | 1, 5, 3 => some .fldpi | 1, 5, 4 => some .fldlg2 | 1, 5, 5 => some .fldln2
  | 1, 5, 6 => some .fldz
  | 1, 6, 0 => some .f2xm1 | 1, 6, 1 => some .fyl2x | 1, 6, 2 => some .fptan
  | 1, 6, 3 => some .fpatan | 1, 6, 4 => some .fxtract | 1, 6, 5 => some .fprem1
  | 1, 6, 6 => some .fdecstp | 1, 6, 7 => some .fincstp
  | 1, 7, 0 => some .fprem | 1, 7, 1 => some .fyl2xp1 | 1, 7, 2 => some .fsqrt
  | 1, 7, 3 => some .fsincos | 1, 7, 4 => some .frndint | 1, 7, 5 => some .fscale
  | 1, 7, 6 => some .fsin | 1, 7, 7 => some .fcos
  | 2, 5, 1 => some .fucompp
  | 3, 4, 2 => some .fnclex | 3, 4, 3 => some .fninit
  | 7, 4, 0 => some .fnstswAx
  | _, _, _ => none

/-- The register forms `D8+o, 11 r i`. -/
def regTable (o r : Nat) (i : Fin 8) : Option Instr :=
  match o, r with
  | 0, 2 => some (.fcom i false) | 0, 3 => some (.fcom i true)
  | 0, r => (Arith.ofDigit r).map fun op => .arithSt0 op i
  | 1, 0 => some (.fldSt i) | 1, 1 => some (.fxch i)
  | 2, 0 => some (.fcmov .b i) | 2, 1 => some (.fcmov .e i) | 2, 2 => some (.fcmov .be i)
  | 2, 3 => some (.fcmov .u i)
  | 3, 0 => some (.fcmov .nb i) | 3, 1 => some (.fcmov .ne i) | 3, 2 => some (.fcmov .nbe i)
  | 3, 3 => some (.fcmov .nu i)
  | 3, 5 => some (.fcomi true false i) | 3, 6 => some (.fcomi false false i)
  | 4, r => (Arith.ofDigitR r).map fun op => .arithSti op i false
  | 5, 0 => some (.ffree i) | 5, 2 => some (.fstSt i false) | 5, 3 => some (.fstSt i true)
  | 5, 4 => some (.fucom i false) | 5, 5 => some (.fucom i true)
  | 6, 3 => if i.val = 1 then some (.nullary .fcompp) else none
  | 6, r => (Arith.ofDigitR r).map fun op => .arithSti op i true
  | 7, 5 => some (.fcomi true true i) | 7, 6 => some (.fcomi false true i)
  | o, r => (nullaryTable o r i.val).map .nullary

/-- The instruction the raw fields name, if any (not yet checked to be the
canonical encoding). -/
def candidate : Raw → Option Instr
  | .wait => some (.nullary .fwait)
  | .esc fs rex o m sib d =>
    if m.mod = 3#2 then regTable o.toNat m.reg.toNat (stOf m.rm)
    else memTable o.toNat m.reg.toNat
      (decodeMem fs (rex.getD Rex.zero).x (rex.getD Rex.zero).b m sib d)

/-! ## Round trip -/

theorem decodeMem_encodeMem (m : Mem) (r : BitVec 3) :
    (encodeMem m).mod ≠ 3#2 ∧
      decodeMem (RM.isFs (.mem m)) (encodeMem m).x (encodeMem m).b
        ⟨(encodeMem m).mod, r, (encodeMem m).rm⟩ (encodeMem m).sib (encodeMem m).disp = m := by
  have h := Ext.decodeRM_encodeRM (.mem m) r
  simp only [encodeRM] at h
  unfold decodeRM at h
  split at h
  · cases h
  · rename_i hm
    exact ⟨hm, RM.mem.inj h⟩

theorem candidate_memRaw (o r : BitVec 3) (m : Mem) :
    candidate (memRaw o r m) = memTable o.toNat r.toNat m := by
  obtain ⟨h3, hm⟩ := decodeMem_encodeMem m r
  simp only [memRaw, candidate, h3, ↓reduceIte, Ext.mkRex_getD]
  rw [hm]

theorem candidate_regRaw (o r rm : BitVec 3) :
    candidate (regRaw o r rm) = regTable o.toNat r.toNat (stOf rm) := by
  simp [regRaw, candidate]

theorem regTable_nullary (op : Nullary) (h : op ≠ .fwait) :
    regTable op.code.1.toNat op.code.2.1.toNat (stOf op.code.2.2) = some (.nullary op) := by
  cases op <;> first | exact absurd rfl h | rfl

theorem candidate_toRaw (i : Instr) : candidate (toRaw i) = some i := by
  cases i with
  | nullary op =>
    by_cases h : op = .fwait
    · subst h; rfl
    · have e : toRaw (.nullary op) = regRaw op.code.1 op.code.2.1 op.code.2.2 := by
        cases op <;> first | exact absurd rfl h | rfl
      rw [e, candidate_regRaw, regTable_nullary op h]
  | fld f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fst f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fstp f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fild f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fist f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fistp f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fisttp f m => cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | arithMem op f m => cases op <;> cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | arithInt op f m => cases op <;> cases f <;> rw [toRaw, candidate_memRaw] <;> rfl
  | comMem f pop m => cases f <;> cases pop <;> rw [toRaw, candidate_memRaw] <;> rfl
  | comInt f pop m => cases f <;> cases pop <;> rw [toRaw, candidate_memRaw] <;> rfl
  | fldcw m | fnstcw m | fnstsw m | fldenv m | fnstenv m | frstor m | fnsave m | fbld m
  | fbstp m => rw [toRaw, candidate_memRaw]; rfl
  | arithSt0 op i => cases op <;> rw [toRaw, candidate_regRaw, stOf_stBits] <;> rfl
  | arithSti op i pop => cases op <;> cases pop <;> rw [toRaw, candidate_regRaw, stOf_stBits] <;> rfl
  | fldSt i | fxch i | ffree i => rw [toRaw, candidate_regRaw, stOf_stBits]; rfl
  | fstSt i pop | fcom i pop | fucom i pop =>
    cases pop <;> rw [toRaw, candidate_regRaw, stOf_stBits] <;> rfl
  | fcomi u pop i => cases u <;> cases pop <;> rw [toRaw, candidate_regRaw, stOf_stBits] <;> rfl
  | fcmov c i => cases c <;> rw [toRaw, candidate_regRaw, stOf_stBits] <;> rfl

theorem toRaw_wf (i : Instr) : (toRaw i).WF := by
  have hmem : ∀ o r m, (memRaw o r m).WF := fun o r m => Ext.encodeRM_ok (.mem m) r
  have hreg : ∀ o r rm, (regRaw o r rm).WF := fun o r rm => by
    simp [regRaw, Raw.WF, ModrmOk, Ext.needsSib, Ext.dispKind, Disp.kind]
  cases i with
  | nullary op => cases op <;> trivial
  | _ => first | exact hmem _ _ _ | exact hreg _ _ _

/-! ## The decoder -/

/-- Decode one instruction from the front of `bytes`: the raw fields name an
instruction and the input begins with its canonical encoding. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match parse bytes with
  | some r =>
    match candidate r with
    | some i => if bytes.take (encode i).length = encode i then some (i, (encode i).length) else none
    | none => none
  | none => none

@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  simp [decode, encode, parse_bytes _ (toRaw_wf i), candidate_toRaw]

theorem eq_append_drop_of_take {l p : List Byte} (h : l.take p.length = p) :
    l = p ++ l.drop p.length := by
  conv_lhs => rw [← List.take_append_drop p.length l]
  rw [h]

theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat} (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ bytes = encode i ++ bytes.drop n := by
  unfold decode at h
  split at h
  · split at h
    · split_ifs at h with hp
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      subst h1 h2
      exact ⟨rfl, eq_append_drop_of_take hp⟩
    · cases h
  · cases h

theorem encode_ne_nil (i : Instr) : encode i ≠ [] := by
  unfold encode
  cases toRaw i <;> simp [Raw.bytes]

/-- The codec as a `Machine.Decoder`. -/
def byteDecoder : Machine.Decoder Instr where
  decode := decode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := decode_sound h
    exact List.length_pos_of_ne_nil (encode_ne_nil _)
  decode_length_le {bytes i n} h := by
    obtain ⟨hn, hb⟩ := decode_sound h
    rw [hb, hn]; simp
  decode_append {bytes i n} extra h := by
    obtain ⟨hn, hb⟩ := decode_sound h
    rw [hb, List.append_assoc, decode_encode_append, hn]
  decode_take {bytes i n} h := by
    obtain ⟨hn, hb⟩ := decode_sound h
    rw [hb, hn, List.take_left, ← hn]
    simpa [hn] using decode_encode_append i []
  decode_encode_append := decode_encode_append

end Silmaril.X86.Features.Fpu
