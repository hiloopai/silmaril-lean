module

public import Silmaril.X86.Ext.Semantics
public import Silmaril.X86.Ext9.Defs

/-!
# Bir9: a first-order symbolic block IR for lifted x86-64 code

A **Bir9 block** is the symbolic summary of a straight-line piece of machine code:

* a list of effectful statements (`Stmt`): loads, stores, the push and pop of the stack,
  condition evaluations, traps, alignment checks and operator checks (`Stmt.chk`, the `#DE`
  of a division, the zero source of BSF/BSR). Every statement that produces a value appends
  it to the block's value list, so a later expression names it `E.v i` (SSA without
  φ-nodes, which a single block does not need);
* a final register map (`Block.regs`, sparse: unlisted registers are unchanged), the final
  flags (`F`), the final `rip` (`E`) and the changed XMM registers (`Block.xmm`).

Expressions (`E`) are pure 64-bit terms over the block-entry state (`E.reg`, `E.rip`,
`E.fs`, `E.xmm`), earlier statement results (`E.v`) and constants. Their operations are the
functions the machine semantics uses (`AluOp.resultN`, `ShiftOp.result`, `logicFlagsN`,
`Ext.divide`, `Ext9.imulWide`, `Ext9.bsrIndex`, …), at the width the instruction used, so
a block means what `Silmaril.X86.Ext.exec` and `Ext9.execNew` compute, and the soundness
proof is unfolding rather than arithmetic. The operators without a structural form (DIV
and IDIV, MUL and one-operand IMUL halves, BSF, BSR, ADC/SBB) are one constructor each in
`E`, `F` and `Stmt` (`E.xop`, `F.xop`, `Stmt.chk`) over the enumerations `EOp`, `FOp`,
`COp`, so adding one extends an enumeration and its denotation only.

## Listings

A lifted listing is a list of `LInstr` with their byte lengths:

* `LInstr.ext i`: an `Ext` instruction, run by `Ext.exec`, checked by `listingOk` against
  `Ext.decode`;
* `LInstr.n9 i`: a new `Ext9` form, run by `Ext9.execNew`, checked against `Ext9.decode`;
* `LInstr.x i` (`XInstr`: 8-bit ALU/TEST, CMOV, BT, indirect JMP/CALL, high-byte ALU/TEST)
  and `LInstr.sse i` (`SInstr`: 128-bit moves and the zeroing idiom): extension forms with
  semantics written here from the Intel SDM. `listingOk` checks only their **length**, and
  `extCount` counts them. The block certificates of `Silmaril.X86.BlockCert9` accept only
  `ext` and `n9` entries (`toX9`), so a contract proved there never trusts them.

`execBlock` runs a listing on `XState` (the core state and the sixteen XMM registers) and
stops at the first non-`ok` result; `Block.run` runs a block.

## The lifter

`symExec` executes a listing symbolically (`symStep`, one instruction at a time) and returns
its block, or `none` for an instruction it does not handle (`adc`/`sbb`, `op r16,r/m16`,
`test r/m8,imm8` on AH..BH and `bt`; the `Ext8` 8-bit forms have no `LInstr` entry).
`liftBlock` is `symExec` followed by the simplifier `Block.simp`. Nothing about either is trusted:
`Silmaril.X86.Bir9.liftBlock_sound` (`Bir9/Thms.lean`) proves that `liftBlock L = some b`
gives `execBlock L s mem = b.run s mem` for every state and memory, and the equation
`liftBlock L = some b` is closed by `decide +kernel`.

Trust: the `Ext` and `Ext9` semantics (handwritten from the SDM, see `docs/x86.md`), and,
for `LInstr.x`/`LInstr.sse` entries only, the semantics of `XInstr.exec`/`SInstr.exec` and
the transcription of their bytes.
-/

@[expose] public section

namespace Silmaril.X86.Bir9

open Silmaril.X86 (Reg Word State MState Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## Extension instructions -/

/-- The second operand of an 8-bit ALU or TEST form. -/
inductive Src8 where
  | reg (r : Reg)
  | imm (b : BitVec 8)
  deriving DecidableEq, Repr

/-- Integer instructions outside `Silmaril.X86.Ext.Instr` that compiled code needs. -/
inductive XInstr where
  /-- `op r/m8, r8` / `op r/m8, imm8` / `cmp al, imm8` (`00..38 /r`, `80 /digit ib`, `3C ib`). -/
  | alu8 (op : AluOp) (dst : RM) (src : Src8)
  /-- `test r/m8, r8` / `test r/m8, imm8` (`84 /r`, `F6 /0 ib`, `A8 ib`). -/
  | test8 (dst : RM) (src : Src8)
  /-- `cmovcc reg, r/m` (`0F 40+cc /r`). The source is read whatever the
  condition, and a 32-bit form zero-extends the destination either way. -/
  | cmov (sz : Sz) (c : Cond) (dst : Reg) (src : RM)
  /-- `bt r/m64, r64` (register form, `REX.W 0F A3 /r`): CF := bit `src mod 64`. -/
  | bt (dst src : Reg)
  /-- `jmp r/m64` (`FF /4`). -/
  | jmpInd (src : RM)
  /-- `call r/m64` (`FF /2`). -/
  | callInd (src : RM)
  /-- `op AH/CH/DH/BH, imm8` (`80 /digit ib` with a high-byte register): `r` is the
  64-bit register whose bits 15:8 are the operand. -/
  | aluHi (op : AluOp) (r : Reg) (imm : BitVec 8)
  /-- `test AH/CH/DH/BH, imm8` (`F6 /0 ib`). -/
  | testHi (r : Reg) (imm : BitVec 8)
  deriving DecidableEq, Repr

/-- Read an 8-bit source operand. -/
def Src8.read (src : Src8) (s : State) : BitVec 8 :=
  match src with
  | .reg r => (s.read r).setWidth 8
  | .imm b => b

/-- Execute an extension instruction of `length` bytes. -/
def XInstr.exec (i : XInstr) (s : State) (memory : Memory) (length : Nat) : Result :=
  let next := s.rip + BitVec.ofNat 64 length
  match i with
  | .alu8 op dst src =>
    match readNarrow .b dst s memory next with
    | none => .dataFault
    | some x =>
      let y := src.read s
      if op = .cmp then retire next (some ({ s with flags := AluOp.flagsN op x y }, memory))
      else retire next ((writeRM8 dst (AluOp.resultN op x y) s memory next).map fun r =>
        ({ r.1 with flags := AluOp.flagsN op x y }, r.2))
  | .test8 dst src =>
    match readNarrow .b dst s memory next with
    | none => .dataFault
    | some x =>
      let x8 : BitVec 8 := x
      retire next (some ({ s with flags := logicFlagsN (x8 &&& src.read s) }, memory))
  | .cmov sz c dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some v =>
      match c.eval s.flags with
      | none => .undefinedCondition c
      | some b => retire next (some (sz.write s dst (if b then v else sz.read s dst), memory))
  | .bt dst src =>
    let bit := (s.read dst).getLsbD ((s.read src).toNat % 64)
    retire next (some ({ s with flags := { s.flags with
      carry := some bit, overflow := none, sign := none, adjust := none, parity := none } },
      memory))
  | .jmpInd src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some v => .ok { s with rip := v } memory
  | .callInd src =>
    match readRM .q src s memory next with
    | none => .dataFault
    | some v =>
      match pushWord s memory next with
      | none => .dataFault
      | some (t, m) => .ok { t with rip := v } m
  | .aluHi op r imm =>
    let x : BitVec 8 := ((s.read r) >>> 8).setWidth 8
    if op = .cmp then retire next (some ({ s with flags := AluOp.flagsN op x imm }, memory))
    else retire next (some ({ s.write r ((s.read r &&& ~~~(0xFF00#64)) |||
        ((AluOp.resultN op x imm).setWidth 64 <<< 8)) with flags := AluOp.flagsN op x imm }, memory))
  | .testHi r imm =>
    let x : BitVec 8 := ((s.read r) >>> 8).setWidth 8
    retire next (some ({ s with flags := logicFlagsN (x &&& imm) }, memory))

/-! ## SSE registers and moves

`Silmaril.X86.Ext.State` has no vector registers. Compiled C uses SSE registers even in
integer code, to zero and copy structures sixteen bytes at a time, so the
lifting machine is `XState`: an `Silmaril.X86.Ext.State` together with the sixteen 128-bit
XMM registers. `Ext` and `XInstr` instructions leave the XMM registers alone;
`SInstr` are the moves. -/

/-- The sixteen XMM registers. -/
abbrev Xmm := Fin 16 → BitVec 128

def Xmm.set (x : Xmm) (d : Fin 16) (v : BitVec 128) : Xmm := fun i => if i = d then v else x i

/-- The machine state of the lifting layer. -/
structure XState where
  core : State
  xmm : Xmm

/-- `Silmaril.X86.Ext.Result` over `XState`. -/
inductive XResult where
  | ok (s : XState) (memory : Memory)
  | dataFault
  | divideError
  | undefinedCondition (c : Cond)
  | trap

/-- A core result, with the XMM registers it leaves unchanged. -/
def liftR (x : Xmm) : Result → XResult
  | .ok s m => .ok ⟨s, x⟩ m
  | .dataFault => .dataFault
  | .divideError => .divideError
  | .undefinedCondition c => .undefinedCondition c
  | .trap => .trap

/-- SSE moves (the integer, non-arithmetic subset). -/
inductive SInstr where
  /-- `movdqa`/`movaps` (`aligned`) and `movdqu`/`movups` `xmm, m128`. -/
  | load128 (aligned : Bool) (dst : Fin 16) (src : Mem)
  /-- `movdqa`/`movaps` (`aligned`) and `movdqu`/`movups` `m128, xmm`. -/
  | store128 (aligned : Bool) (dst : Mem) (src : Fin 16)
  /-- `pxor x, x` / `xorps x, x`: the zeroing idiom. -/
  | zero (dst : Fin 16)
  /-- `movdqa`/`movaps xmm, xmm`. -/
  | mov (dst src : Fin 16)
  deriving DecidableEq, Repr

/-- The low and high 64-bit halves of a 128-bit value. -/
def lo64 (v : BitVec 128) : Word := v.setWidth 64
def hi64 (v : BitVec 128) : Word := v.extractLsb' 64 64

/-- An aligned form faults (`#GP`, reported as a data fault) on an address that
is not a multiple of 16. -/
def misaligned (aligned : Bool) (a : Word) : Bool := aligned && a.toNat % 16 != 0

/-- Execute an SSE move. A 16-byte access is two 8-byte accesses: either
faults exactly when the access as a whole does. -/
def SInstr.exec (i : SInstr) (s : XState) (memory : Memory) (length : Nat) : XResult :=
  let next := s.core.rip + BitVec.ofNat 64 length
  let fin (x : Xmm) (m : Memory) : XResult := .ok ⟨{ s.core with rip := next }, x⟩ m
  match i with
  | .load128 al d src =>
    let a := src.addr s.core next
    if misaligned al a then .dataFault else
    match loadN memory a 8 with
    | none => .dataFault
    | some l =>
      match loadN memory (a + 8#64) 8 with
      | none => .dataFault
      | some h => fin (s.xmm.set d (h ++ l)) memory
  | .store128 al dst src =>
    let a := dst.addr s.core next
    if misaligned al a then .dataFault else
    match storeN memory a 8 (lo64 (s.xmm src)) with
    | none => .dataFault
    | some m1 =>
      match storeN m1 (a + 8#64) 8 (hi64 (s.xmm src)) with
      | none => .dataFault
      | some m2 => fin s.xmm m2
  | .zero d => fin (s.xmm.set d 0) memory
  | .mov d src => fin (s.xmm.set d (s.xmm src)) memory

/-- The instructions a lifted listing may contain. -/
inductive LInstr where
  | ext (i : Silmaril.X86.Ext.Instr)
  | x (i : XInstr)
  | sse (i : SInstr)
  /-- A form of the decoder extension `Ext9` (`Ext9.New`), with `Ext9.execNew`'s
  semantics. Checked against `Ext9.decode` by `listingOk`. -/
  | n9 (i : Ext9.New)
  deriving DecidableEq, Repr

/-- Execute a listed instruction with its byte length. On `Ext` instructions
this is `Silmaril.X86.Ext.exec`, with the XMM registers unchanged. -/
def LInstr.exec : LInstr → XState → Memory → Nat → XResult
  | .ext i, s, m, len => liftR s.xmm (Silmaril.X86.Ext.exec i s.core m len)
  | .x i, s, m, len => liftR s.xmm (XInstr.exec i s.core m len)
  | .sse i, s, m, len => SInstr.exec i s m len
  | .n9 i, s, m, len => liftR s.xmm (Ext9.execNew i s.core m (s.core.rip + BitVec.ofNat 64 len))

/-- Run a straight-line list of instructions (each with its length): stop at
the first non-`ok` result. -/
def execBlock : List (LInstr × Nat) → XState → Memory → XResult
  | [], s, m => .ok s m
  | (i, len) :: rest, s, m =>
    match i.exec s m len with
    | .ok s' m' => execBlock rest s' m'
    | r => r

/-! ## Extension operators

The base IR has no division, no double-width products, no bit scans and no
add-with-carry. Bir9 adds them as three *operator* constructors, one each to `E`, `F` and
`Stmt`, whose meaning is a non-recursive function of up to three 64-bit operands: so a new
operator only extends the enumerations below and their denotations, never the structural
proofs over expressions. Each denotation is literally the computation of the
`Ext`/`Ext9` semantics at the instruction's width. -/

/-- Value operators. Operands are read at the width `sz` (low bits) and the result is
zero-extended to 64 bits. -/
inductive EOp where
  /-- DIV/IDIV quotient of `a:b` (high:low) by `c` (`0` where `#DE`). -/
  | divq (sz : Sz) (signed : Bool)
  /-- DIV/IDIV remainder. -/
  | divr (sz : Sz) (signed : Bool)
  /-- MUL: the low half `ofNat (a * b)`. -/
  | mulLo (sz : Sz)
  /-- MUL: the high half of the unsigned product. -/
  | mulHi (sz : Sz)
  /-- IMUL (one operand): the low half of the signed product. -/
  | imulLo (sz : Sz)
  /-- IMUL (one operand): the high half. -/
  | imulHi (sz : Sz)
  /-- BSF: the index of the lowest set bit of `a` (meaningful for `a ≠ 0`). -/
  | bsf (sz : Sz)
  /-- BSR: the index of the highest set bit of `a`. -/
  | bsr (sz : Sz)
  /-- ADC (`sub = false`) / SBB: `a ± b ± carry`, carry-in `c ≠ 0`. -/
  | carry (sz : Sz) (sub : Bool)
  deriving DecidableEq, Repr

/-- Flags operators. -/
inductive FOp where
  /-- BSF/BSR on a nonzero source: `Ext9.scanFlags` (a constant). -/
  | scan
  /-- MUL: `mulFlags (high half ≠ 0)` of `a * b`. -/
  | mul (sz : Sz)
  /-- IMUL (one operand): `Ext9.imul1Flags a b`. -/
  | imul1 (sz : Sz)
  /-- ADC/SBB: `Ext9.carryFlags`. -/
  | carry (sz : Sz) (sub : Bool)
  deriving DecidableEq, Repr

/-- Check operators: a statement that stops the block on a condition of its operands. -/
inductive COp where
  /-- DIV/IDIV of `a:b` by `c` raises `#DE` (`Ext.divide` is `none`). -/
  | div (sz : Sz) (signed : Bool)
  /-- BSF/BSR of a zero source: `undefinedCondition .e` (`Ext9`'s choice). -/
  | nz (sz : Sz)
  deriving DecidableEq, Repr

def EOp.den : EOp → Word → Word → Word → Word
  | .divq sz sg, a, b, c =>
    match divide sz sg (a.setWidth sz.bits) (b.setWidth sz.bits) (c.setWidth sz.bits) with
    | some (q, _) => q.setWidth 64
    | none => 0
  | .divr sz sg, a, b, c =>
    match divide sz sg (a.setWidth sz.bits) (b.setWidth sz.bits) (c.setWidth sz.bits) with
    | some (_, r) => r.setWidth 64
    | none => 0
  | .mulLo sz, a, b, _ =>
    (BitVec.ofNat sz.bits ((a.setWidth sz.bits).toNat * (b.setWidth sz.bits).toNat)).setWidth 64
  | .mulHi sz, a, b, _ =>
    (BitVec.ofNat sz.bits ((a.setWidth sz.bits).toNat * (b.setWidth sz.bits).toNat /
      2 ^ sz.bits)).setWidth 64
  | .imulLo sz, a, b, _ => (Ext9.imulWide (a.setWidth sz.bits) (b.setWidth sz.bits)).1.setWidth 64
  | .imulHi sz, a, b, _ => (Ext9.imulWide (a.setWidth sz.bits) (b.setWidth sz.bits)).2.setWidth 64
  | .bsf sz, a, _, _ => (BitVec.ofNat sz.bits (Ext9.bsfIndex (a.setWidth sz.bits))).setWidth 64
  | .bsr sz, a, _, _ => (BitVec.ofNat sz.bits (Ext9.bsrIndex (a.setWidth sz.bits))).setWidth 64
  | .carry sz sub, a, b, c =>
    (Ext9.carryResult sub (a.setWidth sz.bits) (b.setWidth sz.bits) (c != 0)).setWidth 64

def FOp.den : FOp → Word → Word → Word → Flags
  | .scan, _, _, _ => Ext9.scanFlags
  | .mul sz, a, b, _ =>
    mulFlags (BitVec.ofNat sz.bits ((a.setWidth sz.bits).toNat * (b.setWidth sz.bits).toNat /
      2 ^ sz.bits) != 0#sz.bits)
  | .imul1 sz, a, b, _ => Ext9.imul1Flags (a.setWidth sz.bits) (b.setWidth sz.bits)
  | .carry sz sub, a, b, c =>
    Ext9.carryFlags sub (a.setWidth sz.bits) (b.setWidth sz.bits) (c != 0)

/-! ## Expressions -/

/-- Pure 64-bit expressions. A value of a narrower operation is held in the
low bits of a 64-bit word; operations say the width at which they read their
operands (`w`) and zero-extend their result. -/
inductive E where
  /-- A register's value at block entry. -/
  | reg (r : Reg)
  /-- RIP at block entry. -/
  | rip
  /-- The FS base. -/
  | fs
  /-- The result of the `i`-th value-producing statement of the block. -/
  | v (i : Nat)
  | imm (w : Word)
  | add (a b : E)
  | sub (a b : E)
  | shl (a : E) (k : Nat)
  /-- `(a.setWidth w).setWidth 64`. -/
  | zext (w : Nat) (a : E)
  /-- `(a.setWidth w).signExtend 64`. -/
  | sext (w : Nat) (a : E)
  /-- `AluOp.resultN op` at width `w`, zero-extended. -/
  | alu (w : Nat) (op : AluOp) (a b : E)
  | neg (w : Nat) (a : E)
  | not (w : Nat) (a : E)
  | mul (w : Nat) (a b : E)
  /-- `ShiftOp.result op` at width `w`, count `(c.setWidth 8).toNat % w`. -/
  | shift (w : Nat) (op : ShiftOp) (a c : E)
  /-- Replace the low `n.bits` bits of `old` by those of `new`. -/
  | merge (n : Narrow) (old new : E)
  /-- `if b ≠ 0 then x else y`. -/
  | sel (b x y : E)
  | bswap (sz : Sz) (a : E)
  | bitcount (op : BitCountOp) (w : Nat) (a : E)
  /-- All ones if bit `w-1` of `a` is set, else zero, at width `w` (CDQ/CQO). -/
  | signmask (w : Nat) (a : E)
  /-- The low (`hi = false`) or high half of an XMM register at block entry. -/
  | xmm (i : Fin 16) (hi : Bool)
  /-- An extension operator. -/
  | xop (o : EOp) (a b c : E)
  deriving DecidableEq, Repr, Inhabited

/-- Flag expressions: the `Flags` value an instruction leaves. -/
inductive F where
  | entry
  | alu (w : Nat) (op : AluOp) (a b : E)
  | logic (w : Nat) (a : E)
  /-- `logicFlagsN (a &&& b)` at width `w` (TEST). -/
  | test (w : Nat) (a b : E)
  | inc (w : Nat) (a : E) (old : F)
  | dec (w : Nat) (a : E) (old : F)
  | neg (w : Nat) (a : E)
  | imul (w : Nat) (a b : E)
  | shift (w : Nat) (op : ShiftOp) (a c : E) (old : F)
  | bitcount (op : BitCountOp) (w : Nat) (a : E)
  | bt (a c : E) (old : F)
  | undef
  /-- An extension flags operator. -/
  | xop (o : FOp) (a b c : E)
  deriving DecidableEq, Repr, Inhabited

/-- Effectful statements. -/
inductive Stmt where
  /-- Load `k` bytes (zero-extended); produces a value. -/
  | load (k : Nat) (addr : E)
  /-- Store the low `k` bytes of `val`. -/
  | store (k : Nat) (addr val : E)
  /-- The eight-byte store of PUSH and CALL. -/
  | push (addr val : E)
  /-- The eight-byte load of POP, RET and LEAVE; produces a value. -/
  | pop (addr : E)
  /-- Evaluate condition `c` on flags `f`: produces `1` or `0`, or stops with
  `undefinedCondition c`. -/
  | cond (c : Cond) (f : F)
  /-- UD2. -/
  | trap
  /-- The alignment check of an aligned SSE access: a data fault unless the
  address is a multiple of `k`. -/
  | align (a : E) (k : Nat)
  /-- An extension check: stops the block when `COp.fault` says so. -/
  | chk (o : COp) (a b c : E)
  deriving DecidableEq, Repr

/-- A lifted block. -/
structure Block where
  stmts : List Stmt
  /-- Changed registers, in register order; the others are unchanged. -/
  regs : List (Reg × E)
  flags : F
  rip : E
  /-- Changed XMM registers (low half, high half), in register order. -/
  xmm : List (Fin 16 × E × E) := []
  deriving DecidableEq, Repr

/-! ## Semantics -/

/-- The environment of a block run: the entry state, the values produced so
far and the current memory. -/
structure Env where
  s0 : State
  vals : List Word
  mem : Memory
  /-- The XMM registers at block entry. -/
  x0 : Xmm := fun _ => 0

def E.den (env : Env) : E → Word
  | .reg r => env.s0.read r
  | .rip => env.s0.rip
  | .fs => env.s0.fsBase
  | .v i => env.vals.getD i 0
  | .imm w => w
  | .add a b => a.den env + b.den env
  | .sub a b => a.den env - b.den env
  | .shl a k => a.den env <<< k
  | .zext w a => ((a.den env).setWidth w).setWidth 64
  | .sext w a => ((a.den env).setWidth w).signExtend 64
  | .alu w op a b => (AluOp.resultN op ((a.den env).setWidth w) ((b.den env).setWidth w)).setWidth 64
  | .neg w a => (0#w - (a.den env).setWidth w).setWidth 64
  | .not w a => (~~~((a.den env).setWidth w)).setWidth 64
  | .mul w a b => ((a.den env).setWidth w * (b.den env).setWidth w).setWidth 64
  | .shift w op a c =>
    (op.result ((a.den env).setWidth w) (((c.den env).setWidth 8).toNat % w)).setWidth 64
  | .merge n old new =>
    (old.den env &&& ~~~(narrowMask n)) ||| ((new.den env).setWidth n.bits).setWidth 64
  | .sel b x y => if b.den env ≠ 0 then x.den env else y.den env
  | .bswap sz a => (byteSwap sz ((a.den env).setWidth sz.bits)).setWidth 64
  | .bitcount op w a => (BitVec.ofNat w (op.count ((a.den env).setWidth w))).setWidth 64
  | .signmask w a =>
    (if ((a.den env).setWidth w).msb then BitVec.allOnes w else 0#w).setWidth 64
  | .xmm i hi => if hi then hi64 (env.x0 i) else lo64 (env.x0 i)
  | .xop o a b c => o.den (a.den env) (b.den env) (c.den env)

def F.den (env : Env) : F → Flags
  | .entry => env.s0.flags
  | .alu w op a b => AluOp.flagsN op ((a.den env).setWidth w) ((b.den env).setWidth w)
  | .logic w a => logicFlagsN ((a.den env).setWidth w)
  | .test w a b => logicFlagsN ((a.den env).setWidth w &&& (b.den env).setWidth w)
  | .inc w a old => incFlagsN ((a.den env).setWidth w) (old.den env)
  | .dec w a old => decFlagsN ((a.den env).setWidth w) (old.den env)
  | .neg w a => negFlagsN ((a.den env).setWidth w)
  | .imul w a b => imulFlags ((a.den env).setWidth w) ((b.den env).setWidth w)
  | .shift w op a c old =>
    op.flags ((a.den env).setWidth w) (((c.den env).setWidth 8).toNat % w) (old.den env)
  | .bitcount op w a => op.flags ((a.den env).setWidth w)
  | .bt a c old =>
    let o := old.den env
    { o with carry := some ((a.den env).getLsbD ((c.den env).toNat % 64)),
             overflow := none, sign := none, adjust := none, parity := none }
  | .undef => undefinedFlags
  | .xop o a b c => o.den (a.den env) (b.den env) (c.den env)

/-- Why a block run stopped early. -/
inductive Fault where
  | data
  | undef (c : Cond)
  | trap
  /-- `#DE`. -/
  | divide
  deriving DecidableEq, Repr

def Fault.toResult : Fault → Result
  | .data => .dataFault
  | .undef c => .undefinedCondition c
  | .trap => .trap
  | .divide => .divideError

def Fault.toX : Fault → XResult
  | .data => .dataFault
  | .undef c => .undefinedCondition c
  | .trap => .trap
  | .divide => .divideError

/-- When a check operator stops the block. -/
def COp.fault : COp → Word → Word → Word → Option Fault
  | .div sz sg, a, b, c =>
    match divide sz sg (a.setWidth sz.bits) (b.setWidth sz.bits) (c.setWidth sz.bits) with
    | some _ => none
    | none => some .divide
  | .nz sz, a, _, _ => if a.setWidth sz.bits = 0#sz.bits then some (.undef .e) else none

def Env.push (env : Env) (w : Word) : Env := { env with vals := env.vals ++ [w] }

def Stmt.run (env : Env) : Stmt → Except Fault Env
  | .load k a =>
    match loadN env.mem (a.den env) k with
    | none => .error .data
    | some w => .ok (env.push w)
  | .store k a x =>
    match storeN env.mem (a.den env) k (x.den env) with
    | none => .error .data
    | some m => .ok { env with mem := m }
  | .push a x =>
    match env.mem.writeBytes (a.den env).toNat (encodeWords [x.den env]) with
    | none => .error .data
    | some m => .ok { env with mem := m }
  | .pop a =>
    match (env.mem.readBytes (a.den env).toNat 8).bind wordOfBytes? with
    | none => .error .data
    | some w => .ok (env.push w)
  | .cond c f =>
    match c.eval (f.den env) with
    | none => .error (.undef c)
    | some b => .ok (env.push (if b then 1#64 else 0#64))
  | .trap => .error .trap
  | .align a k => if (a.den env).toNat % k = 0 then .ok env else .error .data
  | .chk o a b c =>
    match o.fault (a.den env) (b.den env) (c.den env) with
    | none => .ok env
    | some f => .error f

def runStmts : List Stmt → Env → Except Fault Env
  | [], env => .ok env
  | st :: rest, env =>
    match st.run env with
    | .error f => .error f
    | .ok env' => runStmts rest env'

/-- A register's final expression. -/
def Block.reg (b : Block) (r : Reg) : E := (b.regs.lookup r).getD (.reg r)

/-- An XMM register's final halves. -/
def Block.xreg (b : Block) (i : Fin 16) : E × E := (b.xmm.lookup i).getD (.xmm i false, .xmm i true)

/-- The final machine state a block describes, in the environment its
statements produced. -/
def Block.state (b : Block) (env : Env) : XState where
  core :=
    { regs := fun r => (b.reg r).den env
      rip := b.rip.den env
      flags := b.flags.den env
      fsBase := env.s0.fsBase }
  xmm := fun i => (b.xreg i).2.den env ++ (b.xreg i).1.den env

/-- Run a block from an entry state and memory. -/
def Block.run (b : Block) (s0 : XState) (mem : Memory) : XResult :=
  match runStmts b.stmts ⟨s0.core, [], mem, s0.xmm⟩ with
  | .error f => f.toX
  | .ok env => .ok (b.state env) env.mem

/-! ## The symbolic machine state and operand forms -/

/-- The symbolic machine state partway through a block. -/
structure SState where
  regs : Reg → E
  flags : F
  rip : E
  /-- The XMM registers, as (low half, high half). -/
  xmm : Fin 16 → E × E := fun i => (.xmm i false, .xmm i true)
  /-- The number of values produced so far. -/
  n : Nat

def SState.setReg (σ : SState) (r : Reg) (e : E) : SState :=
  { σ with regs := fun q => if q = r then e else σ.regs q }

/-- After a value-producing statement: its value is `.v σ.n`. -/
def SState.fresh (σ : SState) : SState := { σ with n := σ.n + 1 }

def addImm : E → Word → E
  | .add x (.imm a), k => .add x (.imm (a + k))
  | e, k => .add e (.imm k)

/-- The symbolic address of a memory operand; `nx` is the next RIP. -/
def sAddr (σ : SState) (nx : E) (m : Mem) : E :=
  let base := match m.base with
    | .reg r => σ.regs r
    | .none => .imm 0
    | .rip => nx
    | .fs => .fs
  let idx := match m.index with
    | none => .imm 0
    | some i => .shl (σ.regs i.reg) i.scale.toNat
  .add (.add base idx) (.imm (m.disp.signExtend 64))

/-- Symbolic `readRM`/`readNarrow` of `k` bytes. -/
def sRead (σ : SState) (nx : E) (k : Nat) : RM → List Stmt × E × SState
  | .reg r => ([], σ.regs r, σ)
  | .mem m => ([.load k (sAddr σ nx m)], .v σ.n, σ.fresh)

/-- Symbolic `writeRM`: a register gets the zero-extension, memory the low bytes. -/
def sWriteRM (σ : SState) (nx : E) (sz : Sz) (op : RM) (e : E) : List Stmt × SState :=
  match op with
  | .reg r => ([], σ.setReg r (.zext sz.bits e))
  | .mem m => ([.store sz.bytes (sAddr σ nx m) (.zext sz.bits e)], σ)

/-- Symbolic `writeNarrow`: a register keeps its other bits. -/
def sWriteN (σ : SState) (nx : E) (n : Narrow) (op : RM) (e : E) : List Stmt × SState :=
  match op with
  | .reg r => ([], σ.setReg r (.merge n (σ.regs r) e))
  | .mem m => ([.store n.bytes (sAddr σ nx m) (.zext n.bits e)], σ)

def nxOf (σ : SState) (len : Nat) : E := addImm σ.rip (BitVec.ofNat 64 len)

/-- Symbolic `aluStep`, retired. -/
def sAlu (σ : SState) (len : Nat) (sz : Sz) (op : AluOp) (dst : RM) (y : E) :
    List Stmt × SState :=
  let nx := nxOf σ len
  let r := sRead σ nx sz.bytes dst
  let fl : F := .alu sz.bits op r.2.1 y
  if op = .cmp then (r.1 ++ [], { r.2.2 with flags := fl, rip := nx })
  else
    let w := sWriteRM r.2.2 nx sz dst (.alu sz.bits op r.2.1 y)
    (r.1 ++ w.1, { w.2 with flags := fl, rip := nx })

/-- Symbolic PUSH of `val`. -/
def sPushStmt (σ : SState) (val : E) : Stmt := .push (.sub (σ.regs .rsp) (.imm 8#64)) val
def sPushState (σ : SState) : SState := σ.setReg .rsp (.sub (σ.regs .rsp) (.imm 8#64))

def sPopState (σ : SState) : SState := σ.fresh.setReg .rsp (.add (σ.regs .rsp) (.imm 8#64))

def sMov (σ : SState) (len : Nat) (sz : Sz) (dst : RM) (e : E) : List Stmt × SState :=
  let w := sWriteRM σ (nxOf σ len) sz dst e
  (w.1, { w.2 with rip := nxOf σ len })

def sMovN (σ : SState) (len : Nat) (n : Narrow) (dst : RM) (e : E) : List Stmt × SState :=
  let w := sWriteN σ (nxOf σ len) n dst e
  (w.1, { w.2 with rip := nxOf σ len })

/-- A register-only instruction: set `r` to `e`, retire. -/
def sSet (σ : SState) (len : Nat) (r : Reg) (e : E) : List Stmt × SState :=
  ([], { σ.setReg r e with rip := nxOf σ len })

/-- Read an r/m (`k` bytes), then set register `r` to `mk x`. -/
def sReadSet (σ : SState) (len : Nat) (op : RM) (k : Nat) (r : Reg) (mk : E → E) :
    List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) k op
  (rd.1 ++ [], { rd.2.2.setReg r (mk rd.2.1) with rip := nxOf σ len })

/-- An immediate at width `w`, as the 64-bit constant whose low `w` bits it is. -/
def immW (w : Nat) (b : BitVec w) : E := .imm (b.setWidth 64)

/-- A flags-only instruction with no memory access. -/
def sFlags (σ : SState) (len : Nat) (f : F) : List Stmt × SState :=
  ([], { σ with flags := f, rip := nxOf σ len })

/-- Read an r/m, then set register `r` to `mk x` and the flags to `fl x`. -/
def sReadSetF (σ : SState) (len : Nat) (op : RM) (k : Nat) (r : Reg) (mk : E → E) (fl : E → F) :
    List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) k op
  (rd.1 ++ [], { rd.2.2.setReg r (mk rd.2.1) with flags := fl rd.2.1, rip := nxOf σ len })

/-- Read an r/m, then set the flags only. -/
def sReadF (σ : SState) (len : Nat) (op : RM) (k : Nat) (fl : E → F) : List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) k op
  (rd.1 ++ [], { rd.2.2 with flags := fl rd.2.1, rip := nxOf σ len })

/-- Read-modify-write of an r/m at size `sz`, optionally setting flags. -/
def sRMW (σ : SState) (len : Nat) (sz : Sz) (dst : RM) (val : E → E) (fl : Option (E → F)) :
    List Stmt × SState :=
  let nx := nxOf σ len
  let rd := sRead σ nx sz.bytes dst
  let w := sWriteRM rd.2.2 nx sz dst (val rd.2.1)
  (rd.1 ++ w.1, { w.2 with flags := (fl.map fun f => f rd.2.1).getD w.2.flags, rip := nx })

/-! ## The symbolic instruction table -/

/-- The 8-bit source operand of an extension ALU form. -/
def Src8.sym (σ : SState) : Src8 → E
  | .reg r => σ.regs r
  | .imm b => .imm (b.setWidth 64)

/-- The shift count operand. -/
def countSym (σ : SState) : Count → E
  | .cl => σ.regs .rcx
  | .one => .imm 1#64
  | .imm n => .imm (n.setWidth 64)

/-- Bits 15:8 of a register, as the low byte of an expression. -/
def hiByte (a : E) : E := .shift 64 .shr a (.imm 8#64)

/-- Replace bits 15:8 of `old` by the low byte of `new`. -/
def setHiByte (old new : E) : E :=
  .alu 64 .or (.alu 64 .and old (.imm (~~~(0xFF00#64)))) (.shl (.zext 8 new) 8)

/-- Update one XMM register of a symbolic state. -/
def xsetS (x : Fin 16 → E × E) (d : Fin 16) (v : E × E) : Fin 16 → E × E :=
  fun i => if i = d then v else x i

/-- The alignment check of an SSE access, if it is an aligned form. -/
def alignChk (al : Bool) (a : E) : List Stmt := if al then [.align a 16] else []

/-- An immediate, sign-extended to `sz`, as a 64-bit constant. -/
def immSz (sz : Sz) (imm : BitVec 32) : E := .imm ((imm.signExtend sz.bits).setWidth 64)

/-- DIV/IDIV: read the divisor, check for `#DE`, write quotient and remainder. -/
def sDiv (σ : SState) (len : Nat) (sz : Sz) (sg : Bool) (src : RM) : List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) sz.bytes src
  let hi := σ.regs .rdx
  let lo := σ.regs .rax
  (rd.1 ++ [.chk (.div sz sg) hi lo rd.2.1],
    { (rd.2.2.setReg .rax (.xop (.divq sz sg) hi lo rd.2.1)).setReg .rdx
        (.xop (.divr sz sg) hi lo rd.2.1) with flags := .undef, rip := nxOf σ len })

/-- MUL (`signed = false`) / one-operand IMUL: `RDX:RAX := RAX * src`. -/
def sMul1 (σ : SState) (len : Nat) (signed : Bool) (sz : Sz) (src : RM) : List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) sz.bytes src
  let x := σ.regs .rax
  (rd.1 ++ [],
    { (rd.2.2.setReg .rax (.xop (if signed then .imulLo sz else .mulLo sz) x rd.2.1 (.imm 0))).setReg
        .rdx (.xop (if signed then .imulHi sz else .mulHi sz) x rd.2.1 (.imm 0)) with
      flags := .xop (if signed then .imul1 sz else .mul sz) x rd.2.1 (.imm 0),
      rip := nxOf σ len })

/-- BSF (`rev = false`) / BSR: read, stop on a zero source, write the index. -/
def sScan (σ : SState) (len : Nat) (rev : Bool) (sz : Sz) (dst : Reg) (src : RM) :
    List Stmt × SState :=
  let rd := sRead σ (nxOf σ len) sz.bytes src
  (rd.1 ++ [.chk (.nz sz) rd.2.1 (.imm 0) (.imm 0)],
    { rd.2.2.setReg dst (.xop (if rev then .bsr sz else .bsf sz) rd.2.1 (.imm 0) (.imm 0)) with
      flags := .xop .scan (.imm 0) (.imm 0) (.imm 0), rip := nxOf σ len })

/-- A 16-bit ALU step on `dst` with second operand `y` (CMP writes nothing). -/
def sAlu16 (σ : SState) (len : Nat) (op : AluOp) (dst : RM) (y : E) : List Stmt × SState :=
  let nx := nxOf σ len
  let rd := sRead σ nx 2 dst
  let fl : F := .alu 16 op rd.2.1 y
  if op = .cmp then (rd.1 ++ [], { rd.2.2 with flags := fl, rip := nx })
  else
    let w := sWriteN rd.2.2 nx .w dst (.alu 16 op rd.2.1 y)
    (rd.1 ++ w.1, { w.2 with flags := fl, rip := nx })

/-- One symbolic step; `none` for instructions the lifter does not handle. -/
def symStep (σ : SState) (i : LInstr) (len : Nat) : Option (List Stmt × SState) :=
  let nx := nxOf σ len
  match i with
  | .ext i =>
    match i with
    | .mov sz dst src => some (sMov σ len sz dst (σ.regs src))
    | .movI sz dst imm => some (sMov σ len sz dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .movI16 dst imm => some (sMovN σ len .w dst (.imm (imm.setWidth 64)))
    | .movI32 dst imm => some (sSet σ len dst (.imm (imm.setWidth 64)))
    | .movabs dst imm => some (sSet σ len dst (.imm imm))
    | .load sz dst src => some (sReadSet σ len (.mem src) sz.bytes dst (.zext sz.bits))
    | .store n dst src => some (sMovN σ len n dst (σ.regs src))
    | .movx sx sz n dst src => some (sReadSet σ len src n.bytes dst
        (fun e => if sx then .zext sz.bits (.sext n.bits e) else .zext sz.bits (.zext n.bits e)))
    | .movsxd dst src => some (sReadSet σ len src 4 dst (.sext 32))
    | .lea sz dst m => some (sSet σ len dst (.zext sz.bits (sAddr σ nx m)))
    | .alu sz op dst src => some (sAlu σ len sz op dst (σ.regs src))
    | .aluR sz op dst src =>
      if op = .cmp then some (sReadF σ len src sz.bytes (fun y => .alu sz.bits op (σ.regs dst) y))
      else some (sReadSetF σ len src sz.bytes dst (fun y => .alu sz.bits op (σ.regs dst) y)
        (fun y => .alu sz.bits op (σ.regs dst) y))
    | .aluI sz op dst imm => some (sAlu σ len sz op dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .aluI8 sz op dst imm => some (sAlu σ len sz op dst (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .aluA sz op imm => some (sAlu σ len sz op (.reg .rax) (.imm ((imm.signExtend sz.bits).setWidth 64)))
    | .test sz dst src => some (sReadF σ len dst sz.bytes (fun x => .test sz.bits x (σ.regs src)))
    | .testA sz imm =>
      some (sFlags σ len (.test sz.bits (σ.regs .rax) (.imm ((imm.signExtend sz.bits).setWidth 64))))
    | .incdec sz dec dst =>
      some (sRMW σ len sz dst (fun x => .alu sz.bits (if dec then .sub else .add) x (.imm 1#64))
        (some fun x => if dec then .dec sz.bits x σ.flags else .inc sz.bits x σ.flags))
    | .bswap sz dst => some (sSet σ len dst (.bswap sz (σ.regs dst)))
    | .unary sz .neg dst => some (sRMW σ len sz dst (.neg sz.bits) (some (.neg sz.bits)))
    | .unary sz .not dst => some (sRMW σ len sz dst (.not sz.bits) none)
    | .imul sz dst src => some (sReadSetF σ len src sz.bytes dst (.mul sz.bits (σ.regs dst))
        (.imul sz.bits (σ.regs dst)))
    | .shift sz op dst count =>
      some (sRMW σ len sz dst (fun x => .shift sz.bits op x (countSym σ count))
        (some fun x => .shift sz.bits op x (countSym σ count) σ.flags))
    | .cxd sz => some (sSet σ len .rdx (.signmask sz.bits (σ.regs .rax)))
    | .cxe .d => some (sSet σ len .rax (.zext 32 (.sext 16 (σ.regs .rax))))
    | .cxe .q => some (sSet σ len .rax (.sext 32 (σ.regs .rax)))
    | .bitcount op sz dst src => some (sReadSetF σ len src sz.bytes dst (.bitcount op sz.bits)
        (.bitcount op sz.bits))
    | .mov8 dst src => some (sReadSet σ len src 1 dst (.merge .b (σ.regs dst)))
    | .movI8 dst imm => some (sMovN σ len .b dst (.imm (imm.setWidth 64)))
    | .nop _ | .endbr64 => some ([], { σ with rip := nx })
    | .ud2 => some ([.trap], σ)
    | .jmp rel => some ([], { σ with rip := addImm nx (rel.signExtend 64) })
    | .jmp8 rel => some ([], { σ with rip := addImm nx (rel.signExtend 64) })
    | .jcc c rel =>
      some ([.cond c σ.flags], { σ.fresh with rip := .sel (.v σ.n) (addImm nx (rel.signExtend 64)) nx })
    | .jcc8 c rel =>
      some ([.cond c σ.flags], { σ.fresh with rip := .sel (.v σ.n) (addImm nx (rel.signExtend 64)) nx })
    | .setcc c dst =>
      let w := sWriteN σ.fresh nx .b dst (.v σ.n)
      some ([.cond c σ.flags] ++ w.1, { w.2 with rip := nx })
    | .call rel => some ([sPushStmt σ nx], { sPushState σ with rip := addImm nx (rel.signExtend 64) })
    | .ret => some ([.pop (σ.regs .rsp)], { sPopState σ with rip := .v σ.n })
    | .push src => some ([sPushStmt σ (σ.regs src)], { sPushState σ with rip := nx })
    | .pushRM src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [sPushStmt rd.2.2 rd.2.1], { sPushState rd.2.2 with rip := nx })
    | .pop dst => some ([.pop (σ.regs .rsp)], { (sPopState σ).setReg dst (.v σ.n) with rip := nx })
    | .leave =>
      let σt := σ.setReg .rsp (σ.regs .rbp)
      some ([.pop (σ.regs .rbp)], { (sPopState σt).setReg .rbp (.v σ.n) with rip := nx })
    -- Bir9: the `Ext` forms the base lifter rejected.
    | .div sz sg src => some (sDiv σ len sz sg src)
    | .mul sz src => some (sMul1 σ len false sz src)
    | .test8 dst src => some (sReadF σ len dst 1 (fun x => .test 8 x (σ.regs src)))
    | .testI8 dst imm => some (sReadF σ len dst 1 (fun x => .test 8 x (.imm (imm.setWidth 64))))
    | .testA8 imm => some (sFlags σ len (.test 8 (σ.regs .rax) (.imm (imm.setWidth 64))))
    | .cmpI8 dst imm => some (sReadF σ len dst 1 (fun x => .alu 8 .cmp x (.imm (imm.setWidth 64))))
    | .cmpA8 imm => some (sFlags σ len (.alu 8 .cmp (σ.regs .rax) (.imm (imm.setWidth 64))))
    | .cmov sz c dst src =>
      let rd := sRead σ nx sz.bytes src
      some (rd.1 ++ [.cond c σ.flags],
        { rd.2.2.fresh.setReg dst (.sel (.v rd.2.2.n) (.zext sz.bits rd.2.1) (.zext sz.bits (σ.regs dst)))
          with rip := nx })
  | .x i =>
    match i with
    | .alu8 op dst src =>
      let rd := sRead σ nx 1 dst
      let y := src.sym σ
      let fl : F := .alu 8 op rd.2.1 y
      if op = .cmp then some (rd.1 ++ [], { rd.2.2 with flags := fl, rip := nx })
      else
        let w := sWriteN rd.2.2 nx .b dst (.alu 8 op rd.2.1 y)
        some (rd.1 ++ w.1, { w.2 with flags := fl, rip := nx })
    | .test8 dst src => some (sReadF σ len dst 1 (fun x => .test 8 x (src.sym σ)))
    | .cmov sz c dst src =>
      let rd := sRead σ nx sz.bytes src
      some (rd.1 ++ [.cond c σ.flags],
        { rd.2.2.fresh.setReg dst (.sel (.v rd.2.2.n) (.zext sz.bits rd.2.1) (.zext sz.bits (σ.regs dst)))
          with rip := nx })
    | .bt dst src => some (sFlags σ len (.bt (σ.regs dst) (σ.regs src) σ.flags))
    | .jmpInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [], { rd.2.2 with rip := rd.2.1 })
    | .callInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [sPushStmt rd.2.2 nx], { sPushState rd.2.2 with rip := rd.2.1 })
    | .aluHi op r imm =>
      let x := hiByte (σ.regs r)
      let fl : F := .alu 8 op x (.imm (imm.setWidth 64))
      if op = .cmp then some ([], { σ with flags := fl, rip := nx })
      else some ([], { σ.setReg r (setHiByte (σ.regs r) (.alu 8 op x (.imm (imm.setWidth 64))))
        with flags := fl, rip := nx })
    | .testHi r imm =>
      some ([], { σ with flags := .test 8 (hiByte (σ.regs r)) (.imm (imm.setWidth 64)), rip := nx })
  | .n9 i =>
    match i with
    | .imulI sz dst src imm =>
      some (sReadSetF σ len src sz.bytes dst (fun x => .mul sz.bits x (immSz sz imm))
        (fun x => .imul sz.bits x (immSz sz imm)))
    | .imul1 sz src => some (sMul1 σ len true sz src)
    | .bsf sz dst src => some (sScan σ len false sz dst src)
    | .bsr sz dst src => some (sScan σ len true sz dst src)
    | .callInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [sPushStmt rd.2.2 nx], { sPushState rd.2.2 with rip := rd.2.1 })
    | .jmpInd src =>
      let rd := sRead σ nx 8 src
      some (rd.1 ++ [], { rd.2.2 with rip := rd.2.1 })
    | .pushI imm => some ([sPushStmt σ (.imm (imm.signExtend 64))], { sPushState σ with rip := nx })
    | .alu16 op dst src => some (sAlu16 σ len op dst (σ.regs src))
    | .alu16I op dst imm => some (sAlu16 σ len op dst (.imm (imm.setWidth 64)))
    | .alu16A op imm => some (sAlu16 σ len op (.reg .rax) (.imm (imm.setWidth 64)))
    | .test16 dst src => some (sReadF σ len dst 2 (fun x => .test 16 x (σ.regs src)))
    | .test16I dst imm => some (sReadF σ len dst 2 (fun x => .test 16 x (.imm (imm.setWidth 64))))
    | .test16A imm => some (sFlags σ len (.test 16 (σ.regs .rax) (.imm (imm.setWidth 64))))
    | .testI sz dst imm => some (sReadF σ len dst sz.bytes (fun x => .test sz.bits x (immSz sz imm)))
    | .adc .. | .adcR .. | .adcI .. | .alu16R .. | .testI8 .. | .bt .. | .repRet => none
  | .sse i =>
    match i with
    | .load128 al d m =>
      let a := sAddr σ nx m
      some (alignChk al a ++ [.load 8 a, .load 8 (.add a (.imm 8#64))],
        { σ.fresh.fresh with xmm := xsetS σ.xmm d (.v σ.n, .v (σ.n + 1)), rip := nx })
    | .store128 al m src =>
      let a := sAddr σ nx m
      some (alignChk al a ++ [.store 8 a (σ.xmm src).1, .store 8 (.add a (.imm 8#64)) (σ.xmm src).2],
        { σ with rip := nx })
    | .zero d => some ([], { σ with xmm := xsetS σ.xmm d (.imm 0, .imm 0), rip := nx })
    | .mov d src => some ([], { σ with xmm := xsetS σ.xmm d (σ.xmm src), rip := nx })

/-! ## Symbolic execution of a block -/

/-- Symbolically execute a straight-line list of instructions. -/
def symGo : List (LInstr × Nat) → SState → Option (List Stmt × SState)
  | [], σ => some ([], σ)
  | (i, len) :: rest, σ =>
    match symStep σ i len with
    | none => none
    | some (s1, σ1) =>
      match symGo rest σ1 with
      | none => none
      | some (s2, σ2) => some (s1 ++ s2, σ2)

/-- The sixteen registers, in hardware order. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def SState.init : SState := { regs := .reg, flags := .entry, rip := .rip, n := 0 }

/-- The changed entries of a total map, as an association list. -/
def changed {α β : Type} [DecidableEq β] (keys : List α) (f d : α → β) : List (α × β) :=
  keys.filterMap fun q => if f q = d q then none else some (q, f q)

def SState.toBlock (sts : List Stmt) (σ : SState) : Block :=
  { stmts := sts, regs := changed allRegs σ.regs .reg, flags := σ.flags, rip := σ.rip,
    xmm := changed (List.finRange 16) σ.xmm (fun i => (.xmm i false, .xmm i true)) }

/-- Lift a straight-line block into Bir. -/
def symExec (instrs : List (LInstr × Nat)) : Option Block :=
  (symGo instrs SState.init).map fun p => SState.toBlock p.1 p.2

/-! ## The simplifier and the lifter -/

def mkAdd : E → E → E
  | .imm a, .imm b => .imm (a + b)
  | e, .imm 0 => e
  | .imm 0, e => e
  | .add x (.imm a), .imm b => .add x (.imm (a + b))
  | x, y => .add x y

def mkSub : E → E → E
  | .imm a, .imm b => .imm (a - b)
  | e, .imm 0 => e
  | x, y => .sub x y

def mkShl : E → Nat → E
  | e, 0 => e
  | .imm a, k => .imm (a <<< k)
  | e, k => .shl e k

def mkZext (w : Nat) : E → E
  | .imm a => .imm ((a.setWidth w).setWidth 64)
  | e => if w = 64 then e else .zext w e

def mkAlu (w : Nat) (op : AluOp) (a b : E) : E :=
  if w = 64 then
    match op with
    | .add => mkAdd a b
    | .sub | .cmp => mkSub a b
    | _ => .alu 64 op a b
  else .alu w op a b

def E.simp : E → E
  | .add a b => mkAdd a.simp b.simp
  | .sub a b => mkSub a.simp b.simp
  | .shl a k => mkShl a.simp k
  | .zext w a => mkZext w a.simp
  | .sext w a => .sext w a.simp
  | .alu w op a b => mkAlu w op a.simp b.simp
  | .neg w a => .neg w a.simp
  | .not w a => .not w a.simp
  | .mul w a b => .mul w a.simp b.simp
  | .shift w op a c => .shift w op a.simp c.simp
  | .merge n a b => .merge n a.simp b.simp
  | .sel b x y => .sel b.simp x.simp y.simp
  | .bswap sz a => .bswap sz a.simp
  | .bitcount op w a => .bitcount op w a.simp
  | .signmask w a => .signmask w a.simp
  | .xop o a b c => .xop o a.simp b.simp c.simp
  | e => e

def F.simp : F → F
  | .entry => .entry
  | .alu w op a b => .alu w op a.simp b.simp
  | .logic w a => .logic w a.simp
  | .test w a b => .test w a.simp b.simp
  | .inc w a o => .inc w a.simp o.simp
  | .dec w a o => .dec w a.simp o.simp
  | .neg w a => .neg w a.simp
  | .imul w a b => .imul w a.simp b.simp
  | .shift w op a c o => .shift w op a.simp c.simp o.simp
  | .bitcount op w a => .bitcount op w a.simp
  | .bt a c o => .bt a.simp c.simp o.simp
  | .undef => .undef
  | .xop o a b c => .xop o a.simp b.simp c.simp

def Stmt.simp : Stmt → Stmt
  | .load k a => .load k a.simp
  | .store k a x => .store k a.simp x.simp
  | .push a x => .push a.simp x.simp
  | .pop a => .pop a.simp
  | .cond c f => .cond c f.simp
  | .trap => .trap
  | .align a k => .align a.simp k
  | .chk o a b c => .chk o a.simp b.simp c.simp

def Block.simp (b : Block) : Block where
  stmts := b.stmts.map Stmt.simp
  regs := b.regs.map fun p => (p.1, p.2.simp)
  flags := b.flags.simp
  rip := b.rip.simp
  xmm := b.xmm.map fun p => (p.1, p.2.1.simp, p.2.2.simp)

/-- Lift a block and simplify it. -/
def liftBlock (instrs : List (LInstr × Nat)) : Option Block := (symExec instrs).map Block.simp

/-! ## Listings checked against bytes -/

/-- An `Silmaril.X86.Ext.Index` with the `≠ rsp` side condition discharged by `decide`. -/
def ix (r : Reg) (scale : BitVec 2) (h : r ≠ .rsp := by decide) : Silmaril.X86.Ext.Index := ⟨r, scale, h⟩

/-- The decoder check for one listed instruction. -/
def LInstr.decodeOk (bytes : List Byte) : LInstr → Nat → Bool
  | .ext i, len => decide (Silmaril.X86.Ext.decode bytes = some (i, len))
  | .x _, len => bytes.length == len
  | .sse _, len => bytes.length == len
  | .n9 i, len => decide (Silmaril.X86.Ext9.decode bytes = some (.new i, len))

/-- Every instruction of a listing is checked against its bytes. -/
def listingOk : List (List Byte) → List (LInstr × Nat) → Bool
  | [], [] => true
  | b :: bs, (i, len) :: rest => i.decodeOk b len && listingOk bs rest
  | _, _ => false

/-- How many instructions of a listing are extension forms checked for their length only
(trust tier `ext+`: `LInstr.x`, `LInstr.sse`). `Ext9` forms are decoder-checked. -/
def extCount (l : List (LInstr × Nat)) : Nat := (l.filter fun p => match p.1 with
  | .ext _ | .n9 _ => false
  | _ => true).length

/-- How many instructions of a listing are `Ext9` forms (semantics: the handwritten
`Ext9.execNew`). -/
def n9Count (l : List (LInstr × Nat)) : Nat := (l.filter fun p => match p.1 with
  | .n9 _ => true
  | _ => false).length

/-! ## Machine states, and reading a block's final state -/

/-- A lifting result as a machine state (the XMM registers are dropped). -/
def ofX : XResult → Option MState
  | .ok s mem => some ⟨s.core, mem⟩
  | _ => none

/-- A listing as a partial map of machine states (XMM registers zero, then dropped). -/
def runL9 (L : List (LInstr × Nat)) (m : MState) : Option MState :=
  ofX (execBlock L ⟨m.core, fun _ => 0⟩ m.memory)

/-- A block as a partial map of machine states. -/
def runB9 (b : Block) (m : MState) : Option MState :=
  ofX (b.run ⟨m.core, fun _ => 0⟩ m.memory)

/-- A register's final expression by decidable equality (`Block.reg` uses `List.lookup`). -/
def lookupE (r : Reg) : List (Reg × E) → E
  | [] => .reg r
  | (a, e) :: rest => if r = a then e else lookupE r rest

/-- The `Ext9` instruction a listed instruction is (`Ext` and `Ext9` forms only). -/
def toX9 : LInstr → Option Ext9.Instr
  | .ext i => some (.ext8 (.base i))
  | .n9 i => some (.new i)
  | _ => none

/-- A listing as an `Ext9` listing (`none` if it has an `XInstr` or SSE entry). -/
def toX9L : List (LInstr × Nat) → Option (List (Ext9.Instr × Nat))
  | [] => some []
  | (i, l) :: rest =>
    match toX9 i, toX9L rest with
    | some j, some r => some ((j, l) :: r)
    | _, _ => none

end Silmaril.X86.Bir9
