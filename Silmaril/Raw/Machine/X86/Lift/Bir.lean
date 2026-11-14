-- Imported from an earlier development
-- Source: Silmaril/X86/Lift/Bir.lean; sha256=77623508371e13fc03a4753454b98ec8fbaf4ac0f396da56f5c1d8a653ed2ad2
-- Reproduce with tools/mor/examples/import_x86_lift.rs; declaration namespaces retained.
module

public import Silmaril.X86.Ext.Semantics

/-!
# Bir: a first-order symbolic block IR for lifted machine code

`tools/x86-lift` transcribes compiled x86-64 into `Ext.Instr` listings; this
module is the *target* of the next step, lifting a basic block of such a
listing into a symbolic, first-order, SSA-shaped block whose semantics is
given here and whose relation to the machine is proved once and for all in
`Silmaril.X86.Lift.BirExec`.

A Bir block is

* a straight-line list of effectful statements (`Stmt`): loads, stores, the
  push/pop forms of the stack, condition evaluations and traps. Every
  statement that produces a value appends it to the block's value list, so a
  later expression names it as `E.v i`: this is SSA without φ-nodes, which a
  single block does not need;
* a final register map (`Block.regs`, sparse: unlisted registers are
  unchanged), final flags (`F`) and final RIP (`E`).

Expressions (`E`) are pure 64-bit terms over the block-entry state (`E.reg`,
`E.rip`, `E.fs`), earlier statement results (`E.v`) and constants. Their
operations are the *same functions* the machine semantics uses
(`AluOp.resultN`, `ShiftOp.result`, `logicFlagsN`, ...), at the width the
instruction used, so that a block's meaning is literally what `Ext.exec`
computes and the soundness proof is unfolding rather than arithmetic.
Readable forms (`rsp - 8` rather than `alu 64 sub rsp 8`) come from the
verified simplifier `E.simp` (`BirSimp`), never from the lifter.

## Extension instructions

`XInstr` adds the integer forms that `gcc -O2` emits and that the `Ext` model
does not yet contain: 8-bit ALU and TEST, CMOVcc, BT, and indirect JMP/CALL.
Their semantics is written here, from the Intel SDM, using `Ext`'s own
helpers; they are **not** in `Ext.decode`, so a listing that contains one is
transcribed by iced-x86 and is labelled with the trust tier `ext+` by the
lifter (see `docs/projects/wasm-wasi.md`). `LInstr` is the sum, and `LInstr.exec` on an
`Ext` instruction is `Ext.exec` exactly.
-/

@[expose] public section

namespace Silmaril.X86.Lift.Bir

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord wordOfBytes?)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## Extension instructions -/

/-- The second operand of an 8-bit ALU or TEST form. -/
inductive Src8 where
  | reg (r : Reg)
  | imm (b : BitVec 8)
  deriving DecidableEq, Repr

/-- Integer instructions outside `Ext.Instr` that compiled code needs. -/
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

`Ext.State` has no vector registers. Compiled C uses SSE registers even in
integer code, to zero and copy structures sixteen bytes at a time, so the
lifting machine is `XState`: an `Ext.State` together with the sixteen 128-bit
XMM registers. `Ext` and `XInstr` instructions leave the XMM registers alone;
`SInstr` are the moves. -/

/-- The sixteen XMM registers. -/
abbrev Xmm := Fin 16 → BitVec 128

def Xmm.set (x : Xmm) (d : Fin 16) (v : BitVec 128) : Xmm := fun i => if i = d then v else x i

/-- The machine state of the lifting layer. -/
structure XState where
  core : State
  xmm : Xmm

/-- `Ext.Result` over `XState`. -/
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
  | ext (i : Ext.Instr)
  | x (i : XInstr)
  | sse (i : SInstr)
  deriving DecidableEq, Repr

/-- Execute a listed instruction with its byte length. On `Ext` instructions
this is `Ext.exec`, with the XMM registers unchanged. -/
def LInstr.exec : LInstr → XState → Memory → Nat → XResult
  | .ext i, s, m, len => liftR s.xmm (Ext.exec i s.core m len)
  | .x i, s, m, len => liftR s.xmm (XInstr.exec i s.core m len)
  | .sse i, s, m, len => SInstr.exec i s m len

@[simp] theorem LInstr.exec_ext (i : Ext.Instr) (s : XState) (m : Memory) (len : Nat) :
    (LInstr.ext i).exec s m len = liftR s.xmm (Ext.exec i s.core m len) := rfl

/-- Run a straight-line list of instructions (each with its length): stop at
the first non-`ok` result. -/
def execBlock : List (LInstr × Nat) → XState → Memory → XResult
  | [], s, m => .ok s m
  | (i, len) :: rest, s, m =>
    match i.exec s m len with
    | .ok s' m' => execBlock rest s' m'
    | r => r

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

/-- Why a block run stopped early. -/
inductive Fault where
  | data
  | undef (c : Cond)
  | trap
  deriving DecidableEq, Repr

def Fault.toResult : Fault → Result
  | .data => .dataFault
  | .undef c => .undefinedCondition c
  | .trap => .trap

def Fault.toX : Fault → XResult
  | .data => .dataFault
  | .undef c => .undefinedCondition c
  | .trap => .trap

@[simp] theorem Fault.liftR_toResult (f : Fault) (x : Xmm) : liftR x f.toResult = f.toX := by
  cases f <;> rfl

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

theorem runStmts_append (l₁ l₂ : List Stmt) (env : Env) :
    runStmts (l₁ ++ l₂) env =
      match runStmts l₁ env with
      | .error f => .error f
      | .ok env' => runStmts l₂ env' := by
  induction l₁ generalizing env with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.cons_append, runStmts]
    cases st.run env with
    | error f => rfl
    | ok env' => exact ih env'

end Silmaril.X86.Lift.Bir
