module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Defs

/-!
# Translation validation of x86 code with branches and loops into CIR

The straight-line checker
(`Cir.Tv.tvRun`) validates straight-line litmus threads against the extractor, whose trace
exploration needs every run to finish within a fuel bound. Compiled synchronisation code spins:
`spin_lock` has runs of every length, so no finite trace set describes it. This module validates
x86 code with **branches and loops** into **structured CIR** (`ite`, bounded `loop`) by a
**simulation certificate**, and states soundness against the small-step thread semantics
`Csl.TStep`, which every CIR-native machine (SC, TSO and XL store buffers) and the CSL logic use.

## The x86 side

`XStep t s acts s'`: one step of the symbolic step `stepSym` (the decoder and slice check of
`Thread.fetch`, `Atomic9.exec` for register-only forms, `memStep` for the memory forms) from core
`s`, with **any** value returned by a read. `stepSym_sound` ties each such step to the
sequential machine `Atomic9.step` on every memory that answers the reads. `XRun` is a finite
sequence of steps. The code is a function body up to (not including) its `ret`: the run has
returned when `rip` reaches `t.endRip`.

## The CIR side

`TRun s rs labs s' rs'`: a sequence of `Csl.TStep`s with the label trace `labs` (silent steps
dropped). A CIR state is seen through its **flat continuation** `Stmt.flat` (the `seq`-leaves
that are not `skip`, left to right), and loops are compared **up to their bounds**
(`Stmt.erase`). A CIR loop `loop n c b` is bounded; the program `GCert.body L` gives every loop
the bound `L`, and soundness says: every x86 run of `k` steps is a run of `body L` for every
`L ≥ k` (each loop iteration costs at least one x86 step, a conditional jump).

## The certificate

A `GCert` is a list of **entries** `(off, cir, zf)`: at x86 code offset `off`, the CIR
continuation is `cir` (up to loop bounds), and if `zf = some z` the x86 zero flag is the truth
value of the CIR expression `z` (`truthy (z.eval rs)`). The checker `tvCfg` decodes the
instruction at each entry with `fetchAt` and checks that every x86 successor is again an
entry (`hasE`):

The instructions (32-bit operands; `kindOf`), the CIR head of `cir` they need, and the next
entry:

* `mov r, imm32`, `mov r, r'`, `lea r, [m]`, `add/sub/and/or/xor r, r'` and `... r, imm8`:
  `assign r e` with the zero-extending expression `kindOf` computes; next `(off+n, rest, none)`;
* `mov [m], r`, `mov [m], imm32`, `mov r, [m]`, `xchg [m], r`, `lock xadd [m], r`: `store`,
  `load`, `rmw xchg`/`fadd` (any mode, write-back); next `(off+n, rest, none)`;
* `test r, r'`, `test al, imm8`, `cmp r, r'`, `cmp r, imm8`: no CIR effect; next
  `(off+n, cir, some z)`;
* `nop`, `pause`: no CIR effect; next `(off+n, cir, none)`;
* `jmp rel8`: no CIR effect; next `(target, cir, none)`;
* `je`/`jne rel8` with `zf = some z`: an `ite c s t` or `loop _ c b` head with `c = z` or
  `c = (z == 0)`; both successors.

Memory operands are `[base + index * 2^scale + disp32]` with a register or no base
(`addrX`); the CIR address adds the index to itself `scale` times. The walk ends at an entry
with `off = code.length` and an empty continuation.

## What is checked and what is not

Modes are compared away (`Stmt.demode`), as in the straight-line checker: the mode is an annotation
that does not change the lowered events. Only the forms in the table are accepted; anything
else (including flags read by anything but `je`/`jne`, 64-bit operands and calls) fails the
check.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem fetchAt binOf)
open Silmaril.X86.Concurrency.Cir.Csl (TStep)

/-! ## Flat continuations, bounds and equality -/

/-- The flat continuation of a statement: its non-`skip` leaves under `seq`, left to right. -/
def flat : Stmt → List Stmt
  | .skip => []
  | .seq s t => flat s ++ flat t
  | s => [s]

/-- Forget loop bounds. -/
def erase : Stmt → Stmt
  | .seq s t => .seq (erase s) (erase t)
  | .ite c s t => .ite c (erase s) (erase t)
  | .loop _ c b => .loop 0 c (erase b)
  | s => s

/-- Give every loop the bound `L`. -/
def setB (L : Nat) : Stmt → Stmt
  | .seq s t => .seq (setB L s) (setB L t)
  | .ite c s t => .ite c (setB L s) (setB L t)
  | .loop _ c b => .loop L c (setB L b)
  | s => s

/-- Every loop bound is at least `F`. -/
def bge (F : Nat) : Stmt → Prop
  | .seq s t | .ite _ s t => bge F s ∧ bge F t
  | .loop n _ b => F ≤ n ∧ bge F b
  | _ => True

/-- Boolean equality of statements without `local` blocks (a block is never equal to anything,
because its contract is a proposition). -/
def sbeq : Stmt → Stmt → Bool
  | .skip, .skip => true
  | .assign d e, .assign d' e' => d == d' && e == e'
  | .load d m sz fl a, .load d' m' sz' fl' a' =>
    d == d' && m == m' && sz == sz' && fl == fl' && a == a'
  | .store m sz fl a v, .store m' sz' fl' a' v' =>
    m == m' && sz == sz' && fl == fl' && a == a' && v == v'
  | .rmw d m sz op a arg, .rmw d' m' sz' op' a' arg' =>
    d == d' && m == m' && sz == sz' && op == op' && a == a' && arg == arg'
  | .fence k, .fence k' => k == k'
  | .futexWait d a v, .futexWait d' a' v' => d == d' && a == a' && v == v'
  | .futexWake a n, .futexWake a' n' => a == a' && n == n'
  | .spawn t, .spawn t' => t == t'
  | .join t, .join t' => t == t'
  | .seq s t, .seq s' t' => sbeq s s' && sbeq t t'
  | .ite c s t, .ite c' s' t' => c == c' && sbeq s s' && sbeq t t'
  | .loop n c b, .loop n' c' b' => n == n' && c == c' && sbeq b b'
  | _, _ => false

/-- Boolean equality of statement lists. -/
def lbeq : List Stmt → List Stmt → Bool
  | [], [] => true
  | s :: l, s' :: l' => sbeq s s' && lbeq l l'
  | _, _ => false

/-- A statement is a flat leaf: neither `skip` nor `seq`. -/
def leafB : Stmt → Bool
  | .skip | .seq .. => false
  | _ => true

/-! ## Expressions for x86 operands -/

/-- The low 32 bits, zero-extended. -/
def mask32 (e : Expr) : Expr := .bin .and e (.lit 0xffffffff)

/-- `r * 2^k`, as `k` doublings. -/
def idxE (r : Reg) : Nat → Expr
  | 0 => .reg r
  | k + 1 => .bin .add (idxE r k) (idxE r k)

/-- The CIR address of an x86 memory operand with a register base or no base:
`(base + index * 2^scale) + disp`. RIP-relative and FS operands are refused. -/
def addrX (a : XMem) : Option Expr :=
  let ie : Expr := match a.index with
    | none => .lit 0
    | some ix => idxE ix.reg ix.scale.toNat
  match a.base with
  | .none => some (.bin .add (.bin .add (.lit 0) ie) (.lit (a.disp.signExtend 64).toNat))
  | .reg r => some (.bin .add (.bin .add (.reg r) ie) (.lit (a.disp.signExtend 64).toNat))
  | _ => none

/-- `e == 0`: true exactly when `e` is false (`truthy`). -/
def notE (e : Expr) : Expr := .bin .eq e (.lit 0)

/-! ## The instruction table -/

/-- What an instruction does, for the checker. -/
inductive Kind where
  /-- one CIR statement (up to modes), then fall through; the flags are forgotten -/
  | op (s : Stmt)
  /-- fall through; the zero flag is now the truth value of `z` -/
  | flag (z : Expr)
  /-- fall through, no CIR effect (`nop`, `pause`) -/
  | skip
  /-- jump by `rel` from the next instruction, no CIR effect -/
  | jmp (rel : BitVec 8)
  /-- `je` (`ne = false`) or `jne` (`ne = true`) by `rel` -/
  | jcc (ne : Bool) (rel : BitVec 8)

/-- The checker's view of an instruction (32-bit forms only), or `none` if unsupported. -/
def kindOf : Atomic9.Instr → Option Kind
  | .open9 (.ext8 (.base (.movI32 d imm))) => some (.op (.assign d (.lit imm.toNat)))
  | .open9 (.ext8 (.base (.mov .d (.reg d) src))) => some (.op (.assign d (mask32 (.reg src))))
  | .open9 (.ext8 (.base (.lea .d d m))) => (addrX m).map fun e => .op (.assign d (mask32 e))
  | .open9 (.ext8 (.base (.alu .d op (.reg d) src))) =>
    if op = .cmp then some (.flag (.bin .eq (mask32 (.reg d)) (mask32 (.reg src))))
    else (binOf op).map fun o => .op (.assign d (mask32 (.bin o (.reg d) (.reg src))))
  | .open9 (.ext8 (.base (.aluI8 .d op (.reg d) imm))) =>
    if op = .cmp then
      some (.flag (.bin .eq (mask32 (.reg d)) (.lit (imm.signExtend 32).toNat)))
    else (binOf op).map fun o =>
      .op (.assign d (mask32 (.bin o (.reg d) (.lit (imm.signExtend 32).toNat))))
  | .open9 (.ext8 (.base (.test .d (.reg d) src))) =>
    some (.flag (.bin .eq (mask32 (.bin .and (.reg d) (.reg src))) (.lit 0)))
  | .open9 (.ext8 (.base (.testA8 imm))) =>
    some (.flag (.bin .eq (.bin .and (.reg .rax) (.lit imm.toNat)) (.lit 0)))
  | .open9 (.ext8 (.base (.mov .d (.mem a) src))) =>
    (addrX a).map fun e => .op (.store .rlx 4 .wb e (.reg src))
  | .open9 (.ext8 (.base (.movI .d (.mem a) imm))) =>
    (addrX a).map fun e => .op (.store .rlx 4 .wb e (.lit imm.toNat))
  | .open9 (.ext8 (.base (.load .d d a))) => (addrX a).map fun e => .op (.load d .rlx 4 .wb e)
  | .new (.xchg .d (.mem a) src) =>
    (addrX a).map fun e => .op (.rmw src .rlx 4 .xchg e (.reg src))
  | .new (.xadd .d true (.mem a) src) =>
    (addrX a).map fun e => .op (.rmw src .rlx 4 .fadd e (.reg src))
  | .open9 (.ext8 (.base (.nop _))) => some .skip
  | .new .pause => some .skip
  | .open9 (.ext8 (.base (.jmp8 rel))) => some (.jmp rel)
  | .open9 (.ext8 (.base (.jcc8 .e rel))) => some (.jcc false rel)
  | .open9 (.ext8 (.base (.jcc8 .ne rel))) => some (.jcc true rel)
  | _ => none

/-! ## Certificates and the checker -/

/-- A simulation entry: at code offset `off` the CIR continuation is `cir` (up to loop
bounds), and if `zf = some z` the zero flag is `truthy (z.eval rs)`. -/
structure Entry where
  off : Nat
  cir : List Stmt
  zf : Option Expr

/-- A simulation certificate: the entries, and the CIR program at offset `0`. -/
structure GCert where
  start : List Stmt
  entries : List Entry

/-- **The CIR program** of a certificate, with every loop bounded by `L`. -/
def GCert.body (c : GCert) (L : Nat) : Stmt := setB L (Tv.chain c.start)

/-- Some entry is at `o`, with the continuation `k` (up to loop bounds) and the flag fact
`z`. -/
def hasE (E : List Entry) (o : Nat) (k : List Stmt) (z : Option Expr) : Bool :=
  E.any fun e => e.off == o && lbeq (e.cir.map erase) (k.map erase) && e.zf == z

/-- The offset reached by a jump of `rel` from the instruction at `o` of length `n`. -/
def jtarget (o n : Nat) (rel : BitVec 8) : Nat :=
  (BitVec.ofNat 64 (o + n) + rel.signExtend 64).toNat

/-- The two successors of a CIR branch `a` with the rest `rest`: the continuation when its
condition is true, and when it is false; and the condition. -/
def branchOf (a : Stmt) (rest : List Stmt) : Option (Expr × List Stmt × List Stmt) :=
  match a with
  | .ite c s t => some (c, flat s ++ rest, flat t ++ rest)
  | .loop _ c b => some (c, flat b ++ a :: rest, rest)
  | _ => none

/-- The successors of a conditional jump (`je` if `ne = false`, `jne` if `ne = true`) to `tk`,
falling through to `ft`, on the zero flag `z`, against a CIR branch on `c` with continuations
`kt` (condition true) and `kf` (false): either `c` is `z` itself, or its negation `notE z`, and
the x86 successor of each truth value of `c` is an entry with the matching continuation. -/
def jccOk (E : List Entry) (ne : Bool) (tk ft : Nat) (z c : Expr) (kt kf : List Stmt) : Bool :=
  (c == z && hasE E (if ne then ft else tk) kt none && hasE E (if ne then tk else ft) kf none) ||
  (c == notE z && hasE E (if ne then tk else ft) kt none && hasE E (if ne then ft else tk) kf none)

/-- **Check one entry** against the code. -/
def chkEntry (t : XThread) (E : List Entry) (e : Entry) : Bool :=
  if e.off = t.code.length then e.cir.isEmpty
  else
    match fetchAt t e.off with
    | none => false
    | some (i, n) =>
      decide (0 < n) &&
      match kindOf i with
      | none => false
      | some (.op s) =>
        match e.cir with
        | a :: rest => sbeq a.demode s && hasE E (e.off + n) rest none
        | [] => false
      | some (.flag z) => hasE E (e.off + n) e.cir (some z)
      | some .skip => hasE E (e.off + n) e.cir none
      | some (.jmp rel) => hasE E (jtarget e.off n rel) e.cir none
      | some (.jcc ne rel) =>
        match e.zf, e.cir with
        | some z, a :: rest =>
          match branchOf a rest with
          | some (c, kt, kf) => jccOk E ne (jtarget e.off n rel) (e.off + n) z c kt kf
          | none => false
        | _, _ => false

/-- **The checker**: the code fits, every entry is in the code and checks, the start entry
`(0, start, none)` is present, and the start is a list of leaves. -/
def tvCfg (t : XThread) (c : GCert) : Bool :=
  decide (t.code.length < 2 ^ 64) &&
    c.entries.all (fun e => decide (e.off ≤ t.code.length) && chkEntry t c.entries e) &&
    hasE c.entries 0 c.start none && c.start.all leafB

/-! ## Runs -/

/-- **One x86 step**: a branch of the symbolic step for some read value. -/
def XStep (t : XThread) (s : State) (acts : List XAct) (s' : State) : Prop :=
  ∃ dom outs, Silmaril.X86.Litmus.stepSym t dom s = some outs ∧ (acts, s') ∈ outs

/-- A finite x86 run: the actions of each step. -/
inductive XRun (t : XThread) : State → List (List XAct) → State → Prop
  | nil {s} : XRun t s [] s
  | cons {s acts s' rest s''} (h : XStep t s acts s') (tl : XRun t s' rest s'') :
      XRun t s (acts :: rest) s''

/-- A finite CIR thread run (`Csl.TStep`s) with its label trace. -/
inductive TRun : Stmt → Regs → List Lab → Stmt → Regs → Prop
  | refl {s rs} : TRun s rs [] s rs
  | tau {s rs s₁ rs₁ l s₂ rs₂} (h : TStep s rs none s₁ rs₁) (tl : TRun s₁ rs₁ l s₂ rs₂) :
      TRun s rs l s₂ rs₂
  | lab {s rs a s₁ rs₁ l s₂ rs₂} (h : TStep s rs (some a) s₁ rs₁) (tl : TRun s₁ rs₁ l s₂ rs₂) :
      TRun s rs (a :: l) s₂ rs₂

/-- The CIR registers of an x86 core. -/
def regsOf (s : State) : Regs := fun r => s.read r

end Silmaril.X86.Concurrency.Cir.TvCfg
