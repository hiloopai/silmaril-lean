module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs

/-!
# Translation validation of futex code into CIR: CAS, locked ALU, early `ret`, `syscall`

The CFG checker
(`TvCfg.tvCfg`) validates spin code: register moves, plain and locked accesses, `test`/`cmp`
and `je`/`jne`. A futex mutex (Drepper, "Futexes Are Tricky") needs five more things, and this
module adds them **around** the checker, reusing its instruction table, certificate shapes and
proofs:

* `lock cmpxchg [m], r32`. Its CIR statement is `rmw rax _ 4 (cas rax) a r`. x86 writes `rax`
  only when the compare fails, while CIR's `rmw` always writes its destination. The two agree
  when `rax < 2^32` before the instruction, which is a **known register value** (below). The
  zero flag is `rax = v` after the step, where `v` is the expected value.
* `lock sub [m], imm`. x86 writes no register. CIR's `rmw` has a destination, so the
  certificate names a scratch register `d` among `rax`, `rcx`, `r11`, and `d` becomes **junk**
  (below). The zero flag is `(d - imm) mod 2^32 = 0`.
* `mov r64, r64` (`mov rax, r8`): an `assign`.
* `ret` in the middle of a function: the function has returned, and the continuation must be
  empty. `stepSym` has no step for `ret`, which pops the stack, so an x86 run stops there.
* `syscall` (`0F 05`), which the decoder does not know. It is read as a futex call by the
  **futex system-call convention** `SysStep`, which is an assumption about Linux, as
  `futexOuts` is. With `rax = 202` and `r10 = 0` (no timeout):
  - `rsi = 128` (`FUTEX_WAIT_PRIVATE`) is CIR's `futexWait rax [rdi] edx`;
  - `rsi = 129` (`FUTEX_WAKE_PRIVATE`) is `futexWake [rdi] rdx`.
  Its memory actions are CIR's lowering of the same label, so the kernel's check is a read of
  the word at an empty store buffer (`Lab.drains`). Afterwards `rax`, `rcx` and `r11` hold any
  values and the flags are arbitrary. Other register values have no step: a call the convention
  does not model stops the run, and the checker proves that the code makes no such call.

## Two facts per entry

An entry (`FEntry`) is the `TvCfg` entry plus two lists:

* `kn`: **known register values** of the CIR state. The checker propagates them through
  `assign` with `constE` (`xor r, r` is `0`) and forgets a register when it is written. The
  `syscall` and `cmpxchg` cases read them.
* `junk`: registers where the x86 core and the CIR state may **differ**, always a subset of
  `clob = [rax, rcx, r11]`. A futex call makes all three junk. An instruction may not read a
  junk register: every CIR statement and flag expression the checker uses must avoid them. A
  write makes the register agree again.

Soundness (`TvCfg.Fx.tvFx_sound`) then says: every x86 run is a CIR run of `c.body L` with the
same memory actions, and the final registers **agree outside `rax`, `rcx` and `r11`**. These are
the System V caller-saved registers that `syscall` clobbers.

## Why not a new CIR operation

The x86 register effects of `syscall` (`rcx := rip`, `r11 := rflags`, `rax := -errno`) are not
memory effects. CIR keeps its futex operations as they were, and the gap is in the
simulation relation, as junk registers.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.TvCfg.Fx

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Cir.Tv (XThread XMem fetchAt)
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Csl (TStep)

/-! ## Registers -/

/-- The registers a `syscall` may change: `rax` (the result), `rcx` and `r11`. -/
def clob : List Reg := [.rax, .rcx, .r11]

/-- The registers an expression reads. -/
def eregs : Expr → List Reg
  | .lit _ => []
  | .reg r => [r]
  | .bin _ a b => eregs a ++ eregs b

/-- The registers a leaf statement reads. -/
def rdRegs : Stmt → List Reg
  | .assign _ e => eregs e
  | .load _ _ _ _ a => eregs a
  | .store _ _ _ a v => eregs a ++ eregs v
  | .rmw _ _ _ op a arg =>
    eregs a ++ eregs arg ++ (match op with | .cas e => eregs e | _ => [])
  | .futexWait _ a v => eregs a ++ eregs v
  | .futexWake a n => eregs a ++ eregs n
  | _ => []

/-- The register a leaf statement writes. -/
def wrReg : Stmt → Option Reg
  | .assign d _ | .load d .. | .rmw d .. | .futexWait d .. => some d
  | _ => none

/-- None of the registers is junk. -/
def avoid (junk rs : List Reg) : Bool := rs.all fun r => !junk.contains r

/-! ## Known values -/

/-- A known value. -/
def lookup (kn : List (Reg × Word)) (r : Reg) : Option Word := (kn.find? (·.1 == r)).map (·.2)

/-- Forget a register. -/
def dropR (kn : List (Reg × Word)) (r : Reg) : List (Reg × Word) := kn.filter (·.1 != r)

/-- The value of an expression from known registers (`x ^ x` is `0` whatever `x` is). -/
def constE (kn : List (Reg × Word)) : Expr → Option Word
  | .lit v => some (BitVec.ofNat 64 v)
  | .reg r => lookup kn r
  | .bin o a b =>
    if o == .xor && a == b then some 0
    else
      match constE kn a, constE kn b with
      | some x, some y => some (o.eval x y)
      | _, _ => none

/-- The known values after a leaf statement. -/
def postKn (kn : List (Reg × Word)) (st : Stmt) : List (Reg × Word) :=
  match st with
  | .assign d e =>
    match constE kn e with
    | some v => (d, v) :: dropR kn d
    | none => dropR kn d
  | _ =>
    match wrReg st with
    | some d => dropR kn d
    | none => kn

/-- The junk registers after a leaf statement whose reads avoid them: a written register agrees
again. -/
def postJunk (junk : List Reg) (st : Stmt) : List Reg :=
  match wrReg st with
  | some d => junk.filter (· != d)
  | none => junk

/-! ## The instruction table -/

/-- What an instruction does, for the checker. -/
inductive FKind where
  /-- a `TvCfg` form (`TvCfg.kindOf`) -/
  | base (k : Kind)
  /-- `lock cmpxchg [a], src` (32 bits) -/
  | cas (a : Expr) (src : Reg)
  /-- `lock sub [a], imm` (32 bits) -/
  | lockSub (a : Expr) (imm : BitVec 32)
  /-- `mov d, src` (64 bits) -/
  | mov64 (d src : Reg)
  /-- `ret`: the function returns -/
  | ret

/-- The checker's view of a decoded instruction. -/
def fxKindOf : Atomic9.Instr → Option FKind
  | .new (.cmpxchg .d true (.mem m) src) => (addrX m).map fun a => .cas a src
  | .new (.lockAluI .d .sub m imm) => (addrX m).map fun a => .lockSub a imm
  | .open9 (.ext8 (.base (.mov .q (.reg d) src))) => some (.mov64 d src)
  | .open9 (.ext8 (.base .ret)) => some .ret
  | i => (kindOf i).map .base

/-- The CIR statement of `lock cmpxchg [a], src` (up to modes). -/
def casStmt (a : Expr) (src : Reg) : Stmt := .rmw .rax .rlx 4 (.cas (.reg .rax)) a (.reg src)

/-- The zero flag after `lock cmpxchg` with expected value `v`: the old value, now in `rax`,
was `v`. -/
def casZ (v : Word) : Expr := .bin .eq (.reg .rax) (.lit v.toNat)

/-- The value `lock sub` subtracts (the immediate, already sign-extended to 32 bits). -/
def subImm (imm : BitVec 32) : Nat := imm.toNat

/-- The CIR statement of `lock sub [a], imm` with scratch destination `d` (up to modes). -/
def subStmt (d : Reg) (a : Expr) (imm : BitVec 32) : Stmt :=
  .rmw d .rlx 4 (.op .sub) a (.lit (subImm imm))

/-- The zero flag after `lock sub`: the new value is `0`. -/
def subZ (d : Reg) (imm : BitVec 32) : Expr :=
  .bin .eq (mask32 (.bin .sub (.reg d) (.lit (subImm imm)))) (.lit 0)

/-- The CIR statement of a futex wait call. -/
def waitStmt : Stmt := .futexWait .rax (.reg .rdi) (.reg .rdx)

/-- The CIR statement of a futex wake call. -/
def wakeStmt : Stmt := .futexWake (.reg .rdi) (.reg .rdx)

/-- `syscall` (`0F 05`) at code offset `o`. -/
def isSysAt (t : XThread) (o : Nat) : Bool :=
  decide (o + 2 ≤ t.code.length) && (t.code.drop o).take 2 == [0x0f, 0x05]

/-! ## Certificates and the checker -/

/-- A simulation entry: the entry, the known CIR register values `kn` and the junk
registers `junk`, where x86 and CIR may differ. -/
structure FEntry where
  off : Nat
  cir : List Stmt
  zf : Option Expr := none
  kn : List (Reg × Word) := []
  junk : List Reg := []

/-- A futex-code certificate. -/
structure FCert where
  start : List Stmt
  entries : List FEntry

/-- **The CIR program** of a certificate, with every loop bounded by `L`. -/
def FCert.body (c : FCert) (L : Nat) : Stmt := setB L (Tv.chain c.start)

/-- Some entry is at `o` with the continuation `k` (up to loop bounds), the flag fact `z`, at
most the known values `kn` and at least the junk `junk`. -/
def hasEF (E : List FEntry) (o : Nat) (k : List Stmt) (z : Option Expr)
    (kn : List (Reg × Word)) (junk : List Reg) : Bool :=
  E.any fun e => e.off == o && lbeq (e.cir.map erase) (k.map erase) && e.zf == z &&
    e.kn.all (kn.contains ·) && junk.all (e.junk.contains ·)

/-- The successors of a conditional jump (as `jccOk`), keeping `kn` and `junk`. -/
def jccOkF (E : List FEntry) (ne : Bool) (tk ft : Nat) (z c : Expr) (kt kf : List Stmt)
    (kn : List (Reg × Word)) (junk : List Reg) : Bool :=
  (c == z && hasEF E (if ne then ft else tk) kt none kn junk &&
    hasEF E (if ne then tk else ft) kf none kn junk) ||
  (c == notE z && hasEF E (if ne then tk else ft) kt none kn junk &&
    hasEF E (if ne then ft else tk) kf none kn junk)

/-- Check a `TvCfg` instruction form at entry `e` (length `n`). -/
def chkBase (E : List FEntry) (e : FEntry) (n : Nat) : Kind → Bool
  | .op s =>
    match e.cir with
    | a :: rest =>
      sbeq a.demode s && avoid e.junk (rdRegs s) &&
        hasEF E (e.off + n) rest none (postKn e.kn s) (postJunk e.junk s)
    | [] => false
  | .flag z => avoid e.junk (eregs z) && hasEF E (e.off + n) e.cir (some z) e.kn e.junk
  | .skip => hasEF E (e.off + n) e.cir none e.kn e.junk
  | .jmp rel => hasEF E (jtarget e.off n rel) e.cir none e.kn e.junk
  | .jcc ne rel =>
    match e.zf, e.cir with
    | some z, a :: rest =>
      match branchOf a rest with
      | some (c, kt, kf) => jccOkF E ne (jtarget e.off n rel) (e.off + n) z c kt kf e.kn e.junk
      | none => false
    | _, _ => false

/-- Check a `syscall` at entry `e`: the convention's registers are known and not junk, the CIR
head is the matching futex statement, and afterwards `rax`, `rcx`, `r11` are junk. -/
def chkSys (E : List FEntry) (e : FEntry) : Bool :=
  match e.cir with
  | a :: rest =>
    avoid e.junk [.rax, .r10, .rsi, .rdi, .rdx] &&
      lookup e.kn .rax == some 202 && lookup e.kn .r10 == some 0 &&
      ((lookup e.kn .rsi == some 128 && sbeq a waitStmt) ||
        (lookup e.kn .rsi == some 129 && sbeq a wakeStmt)) &&
      hasEF E (e.off + 2) rest none (e.kn.filter fun p => !clob.contains p.1) clob
  | [] => false

/-- **Check one entry** against the code. -/
def chkEntryF (t : XThread) (E : List FEntry) (e : FEntry) : Bool :=
  e.junk.all (clob.contains ·) &&
  if e.off = t.code.length then e.cir.isEmpty
  else if isSysAt t e.off then (fetchAt t e.off).isNone && chkSys E e
  else
    match fetchAt t e.off with
    | none => false
    | some (i, n) =>
      decide (0 < n) &&
      match fxKindOf i with
      | none => false
      | some (.base k) => chkBase E e n k
      | some (.cas a src) =>
        match e.cir, lookup e.kn .rax with
        | h :: rest, some v =>
          decide (v.toNat < 2 ^ 32) && avoid e.junk (.rax :: src :: eregs a) &&
            sbeq h.demode (casStmt a src) &&
            hasEF E (e.off + n) rest (some (casZ v)) (dropR e.kn .rax)
              (postJunk e.junk (casStmt a src))
        | _, _ => false
      | some (.lockSub a imm) =>
        match e.cir with
        | h :: rest =>
          match h.demode with
          | .rmw d .rlx 4 (.op .sub) a' (.lit k) =>
            clob.contains d && a' == a && k == subImm imm && avoid e.junk (eregs a) &&
              hasEF E (e.off + n) rest (some (subZ d imm)) (dropR e.kn d)
                (if e.junk.contains d then e.junk else d :: e.junk)
          | _ => false
        | [] => false
      | some (.mov64 d src) =>
        match e.cir with
        | h :: rest =>
          sbeq h (.assign d (.reg src)) && avoid e.junk [src] &&
            hasEF E (e.off + n) rest none (postKn e.kn (.assign d (.reg src)))
              (postJunk e.junk (.assign d (.reg src)))
        | [] => false
      | some .ret => e.cir.isEmpty

/-- **The futex-code checker**: the code fits, every entry is in the code and checks, the
start entry `(0, start)` with nothing known and nothing junk is present, and the start is a list
of leaves. -/
def tvFx (t : XThread) (c : FCert) : Bool :=
  decide (t.code.length < 2 ^ 64) &&
    c.entries.all (fun e => decide (e.off ≤ t.code.length) && chkEntryF t c.entries e) &&
    hasEF c.entries 0 c.start none [] [] && c.start.all leafB

/-! ## The x86 side -/

/-- The labels a futex call may have from core `s`: a wait (`rsi = 128`) on the word at `rdi`
expecting the low 32 bits of `rdx`, which reads any 32-bit `seen` and any queue byte `r`; or a
wake (`rsi = 129`) of `rdx` waiters, which reads any queue byte. -/
def FutexLab (s : State) (l : Lab) : Prop :=
  (s.read .rsi = 128 ∧ ∃ seen r, seen < 2 ^ 32 ∧ r < 2 ^ 8 ∧
    l = .fwait (s.read .rdi).toNat ((s.read .rdx).toNat % 2 ^ 32) seen r) ∨
  (s.read .rsi = 129 ∧ ∃ q, q < 2 ^ 8 ∧ l = .fwake (s.read .rdi).toNat (s.read .rdx).toNat q)

/-- **The futex system-call convention** (an assumption about Linux, as `futexOuts`): a
`syscall` with `rax = 202` and `r10 = 0` is a futex call whose memory actions are CIR's lowering
of its label. It returns to the next instruction with any `rax`, `rcx`, `r11` and flags; every
other register is kept. -/
def SysStep (t : XThread) (s : State) (acts : List XAct) (s' : State) : Prop :=
  isSysAt t (s.rip - t.base).toNat = true ∧ s.read .rax = 202 ∧ s.read .r10 = 0 ∧
    ∃ (l : Lab) (va vc v11 : Word) (fl : Silmaril.X86.Flags), FutexLab s l ∧ acts = l.acts ∧
      s' = { (((s.write .rax va).write .rcx vc).write .r11 v11) with
        rip := s.rip + BitVec.ofNat 64 2, flags := fl }

/-- **One x86 step**: a step of `stepSym` (`XStep`) or a futex call. -/
def FStep (t : XThread) (s : State) (acts : List XAct) (s' : State) : Prop :=
  XStep t s acts s' ∨ SysStep t s acts s'

/-- A finite x86 run. -/
inductive FRun (t : XThread) : State → List (List XAct) → State → Prop
  | nil {s} : FRun t s [] s
  | cons {s acts s' rest s''} (h : FStep t s acts s') (tl : FRun t s' rest s'') :
      FRun t s (acts :: rest) s''

/-- The function has returned: `rip` is at the end of the code (its last `ret`) or at another
`ret`. -/
def Returned (t : XThread) (s : State) : Prop :=
  s.rip = t.endRip ∨ ∃ n, t.fetch s = some (.open9 (.ext8 (.base .ret)), n)

/-- Build an entry. -/
def fent (off : Nat) (cir : List Stmt) (zf : Option Expr := none) (kn : List (Reg × Word) := [])
    (junk : List Reg := []) : FEntry := ⟨off, cir, zf, kn, junk⟩

end Silmaril.X86.Concurrency.Cir.TvCfg.Fx
