module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Litmus.Test.Defs
public import Silmaril.X86.Concurrency.Cir.Refute.Defs

/-!
# Translation validation of spin loops into CIR

Compiled C channel code
waits with **spin loops**: `while (LD_ACQ(c) <cond>) ;` compiles (gcc and clang, `-O2`) to

```
L: mov  c, %r32          ; 8B /r, absolute [disp32]
   test %r32, %r32       ; or  cmp $k, %r32  (imm8)
   jcc  L                ; jne / je / jbe / jb, rel8
```

and the code between loops is the straight-line forms plus alignment `nop`s. The walk
has no branches. Rather than adding control flow to the instruction checker, a thread is cut into
**pieces** (`SPiece`), each its own small litmus thread:

* `seg its`: straight-line code, checked by the unchanged `walk`;
* `pad len`: one `nop` of `len` bytes, CIR `skip`;
* `spin len r m a c`: exactly the three instructions above, CIR
  `r = load.m a; loop n c (r = load.m a)` (`spinStmt`). The checker reads the register, the
  address, the immediate and the condition code from the decoded instructions and requires the
  certificate's condition `c` to be the one they mean (`spinCond`), the jump to go back to the
  load, and the load's address to be readable.

## The x86 semantics

`pexplore` runs the pieces in order from the thread's initial core. Straight pieces run under
`explore` (all branches of the symbolic extractor). A spin runs under `exploreT`, which is
`explore` except that a branch still running when the fuel is exhausted is **dropped** instead
of failing the whole extraction: spin loops have unboundedly long runs (a read may keep
returning the old value), so `explore` fails on them for every fuel. A spin is given fuel
`3 (n + 1)`, so `exploreT` gives exactly the runs that leave the loop after at most `n`
retries. The x86 behaviours of a spin test are therefore **bounded**: every spin retries at most
`n` times.

That running the pieces one after the other is running the whole function is argued, not proved
(as for the marked segments): every piece's instruction boundaries are those of the function,
the spin's jump goes back to its own first byte, and the pieces cover the code exactly.

## Tests

`STest`: locations, condition and recorded verdict (a litmus `Test`, threads unused), the threads,
one certificate per thread, the domain, the fuel of the straight pieces and the spin bound `n`.
`STest.prog` is the CIR program with spin bound `n`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Trace StepRec explore stepSym consStep readOk)
open Silmaril.Process (Region)
open Silmaril.X86.MemoryModel.Litmus (XTrace Test Cond Byte)

/-! ## Pieces and certificates -/

/-- A piece of a spin-validated thread. -/
inductive SPiece where
  /-- Straight-line code: one `Item` per instruction. -/
  | seg (its : List Item)
  /-- One `nop` of `len` bytes. -/
  | pad (len : Nat)
  /-- A spin loop of `len` bytes on register `r` reading address `a` with mode `m`; it loops
  while `c` holds. -/
  | spin (len : Nat) (r : Reg) (m : Mode) (a : Nat) (c : Expr)

/-- The byte length of a piece. -/
def SPiece.len : SPiece → Nat
  | .seg its => (its.map Item.len).sum
  | .pad len => len
  | .spin len .. => len

/-- **The CIR spin**: `r = load.m a; while (c) r = load.m a`, at most `n` retries. -/
def spinStmt (n : Nat) (r : Reg) (m : Mode) (a : Nat) (c : Expr) : Stmt :=
  .seq (.load r m 4 .wb (.lit a)) (.loop n c (.load r m 4 .wb (.lit a)))

/-- The CIR statements of a piece. -/
def SPiece.ops (n : Nat) : SPiece → List Stmt
  | .seg its => its.flatMap Item.ops
  | .pad _ => []
  | .spin _ r m a c => [spinStmt n r m a c]

/-- A spin certificate: the initial registers and the pieces. -/
structure SCert where
  pro : List (Reg × Nat)
  pieces : List SPiece

/-- **The CIR thread of a certificate**, with spin bound `n`. -/
def SCert.body (c : SCert) (n : Nat) : Stmt :=
  chain ((c.pro.map fun p => .assign p.1 (.lit p.2)) ++ c.pieces.flatMap (SPiece.ops n))

/-- Some straight piece reads memory (spins always read). -/
def SCert.reads (c : SCert) : Bool :=
  c.pieces.any fun
    | .seg its => its.any fun it => it.ops.any Stmt.reads
    | _ => true

/-! ## Threads and the x86 semantics -/

/-- A compiled thread: the relocated bytes of its function without the final `ret`. -/
structure SThread where
  base : Word
  code : List Byte
  regions : List Region
  init : State

/-- The code from offset `lo` to `hi`, as a litmus thread. -/
def SThread.sub (th : SThread) (lo hi : Nat) : XThread :=
  ⟨th.base + BitVec.ofNat 64 lo, (th.code.drop lo).take (hi - lo), th.regions, th.init⟩

/-- `explore`, except that a branch still running when the fuel runs out is dropped. -/
def exploreT (t : XThread) (dom : List Nat) : Nat → State → Option (List Trace)
  | fuel, s =>
    if s.rip = t.endRip then some [⟨[], s⟩]
    else
      match fuel with
      | 0 => some []
      | f + 1 =>
        match stepSym t dom s with
        | none => none
        | some outs =>
          (outs.mapM fun o => (exploreT t dom f o.2).map (consStep o.1 o.2)).map List.flatten

/-- One trace, then another. -/
def catTr (tr tr' : Trace) : Trace := ⟨tr.steps ++ tr'.steps, tr'.final⟩

/-- **The x86 semantics of a spin-cut thread**: the pieces from code offset `o`, in order;
straight pieces under `explore` with `fuel`, spins under `exploreT` with fuel `3 (n + 1)`. -/
def pexplore (th : SThread) (dom : List Nat) (fuel n : Nat) :
    Nat → List SPiece → State → Option (List Trace)
  | _, [], s => some [⟨[], s⟩]
  | o, p :: ps, s =>
    let t := th.sub o (o + p.len)
    let here := match p with
      | .spin .. => exploreT t dom (3 * (n + 1)) s
      | _ => explore t dom fuel s
    here.bind fun trs =>
      (trs.mapM fun tr =>
        (pexplore th dom fuel n (o + p.len) ps
          { tr.final with rip := th.base + BitVec.ofNat 64 (o + p.len) }).map
          (List.map (catTr tr))).map List.flatten

/-! ## The checker -/

/-- The meaning of `test r, r` (`k = none`) or `cmp $k, r` followed by `jcc` as a CIR loop
condition on the 64-bit register `r` (which holds a zero-extended 32-bit value). -/
def spinCond (cc : Silmaril.X86.Ext.Cond) (r : Reg) (k : Nat) : Option Expr :=
  match cc with
  | .ne => some (.bin .ne (.reg r) (.lit k))
  | .e => some (.bin .eq (.reg r) (.lit k))
  | .be => some (.bin .ltu (.reg r) (.lit (k + 1)))
  | .b => some (.bin .ltu (.reg r) (.lit k))
  | _ => none

/-- The compare of a spin at offset `o`: the register, the constant and the length. -/
def spinCmp (t : XThread) (o : Nat) (r : Reg) : Option (Nat × Nat) :=
  match fetchAt t o with
  | some (.open9 (.ext8 (.base (.test .d (.reg r') r''))), n) =>
    if r' = r ∧ r'' = r then some (0, n) else none
  | some (.open9 (.ext8 (.base (.aluI8 .d .cmp (.reg r') k))), n) =>
    if r' = r ∧ k.toNat < 128 then some (k.toNat, n) else none
  | _ => none

/-- **A spin piece checks**: load, compare, conditional jump back to the load, covering the
piece; the condition is the certificate's. -/
def spinOk (t : XThread) (r : Reg) (a : Nat) (c : Expr) : Bool :=
  match fetchAt t 0 with
  | some (.open9 (.ext8 (.base (.load .d r' mo))), 7) =>
    decide (r' = r) && decide (mo.base = .none) && decide (mo.index = none) &&
      decide ((mo.disp.signExtend 64).toNat = a) && readOk t.regions a 4 &&
      decide (t.code.length < 2 ^ 32) &&
      match spinCmp t 7 r with
      | some (k, m) =>
        match fetchAt t (7 + m) with
        | some (.open9 (.ext8 (.base (.jcc8 cc rel))), 2) =>
          decide (7 + m + 2 = t.code.length) &&
            decide (t.base + BitVec.ofNat 64 (7 + m + 2) + rel.signExtend 64 = t.base) &&
            decide (spinCond cc r k = some c)
        | _ => false
      | none => false
  | _ => false

/-- **A pad piece checks**: one `nop` covering the piece. -/
def padOk (t : XThread) : Bool :=
  match fetchAt t 0 with
  | some (.open9 (.ext8 (.base (.nop _))), n) => decide (0 < n ∧ n = t.code.length)
  | _ => false

/-- Walk the pieces from code offset `o`; the clobber set flows through, the fitting set
restarts empty after every piece. -/
def pwalk (th : SThread) : Nat → List SPiece → List Reg → List Reg → Option (List Reg)
  | o, [], K, _ => if o = th.code.length then some K else none
  | o, p :: ps, K, Z =>
    let t := th.sub o (o + p.len)
    if o + p.len ≤ th.code.length ∧ t.code.length < 2 ^ 64 then
      match p with
      | .seg its =>
        match walk t K Z 0 its with
        | some K' => pwalk th (o + p.len) ps K' []
        | none => none
      | .pad _ => if padOk t then pwalk th (o + p.len) ps K [] else none
      | .spin _ r _ a c => if spinOk t r a c then pwalk th (o + p.len) ps K [] else none
    else none

/-- **The spin checker**: the final clobber set, or `none`. -/
def stvRun (th : SThread) (c : SCert) : Option (List Reg) :=
  let pc : Cert := ⟨c.pro, []⟩
  if th.init.rip = th.base ∧ (allRegs.all fun r => th.init.read r == pc.proRegs r) then
    pwalk th 0 c.pieces [] (allRegs.filter fun r => decide ((pc.proRegs r).toNat < 2 ^ 32))
  else none

/-! ## Tests -/

/-- A translation-validated C test with spin loops. -/
structure STest where
  test : Test
  threads : List SThread
  certs : List SCert
  dom : List Nat
  fuel : Nat

/-- The certificate of thread `k`. -/
def STest.cert (c : STest) (k : Nat) : SCert := c.certs.getD k ⟨[], []⟩

/-- **The CIR program** of a test, with spin bound `n`. -/
def STest.prog (c : STest) (n : Nat) : Prog :=
  ⟨c.test.locs, c.threads.mapIdx fun k _ => ⟨(c.cert k).body n, false⟩⟩

/-- The x86 traces of every thread, spins retrying at most `n` times. -/
def STest.xtraces (c : STest) (n : Nat) : Option (List (List XTrace)) :=
  (c.threads.mapIdx fun k th =>
    pexplore th c.dom c.fuel n 0 (c.cert k).pieces th.init).mapM id

/-- **The x86 behaviours** of a test under `M`, every spin retrying at most `n` times. -/
def STest.XBehav (c : STest) (n : Nat) (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop)
    (f : Silmaril.X86.MemoryModel.Litmus.Final) : Prop :=
  ∃ T, c.xtraces n = some T ∧ Silmaril.X86.MemoryModel.Litmus.AxReach (c.prog n).memTest T M f

/-- The clobber sets. -/
def STest.clobs (c : STest) : Option (List (List Reg)) :=
  (c.threads.mapIdx fun k th => stvRun th (c.cert k)).mapM id

/-- One certificate per thread, every certificate checks, and no observed register is
clobbered. -/
def STest.tvOk (c : STest) : Bool :=
  c.threads.length == c.certs.length &&
    match c.clobs with
    | some Ks => condAvoids c.test.cond Ks
    | none => false

/-- The domain fits in 32 bits. -/
def STest.domOk (c : STest) : Bool := c.dom.all fun v => decide (v < 2 ^ 32)

/-- **The safety check of a test**: the certificates check, the domain fits, the bytes extract
(spin bound `0`), and the forced-cycle check (`Cir.Refute.safeCheck`) proves the condition for
every behaviour of the CIR program with spin bound `0`. -/
def STest.safeOk (c : STest) : Bool :=
  c.tvOk && c.domOk && (c.xtraces 0).isSome &&
    Silmaril.X86.Concurrency.Cir.Refute.safeCheck (c.prog 0).memTest ((c.prog 0).traces c.dom)
      c.test.cond

/-- **The witness check of a test**: the certificates check, the domain fits, the bytes
extract, and the CIR program with spin bound `0` has an explicit SC execution (traces `ks`)
satisfying the condition. -/
def STest.witnessOk (c : STest) (ks : List Nat) : Bool :=
  c.tvOk && c.domOk && (c.xtraces 0).isSome &&
    Silmaril.X86.Concurrency.Cir.Refute.witnessAuto (c.prog 0).memTest ((c.prog 0).traces c.dom)
      ks c.test.cond

end Silmaril.X86.Concurrency.Cir.Tv
