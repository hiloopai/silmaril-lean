module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs

/-!
# CIR litmus tests: the checker and the tests

A CIR litmus test (`CTest`) is a litmus test (`Litmus.Test`:
locations, final condition, recorded SC/TSO/XL verdicts) together with CIR threads that replace
its machine code. The checker `CTest.check` reuses the candidate enumerator `Test.axJudge`
on the CIR traces over the test's value domain (`CTest.domain`) and compares its SC, TSO and XL
verdicts with the recorded ones; the verdict theorems are in `...Cir.Litmus.Thms`.

## The tests

Eight corpus tests, as CIR programs with the corpus's own locations, conditions and recorded
verdicts: `SB`, `SB+mfences`, `MP`, `LB`, `IRIW` (the corpus's `amd6`), `2+2W`,
`n6` and `RMW+lock-xadds`; and two more, `SB+lock-cmpxchgs` and `MP+mfences`.

Five CIR-only tests exercise the sync events, local blocks and flavours (verdicts stated from the
intended semantics, checked by the same enumerator):

* `MP+spawn`: the parent stores `x = 1` and then spawns the child, which reads `x`; reading `0`
  is forbidden;
* `MP+join`: the parent spawns a child that stores `x = 1`, joins it and reads `x`; reading `0`
  is forbidden;
* `MP+futex`: the writer stores `x = 1` then the futex word `f = 1`; the waiter's
  `futex_wait(f, 0)` returns `EAGAIN` (so it saw `f = 1`) and then it reads `x`; reading `0` is
  forbidden;
* `MP+local`: the data is written and read by opaque local blocks (`local(B)`), the flag by
  plain accesses; seeing the flag but old data is forbidden;
* `MP+nt`: `MP` with a non-temporal data store; seeing the flag but old data
  is allowed under XL and forbidden under TSO and SC.

## Cross-check against the bytes

`CTest.matchesX86`: for a corpus test, every thread's CIR traces and the traces the extractor
extracts from its
**bytes** have the same memory actions (kind, address, size, `locked`, flavour, bytes
read and written) and observed final registers, as sets. This is a per-test translation-validation
check of the CIR program against the x86 code (a Boolean fact proved by `decide`); its semantic
consequence (equal outcome sets) is not stated as a theorem, but both sides' verdicts are
proved.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-! ## Domains -/

/-- Add the written values, at most `k` times, stopping at a fixpoint. -/
def Prog.domIter (P : Prog) : Nat → List Nat → List Nat
  | 0, d => d
  | k + 1, d =>
    let d' := uniq (d ++ P.written d)
    if d'.length = d.length then d else P.domIter k d'

/-! ## CIR litmus tests -/

/-- A CIR litmus test: a litmus test (locations, condition, recorded verdicts) and CIR threads. -/
structure CTest where
  test : Test
  threads : List Thread

/-- The program of a CIR litmus test. -/
def CTest.prog (c : CTest) : Prog := ⟨c.test.locs, c.threads⟩

/-- The value domain: initial values and the condition's values, extended twice (or until a
fixpoint) by the values the runs write. The corpus domain iterates as many times as the test has
instructions; two rounds reach a fixpoint on every test here except `RMW+lock-xadds`, where
they give the corpus domain `[0, 1, 2]`. -/
def CTest.domain (c : CTest) : List Nat :=
  c.prog.domIter 2 (uniq ((c.test.locs.map Loc.init) ++ c.test.cond.atoms.map Atom.value))

/-- The recorded verdict of a model (`tso`/`sc` default to the XL verdict when not recorded). -/
def CTest.verdict (c : CTest) : Model → Verdict
  | .sc => c.test.sc.getD c.test.xl
  | .tso => c.test.tso.getD c.test.xl
  | .xl => c.test.xl

/-- **The CIR litmus check**: the axiomatic enumerator on the CIR traces gives the recorded
SC, TSO and XL verdicts, and some SC execution exists (so no verdict holds vacuously). -/
def CTest.check (c : CTest) : Bool :=
  match c.test.axJudge (c.prog.traces c.domain) with
  | some js =>
    c.verdict .sc == c.test.verdictOf (outsBy js Model.sc.sel) &&
      c.verdict .tso == c.test.verdictOf (outsBy js Model.tso.sel) &&
      c.verdict .xl == c.test.verdictOf (outsBy js Model.xl.sel) &&
      !(outsBy js Model.sc.sel).isEmpty
  | none => false

/-- The full views of a list of traces: every memory action (kind, address, size, `locked`,
**flavour**, bytes read and written) with the observed registers of thread `i`. (The compact
`Trace.view` omits the flavour, so the first version of `matchesX86` accepted a CIR program
with a non-temporal store against a plain `mov`; the flavour changes XL verdicts, `Lit.mpNt`.) -/
def viewsOf (t : Test) (i : Nat) (trs : List XTrace) : List (List XAct × List Nat) :=
  trs.map fun tr => (tr.acts, (t.obsRegs i).map fun r => (tr.final.read r).toNat)

/-- **Per-test translation validation against the bytes**: per thread, the CIR traces and the
traces extracted from the test's bytes have the same full views. -/
def CTest.matchesX86 (c : CTest) : Bool :=
  match c.test.traces with
  | some T =>
    T.length == c.threads.length &&
      ((List.range T.length).all fun i =>
        let a := viewsOf c.test i (T.getD i [])
        let b := viewsOf c.test i ((c.prog.traces c.domain).getD i [])
        a.all (memB · b) && b.all (memB · a))
  | none => false

/-! ## The tests -/

namespace Lit

open Stmt

/-- `x`, `y` (the corpus locations) and a futex word `f`. -/
abbrev x : Nat := 0x10000
abbrev y : Nat := 0x10040
abbrev f : Nat := 0x10080

/-- A plain 4-byte relaxed store of a constant. -/
def st (a v : Nat) : Stmt := .store .rlx 4 .wb (.lit a) (.lit v)

/-- A plain 4-byte relaxed load. -/
def ld (r : Reg) (a : Nat) : Stmt := .load r .rlx 4 .wb (.lit a)

/-- `mfence`. -/
def mf : Stmt := .fence .mfence

/-- A thread from a list of statements. -/
def th (l : List Stmt) : Thread := ⟨Stmt.block l, false⟩

/-- A spawned thread from a list of statements. -/
def sth (l : List Stmt) : Thread := ⟨Stmt.block l, true⟩

def sb : CTest := ⟨Corpus.«SB», [th [st x 1, ld .rax y], th [st y 1, ld .rax x]]⟩

def sbMfences : CTest :=
  ⟨Corpus.«SB+mfences», [th [st x 1, mf, ld .rax y], th [st y 1, mf, ld .rax x]]⟩

def mp : CTest := ⟨Corpus.«MP», [th [st x 1, st y 1], th [ld .rax y, ld .rbx x]]⟩

def mpMfences : CTest :=
  ⟨Corpus.«MP+mfences», [th [st x 1, mf, st y 1], th [ld .rax y, mf, ld .rbx x]]⟩

def lb : CTest := ⟨Corpus.«LB», [th [ld .rax x, st y 1], th [ld .rax y, st x 1]]⟩

def iriw : CTest :=
  ⟨Corpus.«amd6», [th [st x 1], th [st y 1], th [ld .rax x, ld .rbx y], th [ld .rcx y, ld .rdx x]]⟩

def w22 : CTest := ⟨Corpus.«2+2W», [th [st x 2, st y 1], th [st y 2, st x 1]]⟩

def n6 : CTest := ⟨Corpus.«n6», [th [st x 1, ld .rax x, ld .rbx y], th [st y 2, st x 2]]⟩

/-- `lock xadd %eax, x` with `rax = 1`. -/
def xadd : Thread := th [.assign .rax (.lit 1), .rmw .rax .sc 4 .fadd (.lit x) (.reg .rax)]

def rmwXadds : CTest := ⟨Corpus.«RMW+lock-xadds», [xadd, xadd]⟩

/-- `lock cmpxchg %ecx, a` with `rax = 0`, `rcx = 1`, then a load into `rbx`. -/
def casThen (a b : Nat) : Thread :=
  th [.rmw .rdx .sc 4 (.cas (.lit 0)) (.lit a) (.lit 1), ld .rbx b]

def sbCas : CTest := ⟨Corpus.«SB+lock-cmpxchgs», [casThen x y, casThen y x]⟩

/-- A litmus test shell for a CIR-only test over `x`, `y`, `f`. -/
def shell (name doc : String) (cond : Cond) (v : Verdict) : Test where
  name := name
  source := "cir"
  doc := doc
  locs := [⟨"x", x, 4, 0⟩, ⟨"y", y, 4, 0⟩, ⟨"f", f, 4, 0⟩]
  threads := []
  quant := .exists_
  cond := cond
  coverage := .tso
  tso := some v
  xl := v
  sc := some v
  basis := "CIR semantics"

def mpSpawn : CTest :=
  ⟨shell "MP+spawn" "store x, then spawn a reader of x" (.atom (.reg 1 .rax 32 0)) .forbidden,
    [th [st x 1, .spawn 1], sth [ld .rax x]]⟩

def mpJoin : CTest :=
  ⟨shell "MP+join" "spawn a writer of x, join it, read x" (.atom (.reg 0 .rax 32 0)) .forbidden,
    [th [.spawn 1, .join 1, ld .rax x], sth [st x 1]]⟩

def mpFutex : CTest :=
  ⟨shell "MP+futex" "store x, store f; futex_wait(f, 0) returns EAGAIN, then read x"
      (.and (.atom (.reg 1 .rax 64 eagain)) (.atom (.reg 1 .rbx 32 0))) .forbidden,
    [th [st x 1, st f 1, .futexWake (.lit f) (.lit 1)],
      th [.futexWait .rax (.lit f) (.lit 0), ld .rbx x]]⟩

/-- A local block writing `1` to `x`. -/
def putOne : Block where
  name := "put1"
  ins := []
  outs := [(x, 4)]
  rin := []
  rout := []
  spec := fun _ o => o = [1]
  dec := fun _ _ => inferInstance

/-- A local block copying `x` into `rbx`. -/
def getX : Block where
  name := "getx"
  ins := [(x, 4)]
  outs := []
  rin := []
  rout := [.rbx]
  spec := fun i o => o = i
  dec := fun _ _ => inferInstance

def mpLocal : CTest :=
  ⟨shell "MP+local" "MP whose data is written and read by local blocks"
      (.and (.atom (.reg 1 .rax 32 1)) (.atom (.reg 1 .rbx 32 0))) .forbidden,
    [th [.local putOne, st y 1], th [ld .rax y, .local getX]]⟩

/-- `MP` with a **non-temporal** data store: XL allows the stale read and TSO and SC
forbid it, so the weak part of XL is visible through CIR's flavours. -/
def mpNt : CTest :=
  ⟨{ shell "MP+nt" "MP whose data store is non-temporal"
      (.and (.atom (.reg 1 .rax 32 1)) (.atom (.reg 1 .rbx 32 0))) .forbidden with xl := .allowed },
    [th [.store .rlx 4 .nt (.lit x) (.lit 1), st y 1], th [ld .rax y, ld .rbx x]]⟩

/-- The re-expressed corpus tests. -/
def corpusTests : List CTest := [sb, sbMfences, mp, mpMfences, lb, iriw, w22, n6, rmwXadds, sbCas]

/-- The CIR-only tests. -/
def cirTests : List CTest := [mpSpawn, mpJoin, mpFutex, mpLocal, mpNt]

end Lit

end Silmaril.X86.Concurrency.Cir
