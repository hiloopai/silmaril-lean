module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Futex.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# Translation validation of compiled C threads with branches, loops and futex system calls

The C futex programs
loop (`while (flag == 0) futex_wait(...)`) and branch (a mutex's slow path), and they make raw
`syscall`s. The straight-line and marked-thread checkers do not apply. This module validates such
threads by
**bounded trace inclusion** instead: it computes every x86 trace of a thread up to an
instruction budget, computes the CIR thread's runs over the same value domain, and checks that
each x86 trace has the actions of some CIR run. The soundness argument is then a few lines
(`Cir.Tv.FTest.refines`): it needs no simulation proof, because the check *is* the inclusion.

## The x86 semantics of a thread (`sexplore`)

A thread is a litmus thread (`XThread`): the bytes of a whole C function at a base address, its
regions and its initial core. `sexplore` follows `explore` (`stepSym`: the memory forms,
and every register-only instruction, including `cmp`, `test`, `jcc` and `jmp`, by the
`Atomic9` executor), with three changes:

* **`ret` ends the thread** (a `C3` byte at `rip`), as a thread function's return ends the
  thread. The function may have several.
* **`syscall` is a futex call** (`0F 05` at `rip`, `futexOuts`). This is the **trusted
  system-call convention**, the analogue of the marker convention: with `rax = 202`, a null
  timeout `r10 = 0` and a 4-byte-aligned `rdi`, the operation `rsi mod 128` (the private flag
  `128` is ignored) is `FUTEX_WAIT` (`0`) or `FUTEX_WAKE` (`1`) on the word at `rdi`, with
  value `rdx mod 2 ^ 32`. Its memory actions are exactly CIR's lowering of the matching futex
  label (`Lab.acts`, see `Cir.Futex`): the futex model is stated once, in CIR. The result is in
  `rax`: `0` or `-EAGAIN` for a wait, any value of the domain for a wake (the number of woken
  waiters is not modelled). `rcx` gets the return address and `r11` is set to `0` (the kernel
  leaves the flags there; compiled code treats both as clobbered). Every other system call is
  unsupported (`none`).
* **Bounded runs**: a branch that needs more than `fuel` instructions, or more than `waits`
  futex waits, is **dropped**, not an error. So the x86 behaviours are those in which every
  thread finishes (or blocks) within `fuel` instructions and `waits` waits. The wait budget
  matches CIR's loop bounds for wait loops (a CIR `loop n` around a wait allows `n` waits); the
  instruction budget is a backstop for loops without system calls. An unsupported instruction
  still makes the whole exploration `none`.

With `blk`, a wait whose check saw the expected value may also **block for ever**: the trace
stops there with the actions of `fblock`.

## The check (`FTest`)

An `FTest` is a C test: locations, condition and recorded verdicts (a litmus `Test`), the x86
threads, the CIR program the C source stands for, a value domain, the instruction and wait
budgets, and whether threads may block. `FTest.allOk` checks:

* `tvOk`: the condition observes memory only, the program has the test's locations, the
  thread counts agree, the x86 traces exist,
  and **every x86 trace's actions (up to `normActs`) are the actions of a CIR trace of the
  same thread** over the same domain (with blocked prefixes if `blk`);
* `cirCheck`: the axiomatic enumerator on the CIR traces gives the recorded SC, TSO and XL
  verdicts, and some SC execution exists.

Where enumerating every combination of thread traces is too expensive, an `allowed` verdict is
proved from one combination (`witnessOk`), or from one combination and a schedule that names
the SC execution (`schedOk`), which is checked without any enumeration.

The CIR program is written from the C source, not derived from the bytes: the check compares
traces, so it does not care how the program was obtained. Registers are not compared (the
conditions observe memory only), so a CIR program may use any registers.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Trace StepRec stepSym consStep)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test Cond Atom Model outsBy AxReach Byte)

/-! ## The x86 semantics with futex system calls -/

/-- The code byte `k` bytes after `rip`. -/
def codeAt (t : XThread) (s : State) (k : Nat) : Option Byte := t.code[(s.rip - t.base).toNat + k]?

/-- A `ret` at `rip`. -/
def atRet (t : XThread) (s : State) : Bool := codeAt t s 0 == some 0xc3

/-- A `syscall` at `rip`. -/
def atSyscall (t : XThread) (s : State) : Bool := codeAt t s 0 == some 0x0f && codeAt t s 1 == some 0x05

/-- The core after a system call returning `v`. -/
def sysRet (s : State) (next v : Word) : State :=
  { ((s.write .rax v).write .rcx next).write .r11 0 with rip := next }

/-- `-EAGAIN` as a 64-bit word. -/
def negEagain : Word := 0 - BitVec.ofNat 64 eagain

/-- **The futex system call** (the trusted convention): its outcomes, each the memory actions,
the next core and whether the thread stops (blocks for ever), or `none` for an unsupported call.
The actions are CIR's lowering of the futex label. -/
def futexOuts (dom : List Nat) (blk : Bool) (s : State) (next : Word) :
    Option (List (List XAct × State × Bool)) :=
  let a := (s.read .rdi).toNat
  let op := (s.read .rsi).toNat % 128
  let e := (s.read .rdx).toNat % 2 ^ 32
  if s.read .rax = 202 ∧ s.read .r10 = 0 ∧ a % 4 = 0 then
    if op = 0 then
      some ((pick dom 4).flatMap fun seen =>
        if seen = e then
          ((qpick dom).map fun r => ((Lab.fwait a e seen r).acts, sysRet s next 0, false)) ++
            (if blk then [((Lab.fblock a e).acts, s, true)] else [])
        else [((Lab.fwait a e seen 0).acts, sysRet s next negEagain, false)])
    else if op = 1 then
      some ((qpick dom).flatMap fun q =>
        dom.map fun w => ((Lab.fwake a (s.read .rdx).toNat q).acts, sysRet s next (BitVec.ofNat 64 w), false))
    else none
  else none

/-- The system call at this core is a futex wait (`rsi mod 128 = 0`). -/
def isWait (s : State) : Bool := (s.read .rsi).toNat % 128 == 0

/-- **The bounded x86 semantics of a thread with futex calls**: every trace that ends (`ret`,
the end of the code, or blocking) within `fuel` instructions and `waits` futex waits; `none` if
some reachable instruction is unsupported. -/
def sexplore (t : XThread) (dom : List Nat) (blk : Bool) : Nat → Nat → State → Option (List Trace)
  | fuel, waits, s =>
    if s.rip = t.endRip ∨ atRet t s = true then some [⟨[], s⟩]
    else
      match fuel with
      | 0 => some []
      | f + 1 =>
        if atSyscall t s = true then
          if isWait s = true ∧ waits = 0 then some []
          else
            let w := if isWait s = true then waits - 1 else waits
            match futexOuts dom blk s (s.rip + 2) with
            | none => none
            | some outs =>
              (outs.mapM fun (o : List XAct × State × Bool) =>
                if o.2.2 then some [⟨[⟨o.1, o.2.1⟩], o.2.1⟩]
                else (sexplore t dom blk f w o.2.1).map (consStep o.1 o.2.1)).map List.flatten
        else
          match stepSym t dom s with
          | none => none
          | some outs =>
            (outs.mapM fun o => (sexplore t dom blk f waits o.2).map (consStep o.1 o.2)).map
              List.flatten

/-! ## Futex C tests -/

/-- A C test validated by bounded trace inclusion. `test` holds the locations, the condition
and the recorded verdicts (its `threads` are unused). -/
structure FTest where
  test : Test
  threads : List XThread
  prog : Prog
  dom : List Nat
  fuel : Nat
  waits : Nat
  blk : Bool

/-- The x86 traces of every thread. -/
def FTest.xtraces (c : FTest) : Option (List (List XTrace)) :=
  (c.threads.map fun t => sexplore t c.dom c.blk c.fuel c.waits t.init).mapM id

/-- The CIR traces of every thread (with blocked prefixes if threads may block). -/
def FTest.ctraces (c : FTest) : List (List XTrace) :=
  if c.blk then c.prog.btraces c.dom else c.prog.traces c.dom

/-- **The x86 behaviours** of a futex C test under `M`. -/
def FTest.XBehav (c : FTest) (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop)
    (f : Silmaril.X86.MemoryModel.Litmus.Final) : Prop :=
  ∃ T, c.xtraces = some T ∧ AxReach c.test T M f

/-- **The CIR behaviours** of a futex C test under `M`: `BBehavIn` if threads may block,
`BehavIn` otherwise (`Cir.Tv.FTest.cbehav_iff`, given `tvOk`, which checks that the program has
the test's locations). -/
def FTest.CBehav (c : FTest) (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop)
    (f : Silmaril.X86.MemoryModel.Litmus.Final) : Prop :=
  AxReach c.test c.ctraces M f

/-- The condition observes memory only. -/
def memOnly (cond : Cond) : Bool :=
  cond.atoms.all fun
    | .mem .. => true
    | .reg .. => false

/-- Every x86 trace has the actions of a CIR trace. -/
def inclB (X U : List XTrace) : Bool := X.all fun a => U.any fun b => normActs a.acts == b.acts

/-- **The translation-validation check**: memory-only condition, one CIR thread per x86 thread,
and bounded trace inclusion per thread. -/
def FTest.tvOk (c : FTest) : Bool :=
  memOnly c.test.cond && c.prog.locs == c.test.locs &&
    c.threads.length == c.prog.threads.length &&
    match c.xtraces with
    | some T => (T.zip c.ctraces).all fun p => inclB p.1 p.2
    | none => false

/-- Every CIR trace has the actions of an x86 trace (the converse of `inclB`). -/
def coverB (X U : List XTrace) : Bool := U.all fun b => X.any fun a => normActs a.acts == b.acts

/-- **The converse check**: memory-only condition, one CIR thread per x86 thread,
and every CIR trace of a thread is, up to `normActs`, the actions of a bounded x86 trace of the
same thread. With `tvOk` it makes the per-thread trace sets equal, so the bounded x86 behaviours
*are* the CIR behaviours (`Cir.Tv.FTest.realizes`): `allowed` verdicts transfer to the x86 code
too, and a `forbidden` verdict for the x86 code is not vacuous (an empty x86 trace set, from a
too small budget, passes `tvOk` but fails this check). -/
def FTest.coverOk (c : FTest) : Bool :=
  memOnly c.test.cond && c.threads.length == c.prog.threads.length &&
    match c.xtraces with
    | some T => (T.zip c.ctraces).all fun p => coverB p.1 p.2
    | none => false

/-- The recorded verdict of a model. -/
def FTest.verdict (c : FTest) : Model → Silmaril.X86.MemoryModel.Litmus.Verdict
  | .sc => c.test.sc.getD c.test.xl
  | .tso => c.test.tso.getD c.test.xl
  | .xl => c.test.xl

/-- **The CIR verdict checks**: the axiomatic enumerator gives the recorded SC, TSO and XL
verdicts over the CIR traces, and some SC execution exists. -/
def FTest.cirCheck (c : FTest) : Bool :=
  match c.test.axJudge c.ctraces with
  | some js =>
    c.verdict .sc == c.test.verdictOf (outsBy js Model.sc.sel) &&
      c.verdict .tso == c.test.verdictOf (outsBy js Model.tso.sel) &&
      c.verdict .xl == c.test.verdictOf (outsBy js Model.xl.sel) &&
      !(outsBy js Model.sc.sel).isEmpty
  | none => false

/-- Every check of a futex C test. -/
def FTest.allOk (c : FTest) : Bool := c.tvOk && c.cirCheck

/-- One CIR trace per thread: trace `ks[k]` of thread `k` (empty if out of range). -/
def FTest.pickT (c : FTest) (ks : List Nat) : List (List XTrace) :=
  (c.ctraces.zip ks).map fun p => (p.1[p.2]?).toList

/-- **An SC witness from one trace per thread**: the enumerator, run on trace `ks[k]` of each
thread only, finds an SC execution whose final state satisfies the witness. This is how an
`allowed` verdict (a bug the checker finds) is proved without enumerating every
combination. -/
def FTest.witnessOk (c : FTest) (ks : List Nat) : Bool :=
  ks.length == c.ctraces.length &&
    match c.test.axJudge (c.pickT ks) with
    | some js => c.test.verdictOf (outsBy js Model.sc.sel) == .allowed
    | none => false

/-- One CIR trace per thread: trace `ks[k]` of thread `k`. -/
def FTest.pickTr (c : FTest) (ks : List Nat) : List XTrace :=
  (c.ctraces.zip ks).filterMap fun p => p.1[p.2]?

/-- Set the coherence list of a cell. -/
def setCell (co : List ((Nat × Nat) × List Nat)) (cell : Nat × Nat) (ws : List Nat) :
    List ((Nat × Nat) × List Nat) :=
  (cell, ws) :: co.filter fun p => p.1 != cell

/-- Replay a schedule (a thread id per step) over the units `evs`: each read takes its source
from the last write of its cell so far, each write goes last in its cell's coherence order. -/
def schedGo (evs : List Silmaril.X86.MemoryModel.Axiomatic.Ev) :
    List Nat → List (List Nat) → List (Nat × Option Nat) → List ((Nat × Nat) × List Nat) →
      List (Nat × Option Nat) × List ((Nat × Nat) × List Nat)
  | [], _, rf, co => (rf, co)
  | t :: sch, rem, rf, co =>
    match rem.getD t [] with
    | [] => schedGo evs sch rem rf co
    | i :: is =>
      let e := evs.getD i Silmaril.X86.MemoryModel.Litmus.dummyEv
      let cell := (e.addr, e.size)
      let ws := (co.lookup cell).getD []
      schedGo evs sch (rem.set t is) (if e.isR then (i, ws.getLast?) :: rf else rf)
        (if e.isW then setCell co cell (ws ++ [i]) else co)

/-- The candidate execution of a schedule over a choice of traces. -/
def schedExec (trs : List XTrace) (sch : List Nat) : Silmaril.X86.MemoryModel.Axiomatic.Exec :=
  let evs := (Silmaril.X86.MemoryModel.Litmus.units trs).map Prod.fst
  let rem := (List.range trs.length).map fun t =>
    (List.range evs.length).filter fun i => (evs.getD i Silmaril.X86.MemoryModel.Litmus.dummyEv).tid == t
  let r := schedGo evs sch rem [] []
  Silmaril.X86.MemoryModel.Litmus.mkExec evs (Silmaril.X86.MemoryModel.Litmus.rmwPairs evs) r.1 r.2

/-- **An SC witness by schedule**: trace `ks[k]` of each thread and the interleaving `sch`
give a well-formed candidate whose reads return the traces' values, which is SC and whose final
state satisfies the witness. The schedule is only a hint: everything is checked. -/
def FTest.schedOk (c : FTest) (ks sch : List Nat) : Bool :=
  let trs := c.pickTr ks
  let x := schedExec trs sch
  trs.length == c.ctraces.length && x.Wf &&
    Silmaril.X86.MemoryModel.Litmus.readsOkB c.test x
      ((Silmaril.X86.MemoryModel.Litmus.units trs).map Prod.snd) &&
    decide x.Sc && c.test.witness.eval (Silmaril.X86.MemoryModel.Litmus.finalAx c.test trs x)

open Silmaril.X86.MemoryModel.Litmus (Verdict) in
/-- What a validated futex C test gives (`Cir.Tv.FTest.transfer_of_allOk`). -/
structure FTest.Transfer (c : FTest) : Prop where
  /-- **Refinement**: every bounded x86 behaviour is a CIR behaviour with the same memory. -/
  refines : ∀ (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop) f, c.XBehav M f →
    ∃ f', c.CBehav M f' ∧ f'.mem = f.mem ∧ c.test.witness.eval f' = c.test.witness.eval f
  /-- **The CIR verdicts** under SC, TSO and XL are the recorded ones. -/
  cir : ∀ M : Model, (c.verdict M).Holds c.test (c.CBehav M.Holds)
  /-- Some SC behaviour exists. -/
  sc_some : ∃ f, c.CBehav Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f
  /-- **Transfer**: every `forbidden` CIR verdict holds for the x86 code. -/
  x86_forbidden : ∀ M : Model, c.verdict M = .forbidden →
    Verdict.forbidden.Holds c.test (c.XBehav M.Holds)

end Silmaril.X86.Concurrency.Cir.Tv
