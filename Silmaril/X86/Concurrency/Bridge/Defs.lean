module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Spin.Defs
public import Silmaril.X86.Litmus.Complete.Defs
public import Silmaril.X86.Pool.Defs
public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.X86.Litmus.Domain.Defs

/-!
# Bridges from the CIR front ends to the real machine: definitions

The front ends that validate x86 code into CIR (`tvRun`, `stvRun`, `tvCfg`, `tvFx`) are sound
against the **symbolic semantics** of one thread: `stepSym` steps (`TvCfg.XStep`), `explore`
traces, and for the pieces of a function run one
after the other (`Tv.pexplore`). The final report of the concurrency track listed four steps
from there to the real machine that were argued, not stated in Lean. This module states them;
`Bridge/Thms.lean` proves what is provable now and the conditional corollaries.

1. **Concurrent x86 runs to CIR behaviours** (`Task.tsoRunCir`, PROVED). A run of the
   byte-granular TSO pool (`X86.Pool.TsoReach`) over the real machine `Atomic9.step`
   (`X86.Pool.atomic9Ev`), from a test memory (`TestMem`) to a drained state where every
   thread has finished, ends in a CIR behaviour of the validated test's program, when the
   test's condition observes only initialised bytes (`CondInit`; without it the statement is
   false, `tsoRunCirAsStated`) and its accesses are cell accesses (`cellsB`; with
   the per-thread `CellsOk` instead the statement is false, `tsoRunCirCells`).
2. **The front ends against the real step.** Proved at the level of one step
   (`xstep_of_step` in `Bridge/Thms.lean`): a real `Atomic9.step` from a core where the
   symbolic step is defined, on a backed memory (`Backed`), is a branch of `stepSym`, so a real
   run (`A9Run`, with interference) is an `XRun`. That the symbolic step is defined wherever
   the real step succeeds on the code a checker accepted (`Task.tvCfgDefined`,
   `Task.tvFxDefined`) is PROVED (`tvCfgDefined_holds`, `tvFxDefined_holds`).
3. **The pieces compose**. Proved in both directions: every trace of `pexplore` replays
   as one trace of the whole function (`whole`) on `Atomic9.step` (`pexplore_replays`), and
   every domain-bounded run of the whole function is a trace of the pieces for some spin bound
   (`Task.piecesComplete`, proved: `piecesComplete_holds`; restated with
   `run ≠ [] ∨ length < 2 ^ 64`, see the Task).
4. **Calls** (`Task.callRet`, PROVED): a `call rel32` to a function body that
   `tvCfg` validates, the body, and the body's `ret`, are on the real machine the push of the
   return address, the body's CIR run, and the pop. The caller checker `ltv` (a caller cut at
   its call sites, linked with its callees' certificates) and its real runs `LRun`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge

open Silmaril.X86 (State Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded)

open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep Answers applyWrites stepSym DomRun Trace)
open Silmaril.X86.MemoryModel.Litmus (XAct Test Final)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (XThread TvTest SThread SCert stvRun pexplore fetchAt)
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (FCert tvFx FRun SysStep Returned isSysAt)
open Silmaril.X86.Pool (TPool TsoReach Drained atomic9Ev)

/-! ## Gap 2: the front ends against the real step -/

/-- **Mapped readable bytes are backed**: every address the mapping list lets a load read has
a byte. Process memories built by a loader have this property (mapped pages are filled); it is
the one assumption the step-level bridge needs about memory, since `Memory.readBacking` fails
on a missing byte. -/
def Backed (m : Memory) : Prop := ∀ a, m.permits .read a = true → (m.bytes.get? a).isSome = true

/-- **A real run of a thread** on `Atomic9.step`, with interference: before each step the
memory may be any backed memory with the thread's regions and code (other threads may have
changed it); the thread has not finished (`rip ≠ endRip`); the step goes to the recorded core
and memory. As `DomRun`, but without the value domain. -/
inductive A9Run (t : XThread) : State → List SeqStep → State → Prop
  | nil (s : State) : A9Run t s [] s
  | cons (s : State) (q : SeqStep) (rest : List SeqStep) (s' : State)
      (hne : s.rip ≠ t.endRip) (hR : q.pre.regions = t.regions)
      (hl : Loaded q.pre t.base t.code) (hb : Backed q.pre)
      (hs : Atomic9.step ⟨s, q.pre⟩ = some ⟨q.post, q.mem⟩)
      (tail : A9Run t q.post rest s') : A9Run t s (q :: rest) s'

/-- The step's actions are those of a real step: the memory before it answers the reads, and
the writes give the memory after it. -/
def ActsOk (acts : List XAct) (q : SeqStep) : Prop :=
  Answers q.pre acts ∧ applyWrites q.pre acts = some q.mem

/-- The symbolic step is defined at `s` (for some value domain; whether it is defined does
not depend on the domain, `stepSym_dom`). -/
def SymDefined (t : XThread) (s : State) : Prop :=
  ∃ dom outs, stepSym t dom s = some outs

/-- **The symbolic step is defined on validated code wherever the real step succeeds**. Take a
thread whose code `tvCfg` accepts, any start core with `rip = base`, and a core
`s` that an `XRun` reaches from it and that has not finished. If `Atomic9.step` succeeds from
`s` on some memory with the thread's regions and code, then `stepSym` is defined at `s`.

With `xstep_of_step` (proved) this makes every real run of the code an `XRun`, so `tvCfg_steps`
applies to the real machine: `tvCfg_real` in `Bridge/Thms.lean`.

PROVED: `tvCfgDefined_holds` in `Bridge/Thms.lean`, following the plan below; step (3)
uses the converse of the listing law (`Atomic9.exec_of_step_base`, `exec_of_step_new`) to get
the executor's `.ok` from the real step.

Plan: (1) the reachable cores sit at entries (the simulation invariant `Inv` of
`tvCfg_steps`' proof, `Proofs/Machine/Concurrency/Cir/TvCfg/Sound.lean`, moved to the header); so `fetchAt t o` decodes an instruction
of a kind `kindOf` accepts; (2) for the register kinds and jumps, `atomic9Accesses` is inert and
`Atomic9.exec` on `Thread.frame` is `.ok` because it is on the real memory (locality,
`atomic9_local`, with empty read and write sets, as `inert_sound`); (3) for the memory
kinds, `memStep` is `none` only if `readOk`/`writeOk` fails on the regions, and then the real
step faults (unfold `loadN`/`storeN`/the locked forms, as `memStep_sound` does in the
other direction). -/
def Task.tvCfgDefined : Prop :=
  ∀ (t : XThread) (c : GCert), tvCfg t c = true →
    ∀ (s₀ s : State) (acc : List (List XAct)), s₀.rip = t.base → XRun t s₀ acc s →
      s.rip ≠ t.endRip →
      ∀ (m : Memory) (s' : State) (m' : Memory), m.regions = t.regions → Loaded m t.base t.code →
        Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩ → SymDefined t s

/-- An observed step of a futex thread: a machine step, or a futex call with its CIR
actions and the core after it (the kernel is not modelled by `Atomic9.step`; `SysStep`
is the convention). -/
inductive FObs where
  | mach (q : SeqStep)
  | sys (acts : List XAct) (post : State)

/-- The actions of an x86 step match an observed step. -/
def FObs.Ok (acts : List XAct) : FObs → Prop
  | .mach q => ActsOk acts q
  | .sys acts' _ => acts = acts'

/-- **A real run of a futex thread**: machine steps as in `A9Run` (not at a `syscall`, the
function not returned), and futex calls by the convention `SysStep`. -/
inductive A9FRun (t : XThread) : State → List FObs → State → Prop
  | nil (s : State) : A9FRun t s [] s
  | mach (s : State) (q : SeqStep) (rest : List FObs) (s' : State)
      (hne : ¬ Returned t s) (hsys : isSysAt t (s.rip - t.base).toNat = false)
      (hR : q.pre.regions = t.regions) (hl : Loaded q.pre t.base t.code) (hb : Backed q.pre)
      (hs : Atomic9.step ⟨s, q.pre⟩ = some ⟨q.post, q.mem⟩)
      (tail : A9FRun t q.post rest s') : A9FRun t s (.mach q :: rest) s'
  | sys (s : State) (acts : List XAct) (s₁ : State) (rest : List FObs) (s' : State)
      (h : SysStep t s acts s₁) (tail : A9FRun t s₁ rest s') :
      A9FRun t s (.sys acts s₁ :: rest) s'

/-- **The symbolic step is defined on validated futex code wherever the real step succeeds**: as
`Task.tvCfgDefined`, for `tvFx` and its runs `FRun`, at a core that has not returned
and is not at a `syscall`.

Plan: as `Task.tvCfgDefined`, over the entries (`FEntry`); the extra kinds are `lock cmpxchg`,
`lock sub` (memory forms of `memStep`) and `mov r64, r64` (inert). PROVED:
`tvFxDefined_holds`; `ret` is excluded by `¬ Returned`. -/
def Task.tvFxDefined : Prop :=
  ∀ (t : XThread) (c : FCert), tvFx t c = true →
    ∀ (s₀ s : State) (acc : List (List XAct)), s₀.rip = t.base → FRun t s₀ acc s →
      ¬ Returned t s → isSysAt t (s.rip - t.base).toNat = false →
      ∀ (m : Memory) (s' : State) (m' : Memory), m.regions = t.regions → Loaded m t.base t.code →
        Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩ → SymDefined t s

/-! ## Gap 3: the pieces of a spin-cut function compose -/

/-- The whole function of a spin-cut thread as one thread. -/
def whole (th : SThread) : XThread := ⟨th.base, th.code, th.regions, th.init⟩

/-- **Every domain-bounded run of the whole function is a trace of its pieces** (the
complete direction; the sound direction is `pexplore_replays`, proved). Take a thread whose
spin certificate `stvRun` accepts, a domain and fuel for which `pexplore` succeeds for every
spin bound, and a run of the whole function on `Atomic9.step` from its initial core to its end,
with interference and every read in the domain (`DomRun`). Then for some spin bound `n`
one trace of the pieces matches the run step by step (`Trace.Matches`).

PROVED (`piecesComplete_holds` in `Bridge/Thms.lean`; proof in
`Silmaril/Proofs/X86/Concurrency/Bridge/Complete.lean`), for `n` = the run's length.

**Restated**: the hypothesis `run ≠ [] ∨ th.code.length < 2 ^ 64` was added. Without it
the statement is false, for an absurdly long code: take `2 ^ 64` one-byte `nop`s cut into
`2 ^ 64` `pad 1` pieces (`stvRun` accepts, `pexplore` succeeds). `whole th` ends at
`base + 2 ^ 64 = base` (64-bit wrap-around) = the initial `rip`, so the empty run is a
`DomRun`, but every trace of the pieces executes the first `nop` and has at least one step.
A non-empty run implies the bound (its first step's memory has the code loaded, so
`base + length ≤ 2 ^ 64`, and the start is not the end), so the restatement only excludes that
degenerate empty run. The counterexample is formalized:
`piecesCompleteUnrestricted_false : ¬ PiecesCompleteUnrestricted` in `Bridge/Thms.lean`, by a
symbolic induction over the `2 ^ 64` pieces (`Silmaril/Proofs/X86/Concurrency/Bridge/Counter.lean`).

With `stvRun_sound` this makes every such run of the bytes a run of the CIR thread
`c.body n` (`whole_refines` in `Bridge/Thms.lean`).

Proof: induction over the pieces, splitting the run at the first core with
`rip = base + o + len` (`explore_split`, `exploreT_split`: the completeness argument step by
step). The piece's fetch agrees with the rest of the function's (`fetch_prefix`): the piece's
15-byte window is a prefix of the longer one and `Atomic9.decode` is **prefix-stable**
(`Atomic9.decode_append`, proved for every form: `Ext`, `Ext8`, `Ext9`, the atomic forms). For
a spin, the run's length bounds the retries, so `exploreT` with fuel `3 (n + 1)` keeps the run.
`pexplore`'s `rip` reset is the identity on a piece's final core. Nothing about the pieces'
certificates is used beyond their lengths covering the code. -/
def Task.piecesComplete : Prop :=
  ∀ (th : SThread) (c : SCert) (K : List Reg), stvRun th c = some K →
    ∀ (dom : List Nat) (fuel : Nat),
      (∀ n, (pexplore th dom fuel n 0 c.pieces th.init).isSome = true) →
      ∀ (run : List SeqStep) (fin : State), DomRun (whole th) dom th.init run fin →
        (run ≠ [] ∨ th.code.length < 2 ^ 64) →
        ∃ n trs, pexplore th dom fuel n 0 c.pieces th.init = some trs ∧
          ∃ tr ∈ trs, tr.Matches run fin

/-- **The original statement of `Task.piecesComplete`**, without the hypothesis
`run ≠ [] ∨ th.code.length < 2 ^ 64`. It is **false** (`piecesCompleteUnrestricted_false` in
`Bridge/Thms.lean`): `2 ^ 64` one-byte `nop`s cut into `pad 1` pieces
pass `stvRun`, every `pexplore` succeeds, the end `base + 2 ^ 64` wraps to `base`, so the empty
run is a `DomRun`, and no trace of the pieces is empty. Kept only to state the counterexample. -/
def PiecesCompleteUnrestricted : Prop :=
  ∀ (th : SThread) (c : SCert) (K : List Reg), stvRun th c = some K →
    ∀ (dom : List Nat) (fuel : Nat),
      (∀ n, (pexplore th dom fuel n 0 c.pieces th.init).isSome = true) →
      ∀ (run : List SeqStep) (fin : State), DomRun (whole th) dom th.init run fin →
        ∃ n trs, pexplore th dom fuel n 0 c.pieces th.init = some trs ∧
          ∃ tr ∈ trs, tr.Matches run fin

/-! ## Gap 1: concurrent x86 runs are CIR behaviours -/

/-- **A memory for a litmus test**: the test's regions, every thread's code loaded at its base
(the placement, `Test.xthread`), every location byte at its initial value, and mapped readable
bytes backed. -/
def TestMem (t : Test) (m : Memory) : Prop :=
  m.regions = Silmaril.X86.Litmus.testRegions t.threads.length ∧
    (∀ k th, t.threads[k]? = some th → Loaded m (Silmaril.X86.Litmus.codeBase k) th.code) ∧
    (∀ a b, t.initMem a = some b → m.bytes.get? a = some b) ∧ Backed m

/-- The initial TSO pool of a test: thread `k` at its initial core, the given memory, empty
store buffers. -/
def testPool (t : Test) (m : Memory) : TPool Nat :=
  ⟨fun k => (t.threads[k]?).map fun th => (t.xthread k th).init, m, fun _ => []⟩

/-- Thread `k` has finished: its `rip` is at the end of its code. -/
def TestFin (t : Test) (k : Nat) (c : State) : Prop :=
  ∀ th, t.threads[k]? = some th → c.rip = (t.xthread k th).endRip

/-- The final state of a pool: each thread's registers (zero for a missing thread) and the
memory's bytes. -/
def poolFinal (p : TPool Nat) : Final :=
  ⟨fun i r => ((p.threads i).map fun c => c.read r).getD 0, fun a => p.memory.bytes.get? a⟩

/-- Within each thread, the memory footprints of every choice of extracted traces are equal or
disjoint (`OpAx.ThreadCells`, the side condition of op-TSO ⊆ ax-TSO, which is false without it:
`partialForward_not_explained`). -/
def CellsOk (t : Test) : Prop :=
  ∀ (D : List Nat) (T : List (List Silmaril.X86.MemoryModel.Litmus.XTrace)), t.extractOver D = some T →
    ∀ trs, List.Forall₂ (· ∈ ·) trs T →
      Silmaril.X86.MemoryModel.OpAx.ThreadCells (trs.mapIdx Silmaril.X86.MemoryModel.Litmus.traceX)

/-- **The final states of the TSO machine over the bytes of a test**: run the byte-granular TSO
pool over `Atomic9.step` (`TsoReach atomic9Ev`: instruction steps fetched from and executed on
the thread's view, locked instructions and `mfence` on an empty buffer, flushes of the oldest
entry) from a test memory, to a drained pool where every thread has finished. -/
def TsoFinal (t : Test) (f : Final) : Prop :=
  ∃ (m₀ : Memory) (p : TPool Nat), TestMem t m₀ ∧
    TsoReach atomic9Ev (TestFin t) (testPool t m₀) p ∧ Drained p ∧
    (∀ k s, p.threads k = some s → TestFin t k s) ∧ f = poolFinal p

/-- **The condition observes only initialised bytes**: every memory atom of the test's condition
reads bytes that some location of the test initialises (`Test.initMem`). A test memory
(`TestMem`) fixes exactly those bytes; any other byte of the data page is arbitrary on the
machine, while a CIR behaviour (`Cir.Behav`, `finalAx`) leaves an unwritten byte at its
initial value, `none` outside the locations. -/
def CondInit (t : Test) : Prop :=
  ∀ a n v, Silmaril.X86.MemoryModel.Litmus.Atom.mem a n v ∈ t.cond.atoms → ∀ j < n,
    (t.initMem (a + j)).isSome = true

/-- `CondInit` as a Boolean check: `condInit_of` in `Bridge/Thms.lean` makes it
sufficient, and every test of the corpus passes it (`corpus_condInit`). -/
def condInitB (t : Test) : Bool :=
  t.cond.atoms.all fun
    | .mem a n _ => (List.range n).all fun j => (t.initMem (a + j)).isSome
    | .reg .. => true

/-- The skeleton of every thread of a test: the events of each instruction of
its straight-line code (`Litmus.Thread.skel`), or `none` if some thread is not straight-line
code. Every symbolic run of the thread to the end of its code has exactly these events, whatever
the values read (`xrun_skel` in `Proofs/.../Bridge/TsoRun.lean`). -/
def testSkels (t : Test) : Option (List (List (List MemEvent.Event))) :=
  (t.threads.mapIdx fun k th => (t.xthread k th).skel t.fuel).mapM id

/-- The memory events (loads, stores, read-modify-writes) of a list of skeletons. -/
def memEvs (Ss : List (List (List MemEvent.Event))) : List MemEvent.Event :=
  Ss.flatten.flatten.filter fun e => e.kind.reads || e.kind.writes

/-- **Every access of the test is a cell access**, checked on the threads'
skeletons: every thread is straight-line code, and its memory accesses

* are single-copy atomic: 1 to 8 bytes, naturally aligned;
* are, across **all** threads, at equal or disjoint footprints (so neither a thread's store
  buffer forwards part of a store, `OpAx.ThreadCells`, nor is an access split into bytes,
  `PoolRun.NoTear`);
* read only bytes some location of the test initialises (a test memory, `TestMem`, fixes only
  those bytes, while a CIR behaviour reads any other byte as `0`; the counterexample).

It replaces `CellsOk` as the hypothesis of `Task.tsoRunCir` (with `CellsOk` the Task is
false: `not_tsoRunCirCells`). That `cellsB` implies `CellsOk` is expected (the skeleton fixes the
extracted traces' events, `extract_skel`) but not proved. -/
def cellsB (t : Test) : Bool :=
  match testSkels t with
  | some Ss =>
    let es := memEvs Ss
    es.all (fun e => decide (0 < e.size) && decide (e.size ≤ 8) && e.addr % e.size == 0) &&
      es.all (fun e => es.all fun f => (e.addr == f.addr && e.size == f.size) ||
        decide (e.addr + e.size ≤ f.addr) || decide (f.addr + f.size ≤ e.addr)) &&
      es.all (fun e => !e.kind.reads ||
        (List.range e.size).all fun j => (t.initMem (e.addr + j)).isSome)
  | none => false

/-- **The original statement of gap 1, which is FALSE** (`not_tsoRunCirAsStated` in
`Bridge/Thms.lean`). As `Task.tsoRunCir` without `CondInit`: a test whose condition reads a
data byte no location initialises (the counterexample has no threads and the condition
`[0x10000] = 5`) is satisfied by a test memory holding `5` there, while every CIR behaviour of
its program leaves that byte undefined. Kept as a plain `def` to record the counterexample. -/
def tsoRunCirAsStated : Prop :=
  ∀ (c : TvTest), c.tvOk = true → CellsOk c.test →
    ∀ f, TsoFinal c.test f →
      ∃ f', Behav c.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso f' ∧
        c.test.witness.eval f' = c.test.witness.eval f

/-- **Every run of the TSO machine over the bytes of a validated test is a CIR behaviour.**
Take a test whose certificates `tvRun` accepts (`TvTest.tvOk`), whose accesses are cell accesses
(`cellsB`: straight-line threads whose accesses are single-copy atomic, at equal or disjoint
footprints across all threads, and read only initialised bytes) and whose condition observes
only initialised bytes (`CondInit`). Every final state of the concurrent TSO machine over its
bytes (`TsoFinal`) has the witness value of some behaviour of the CIR program under axiomatic
TSO (over some value domain, `Cir.Behav`).

PROVED: `tsoRunCir_holds` in `Bridge/Thms.lean` (proofs in
`Silmaril/Proofs/X86/Concurrency/Bridge/TsoRun/{Mem,Run,Cells,Main}.lean`). All 60 corpus tests
pass both checks (`corpus_cellsB`, `corpus_condInit`).

**Restated twice.** First `CondInit` was added: without it the statement is false
(`tsoRunCirAsStated`, `not_tsoRunCirAsStated`). Then the per-thread cell condition
`CellsOk` was replaced by `cellsB`: with `CellsOk` the statement is false (`tsoRunCirCells`,
`not_tsoRunCirCells`, the counterexample: a thread reads a byte no location initialises, which
the test memory may set while CIR reads it as `0`). `cellsB` also asks the accesses of
**different** threads to be at equal or disjoint footprints and single-copy atomic, so that no
access is split into bytes (`NoTear`). That part is what the proof needs, not shown to be
necessary: a test with tearing accesses is outside the statement, not a counterexample.

This is the step from "the CIR verdicts hold" to "they hold for the bytes running
concurrently": `forbidden_tso_bytes` in `Bridge/Thms.lean`. The litmus layer's per-thread
traces (`Test.traces`) and its op-TSO column (the machine over **extracted events**) are not a
concurrent machine over the bytes; `TsoReach atomic9Ev` is.

The proof:
(1) the pool run keeps the test's regions, backing and code, and buffers only write-permitted
bytes (`MemInv`), so each thread's view `overlay memory buffer` has the thread's regions and code
and is backed; (2) each instruction step is a symbolic step (`xstep_of_step`, with `stepSym`
defined by `tvRunDefined_holds`), the pool's fetch on the view being the fetch on the code
(`Atomic9.fetch_of_listed_base`, `fetch_of_listed_new`), so the run is recorded with `RunA` and
every thread's history is an `XRun` from its initial core (`reach_inv`); **not**
`extract_complete`, since extraction over the run's own values can fail (a later address may
depend on an earlier loaded value); (3) each finished history is a CIR run over any domain
holding the values read (`Cir.Tv.tvRun_xrun`; `chk1` makes an 8-byte read
leave the fitting set, `Cir.Tv.q_load_unfit`, `qCas_rejected`); (4) the recorded run is an
`OpAx.Run` of the operational machine (`opRun_of_runA`); (5) `run_explains_tso_paired` gives a
TSO candidate, needing `ThreadCells`; (6) `axReach_of_explains` turns it into `AxReach`, needing
`NoTear` and `InitReads`; `cellsB` gives `ThreadCells`, `NoTear` and `InitReads`, since
every run of straight-line code to its end has the code's skeleton as its events
(`xrun_skel`); `axReach_pick` then moves the `AxReach` state to the CIR traces;
(7) the witness: observed registers are not clobbered (`condAvoids`), and observed bytes are
initialised (`CondInit`), so an unwritten one is the location's initial value on both sides.
Not covered: Weak9's non-temporal and string forms, loops and computed addresses (not
straight-line), and tearing accesses. -/
def Task.tsoRunCir : Prop :=
  ∀ (c : TvTest), c.tvOk = true → cellsB c.test = true → CondInit c.test →
    ∀ f, TsoFinal c.test f →
      ∃ f', Behav c.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso f' ∧
        c.test.witness.eval f' = c.test.witness.eval f

/-- **The statement of gap 1 with `CellsOk`, which is FALSE** (`not_tsoRunCirCells` in
`Bridge/Thms.lean`, formalising the counterexample). As `Task.tsoRunCir` with the per-thread
cell condition `CellsOk` in place of `cellsB`: a thread may read a byte no location initialises
(`mov eax, dword [0x10004]` in a test without locations), which a test memory leaves free (it
may hold `5`) while every CIR behaviour reads it as `0`. Kept to record the counterexample. -/
def tsoRunCirCells : Prop :=
  ∀ (c : TvTest), c.tvOk = true → CellsOk c.test → CondInit c.test →
    ∀ f, TsoFinal c.test f →
      ∃ f', Behav c.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso f' ∧
        c.test.witness.eval f' = c.test.witness.eval f

/-! ## Gap 4: calls -/

/-- The code from offset `lo` to `hi` of a thread, at its own base (a function body inside an
image). -/
def slice (t : XThread) (lo hi : Nat) : XThread :=
  ⟨t.base + BitVec.ofNat 64 lo, (t.code.drop lo).take (hi - lo), t.regions, t.init⟩

/-- A `call rel32` at offset `o` of the image whose target is offset `fo`. -/
def CallAt (t : XThread) (o fo : Nat) : Prop :=
  ∃ rel : BitVec 32, fetchAt t o = some (.open9 (.ext8 (.base (.call rel))), 5) ∧
    t.base + BitVec.ofNat 64 (o + 5) + rel.signExtend 64 = t.base + BitVec.ofNat 64 fo

/-- **One validated call on the real machine.** Take an image `t` with a `call rel32` at offset
`o` to offset `fo`, where the callee's body `[fo, fo + fl)` is accepted by `tvCfg` against a
certificate `c` and is followed by a `ret` (`C3`). On the real machine `Atomic9.step`:

* the `call` from core `s` on memory `m₁` pushes the return address `s.rip + 5` at `rsp - 8`
  (`m₂` is `m₁` with those eight bytes written), sets `rsp` to `rsp - 8` and goes to the body,
  keeping every other register;
* for every symbolic run `acc` of the body (`XRun` of the slice) to its end that leaves `rsp`
  as the call set it, and a memory `m₃`
  whose stack slot still holds what the call wrote (interference left it alone), the `ret`
  returns to `s.rip + 5`, restores `rsp`, keeps every other register of the body's final core,
  and leaves memory unchanged;
* and the body is a CIR run of `c.body L` that has finished (`skip`) for every `L ≥ |acc|`,
  step for step (`tvCfg_steps`), from the registers after the call.

This is the obligation a call-level front end discharges per call site.

PROVED (as stated): `callRet_holds` in `Bridge/Thms.lean` (proof in
`Silmaril/Proofs/X86/Concurrency/Bridge/Link.lean`), by steps (1) and (2) of the plan below:
`call_law` and `ret_law` (the converse of the listing law, `Atomic9.exec_of_step_base`, turns
the real step into `Ext.exec` of `call`/`ret`, which is `pushWord`/`popWord`), and
`tvCfg_steps` on the slice. Steps (3) and (4) are the caller checker `ltv` below, whose
soundness `ltv_real` keeps the stack slot as a run hypothesis (`LRun`) instead of erasing it by
`cirLocalize`'s argument; `pthread_*` (4) is not done.

Plan: (1) the call and `ret` laws: `step_of_listed` reduces `Atomic9.step` at the listed `E8`
and `C3` to `Ext.exec`, which is `X86.Insn.exec` on `call`/`ret` (`Ext.exec_ofInsn`), i.e.
`pushWord`/`popWord`; the converse (a successful step is that one) is `step_of_listed` and
`Atomic9.step` being a function; (2) the last conjunct is `tvCfg_steps` on the slice, whose
start core has `rip = slice base` by (1); (3) the push and pop are accesses to a thread-owned
cell, so on CIR they are erased by `Tv.Task.cirLocalize`'s argument (owned fragment, not
visible to other threads), which a linking theorem over the caller's pieces (`mwalk`
shape, cut at `call` sites) uses; (4) `pthread_create`/`pthread_join` are then CIR
`spawn`/`join` through the PIR lowering and `PStep`. -/
def Task.callRet : Prop :=
  ∀ (t : XThread) (c : GCert) (o fo fl : Nat),
    CallAt t o fo → fo + fl < t.code.length → t.code[fo + fl]? = some 0xC3 →
    tvCfg (slice t fo (fo + fl)) c = true →
    ∀ (s s₁ : State) (m₁ m₂ : Memory), s.rip = t.base + BitVec.ofNat 64 o →
      m₁.regions = t.regions → Loaded m₁ t.base t.code →
      Atomic9.step ⟨s, m₁⟩ = some ⟨s₁, m₂⟩ →
      m₁.writeBytes (s.read .rsp - 8).toNat (encodeWords [s.rip + 5]) = some m₂ ∧
      s₁.read .rsp = s.read .rsp - 8 ∧ s₁.rip = (slice t fo (fo + fl)).base ∧
      (∀ r, r ≠ .rsp → s₁.read r = s.read r) ∧
      ∀ (acc : List (List XAct)) (s₂ : State), XRun (slice t fo (fo + fl)) s₁ acc s₂ →
        s₂.rip = (slice t fo (fo + fl)).endRip → s₂.read .rsp = s₁.read .rsp →
        (∀ (m₃ : Memory) (s₃ : State) (m₄ : Memory), m₃.regions = t.regions →
          Loaded m₃ t.base t.code →
          m₃.readBytes (s.read .rsp - 8).toNat 8 = some (encodeWords [s.rip + 5]) →
          Atomic9.step ⟨s₂, m₃⟩ = some ⟨s₃, m₄⟩ →
          s₃.rip = s.rip + 5 ∧ s₃.read .rsp = s.read .rsp ∧ m₄ = m₃ ∧
            ∀ r, r ≠ .rsp → s₃.read r = s₂.read r) ∧
        ∀ L, acc.length ≤ L → ∃ rs, ∃ los : List (Option Lab),
          TRun (c.body L) (regsOf s₁) (los.filterMap id) .skip rs ∧
          List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
          regsOf s₂ = rs

/-! ## Gap 4: a caller cut at its call sites, linked with its callees' certificates -/

/-- **A callee**: its body `[off, off + len)` of the image, followed by a `ret`, and the
certificate of the body. -/
structure Callee where
  off : Nat
  len : Nat
  cert : GCert

/-- **A part of a caller**: a segment of `len` bytes validated by `cert`, then a `call rel32`
to `callee`. -/
structure Part where
  len : Nat
  cert : GCert
  callee : Callee

/-- **A linking certificate** of a caller: its parts, cut at its call sites, and the last
segment (up to the caller's own `ret`, which belongs to its caller). -/
structure LCert where
  parts : List Part
  lastLen : Nat
  lastCert : GCert

/-- A segment of `n` bytes at offset `o` fits in the image and `tvCfg` accepts it. -/
def segOk (t : XThread) (o n : Nat) (c : GCert) : Bool :=
  decide (o + n ≤ t.code.length) && tvCfg (slice t o (o + n)) c

/-- **A call site checks**: the instruction at `o` is a `call rel32` whose target is the
callee's offset (mod `2 ^ 64`, so independent of the image's base), the callee's body is followed
by a `ret` (`C3`) inside the image, and `tvCfg` accepts the body. -/
def callOk (t : XThread) (o : Nat) (f : Callee) : Bool :=
  match fetchAt t o with
  | some (.open9 (.ext8 (.base (.call rel))), 5) =>
    BitVec.ofNat 64 (o + 5) + rel.signExtend 64 == BitVec.ofNat 64 f.off &&
      decide (f.off + f.len < t.code.length) && t.code[f.off + f.len]? == some 0xC3 &&
      tvCfg (slice t f.off (f.off + f.len)) f.cert
  | _ => false

/-- The walk over the parts from offset `o`. -/
def ltvFrom (t : XThread) : Nat → List Part → Nat → GCert → Bool
  | o, [], n, c => segOk t o n c
  | o, p :: ps, n, c =>
    segOk t o p.len p.cert && callOk t (o + p.len) p.callee && ltvFrom t (o + p.len + 5) ps n c

/-- **The caller checker** (`mwalk` shape, cut at `call` sites instead of marker calls):
the caller at offset `o` of the image `t`, its segments and its callees' bodies validate. -/
def ltv (t : XThread) (o : Nat) (lc : LCert) : Bool := ltvFrom t o lc.parts lc.lastLen lc.lastCert

/-- The CIR glue of a `call`: `rsp := rsp - 8` (the push of the return address is erased: its
slot is thread-owned stack, see `LRun`). -/
def push8 : Stmt := .assign .rsp (.bin .sub (.reg .rsp) (.lit 8))

/-- The CIR glue of a `ret`: `rsp := rsp + 8`. -/
def pop8 : Stmt := .assign .rsp (.bin .add (.reg .rsp) (.lit 8))

/-- **The linked CIR program** of a caller, loops bounded by `L`: each segment's program, then
the glue, the callee's program and the glue, then the next part. -/
def lbody (L : Nat) : List Part → GCert → Stmt
  | [], c => c.body L
  | p :: ps, c =>
    .seq (p.cert.body L) (.seq push8 (.seq (p.callee.cert.body L) (.seq pop8 (lbody L ps c))))

/-- The linked CIR program of a linking certificate. -/
def LCert.body (lc : LCert) (L : Nat) : Stmt := lbody L lc.parts lc.lastCert

/-- An observed step of a caller run: a machine step inside a segment or a callee's body, the
`call`, or the `ret`. -/
inductive LObs where
  | step (q : SeqStep)
  | call (q : SeqStep)
  | ret (q : SeqStep)

/-- The CIR label of an observed step: a machine step's actions are those of the label and are
the real step's (`ActsOk`); a `call` has no label and writes exactly the 8-byte slot at the new
`rsp`; a `ret` has no label and does not change memory. -/
def LObs.Ok : LObs → Option Lab → Prop
  | .step q, o => ActsOk (o.toList.flatMap Lab.acts) q
  | .call q, o => o = none ∧ ∃ w, q.pre.writeBytes (q.post.read .rsp).toNat (encodeWords [w]) = some q.mem
  | .ret q, o => o = none ∧ q.mem = q.pre

/-- **A real run of a caller** on `Atomic9.step`, with interference, cut at its call sites: each
segment's run (`A9Run` of the segment's slice) to the segment's end; the `call` (on a memory with
the image's regions and code); the callee's run to the end of its body; the `ret`, on a memory
whose slot at `rsp` holds the return address; and so on, to the end of the last segment.

The slot hypothesis `hslot` is the one assumption about the stack: the return address the
`call` pushed is still there when the callee returns (no other thread and not the callee wrote
it). It is not derived here; `Tv.Task.cirLocalize`'s argument is the CIR form of it. -/
inductive LRun (t : XThread) : Nat → List Part → Nat → GCert → State → List LObs → State → Prop
  | last {o n : Nat} {c : GCert} {s : State} {xs : List SeqStep} {s' : State}
      (hr : A9Run (slice t o (o + n)) s xs s') (he : s'.rip = (slice t o (o + n)).endRip) :
      LRun t o [] n c s (xs.map .step) s'
  | call {o : Nat} {p : Part} {ps : List Part} {n : Nat} {c : GCert} {s : State}
      {xs : List SeqStep} {s₁ : State} {qc : SeqStep} {ys : List SeqStep} {s₃ : State}
      {qr : SeqStep} {zs : List LObs} {s' : State}
      (hr : A9Run (slice t o (o + p.len)) s xs s₁)
      (he : s₁.rip = (slice t o (o + p.len)).endRip)
      (hRc : qc.pre.regions = t.regions) (hlc : Loaded qc.pre t.base t.code)
      (hc : Atomic9.step ⟨s₁, qc.pre⟩ = some ⟨qc.post, qc.mem⟩)
      (hf : A9Run (slice t p.callee.off (p.callee.off + p.callee.len)) qc.post ys s₃)
      (hfe : s₃.rip = (slice t p.callee.off (p.callee.off + p.callee.len)).endRip)
      (hRr : qr.pre.regions = t.regions) (hlr : Loaded qr.pre t.base t.code)
      (hslot : qr.pre.readBytes (s₃.read .rsp).toNat 8 = some (encodeWords [s₁.rip + 5]))
      (hret : Atomic9.step ⟨s₃, qr.pre⟩ = some ⟨qr.post, qr.mem⟩)
      (tl : LRun t (o + p.len + 5) ps n c qr.post zs s') :
      LRun t o (p :: ps) n c s (xs.map .step ++ .call qc :: ys.map .step ++ .ret qr :: zs) s'

end Silmaril.X86.Concurrency.Bridge
