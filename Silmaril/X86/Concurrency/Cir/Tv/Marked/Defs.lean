module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Sync.Defs

/-!
# Translation validation of compiled C threads with spawn/join marker calls

A compiled C thread
function calls **marker stubs** where the C program spawns or joins a thread
(`call cir_spawn1`, `call cir_join1`, ...). In the x86 code a marker call is an ordinary
`call rel32`. Its meaning is a CIR thread operation, which no x86 instruction has, so it is
given here as a convention and stated as part of the x86 semantics (`mexplore`).

## The x86 semantics of a marked thread

A `CThread` is the relocated bytes of a thread function (without its final `ret`), placed at
a base address, together with the code offsets of its marker calls (`cuts`). The cuts are
taken from the object's relocations against the marker symbols. `CThread.split` cuts the code
at these offsets into straight-line **segments** (litmus threads). It checks that each cut is a
`call rel32` (`E8` and four displacement bytes) whose target is a marker stub (`Stubs`), and
gives the marks between the segments.

`mexplore` runs the segments in order with the extractor (`explore`). A marker call is
**one event**: the ghost control action of its thread operation (`Mark.act`, the same action
CIR's `spawn`/`join` lower to). It leaves every register unchanged and continues at the next
segment (`rip := next base`). The call does not push a return address, and the stub's code is
not run. A real runtime implements this with a stub that saves every register and synchronises.
That the stub has this meaning is an assumption, not proved. A spawned thread's trace is wrapped
with its start and end control actions (`wrap`), as CIR's `Thread.acts` does.

## The certificate and the checker

`MCert`: the initial registers as CIR assignments (`pro`), and for each segment its items, one
per instruction (`Item`). The CIR thread is the segments' statements with `m.stmt`
(`spawn t` or `join t`) between them (`MCert.body`). `mtvRun` checks three things:

* the prologue gives the initial registers;
* every segment passes `walk`;
* the clobber set flows from one segment to the next.

The fitting set `Z` restarts empty after a marker, because nothing is known about the ranges of
the registers there. The checker gives the final clobber set.

`Cir.Tv.mtvRun_sound` (in `Marked/Thms.lean`) gives the refinement per thread: every trace of
`mexplore` is a CIR run over the same domain. The actions are equal up to `normActs`, and the
final registers are equal outside the clobber set.

## Tests

A `CTest` is a C test: memory locations, condition and recorded verdicts (a litmus `Test` with no
x86 threads), the C threads, the stubs, one certificate per thread, a value domain and fuel.
`CTest.allOk` is the Boolean check behind `Cir.Tv.CTest.transfer_of_allOk`:

* the certificates check;
* the domain fits;
* the enumerators on the CIR program give the recorded SC, TSO and XL verdicts, and the
  recorded verdict under operational TSO with the control bytes mapped;
* some SC execution exists;
* the x86 traces exist.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Trace StepRec explore)
open Silmaril.Process (Region)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test Cond Model outsBy AxReach OpReach Byte)

/-! ## Marks -/

/-- The thread operation a marker call stands for. -/
inductive Mark where
  | spawn (t : Nat)
  | join (t : Nat)
  deriving DecidableEq, Repr

/-- The CIR statement of a mark. -/
def Mark.stmt : Mark → Stmt
  | .spawn t => .spawn t
  | .join t => .join t

/-- The CIR label of a mark. -/
def Mark.lab : Mark → Lab
  | .spawn t => .spawn t
  | .join t => .join t

/-- The memory action of a mark: its ghost control action, as CIR lowers it. -/
def Mark.act : Mark → XAct
  | .spawn t => ctlAct t 0 1
  | .join t => endAct t 1 2

/-- Marker stubs: the absolute address of each stub, with its mark. -/
abbrev Stubs := List (Nat × Mark)

/-! ## Marked threads -/

/-- A compiled C thread: the relocated bytes of its function without the final `ret`, at
`base`, with its regions and initial core, the code offsets of its marker calls, and whether
another thread spawns it. -/
structure CThread where
  base : Word
  code : List Byte
  regions : List Region
  init : State
  cuts : List Nat
  spawned : Bool := false

/-- The target of the `call rel32` at code offset `c` with displacement bytes `ds`. -/
def callTarget (base : Word) (c : Nat) (ds : List Byte) : Nat :=
  (base + BitVec.ofNat 64 (c + 5) +
    (BitVec.ofNat 32 (Silmaril.X86.Ext.leValue ds)).signExtend 64).toNat

/-- The mark of the marker call at code offset `c`: the bytes are `E8 rel32` and the target is
a stub. -/
def CThread.markAt (th : CThread) (st : Stubs) (c : Nat) : Option Mark :=
  match (th.code.drop c).take 5 with
  | [op, d0, d1, d2, d3] =>
    if op = 0xe8 then st.lookup (callTarget th.base c [d0, d1, d2, d3]) else none
  | _ => none

/-- The segment of code offsets `lo` to `hi`, as a litmus thread. -/
def CThread.seg (th : CThread) (lo hi : Nat) : XThread :=
  ⟨th.base + BitVec.ofNat 64 lo, (th.code.drop lo).take (hi - lo), th.regions, th.init⟩

/-- **Cut the code at the marker calls**: the segments and the marks between them. -/
def CThread.split (th : CThread) (st : Stubs) : Nat → List Nat → Option (List XThread × List Mark)
  | lo, [] => if lo ≤ th.code.length then some ([th.seg lo th.code.length], []) else none
  | lo, c :: cs =>
    if lo ≤ c then
      match th.markAt st c, th.split st (c + 5) cs with
      | some m, some (ts, ms) => some (th.seg lo c :: ts, m :: ms)
      | _, _ => none
    else none

/-- A segment trace, the marker's event, then the trace of the rest. -/
def glue (tr : Trace) (m : Mark) (tr' : Trace) : Trace :=
  ⟨tr.steps ++ ⟨[m.act], tr.final⟩ :: tr'.steps, tr'.final⟩

/-- **The x86 semantics of a marked thread**: the segments run in order with the extractor.
Each marker call is its control event; it keeps every register and continues at the next
segment. -/
def mexplore (dom : List Nat) (fuel : Nat) : List XThread → List Mark → State → Option (List Trace)
  | [t], [], s => explore t dom fuel s
  | t :: t' :: ts, m :: ms, s =>
    (explore t dom fuel s).bind fun trs =>
      (trs.mapM fun tr =>
        (mexplore dom fuel (t' :: ts) ms { tr.final with rip := t'.base }).map
          (List.map (glue tr m))).map List.flatten
  | _, _, _ => none

/-- A spawned thread's trace starts and ends with its control events. -/
def wrap (i : Nat) (sp : Bool) (tr : Trace) : Trace :=
  if sp then ⟨⟨[ctlAct i 1 2], tr.final⟩ :: tr.steps ++ [⟨[endAct i 0 1], tr.final⟩], tr.final⟩
  else tr

/-- The marks of a thread (empty if the cuts are not marker calls). -/
def CThread.marks (th : CThread) (st : Stubs) : List Mark :=
  match th.split st 0 th.cuts with
  | some (_, ms) => ms
  | none => []

/-- **The x86 traces of thread `i`** over `dom`. -/
def CThread.traces (th : CThread) (st : Stubs) (i : Nat) (dom : List Nat) (fuel : Nat) :
    Option (List Trace) :=
  match th.split st 0 th.cuts with
  | some (ts, ms) => (mexplore dom fuel ts ms th.init).map (List.map (wrap i th.spawned))
  | none => none

/-! ## Certificates -/

/-- A marked certificate: the initial registers, and the items of each segment. -/
structure MCert where
  pro : List (Reg × Nat)
  segs : List (List Item)

/-- The statements of the segments with the marks between them. -/
def mops : List (List Item) → List Mark → List Stmt
  | [its], [] => its.flatMap Item.ops
  | its :: iss, m :: ms => its.flatMap Item.ops ++ m.stmt :: mops iss ms
  | _, _ => []

/-- **The CIR thread of a marked certificate.** -/
def MCert.body (c : MCert) (ms : List Mark) : Stmt :=
  chain ((c.pro.map fun p => .assign p.1 (.lit p.2)) ++ mops c.segs ms)

/-- Some item reads memory. -/
def MCert.reads (c : MCert) : Bool := c.segs.any fun its => its.any fun it => it.ops.any Stmt.reads

/-- Walk the segments in order, the clobber set flowing through the markers. -/
def mwalk : List XThread → List Mark → List (List Item) → List Reg → List Reg → Option (List Reg)
  | [t], [], [its], K, Z => if t.code.length < 2 ^ 64 then walk t K Z 0 its else none
  | t :: t' :: ts, _ :: ms, its :: iss, K, Z =>
    if t.code.length < 2 ^ 64 then
      match walk t K Z 0 its with
      | some K' => mwalk (t' :: ts) ms iss K' []
      | none => none
    else none
  | _, _, _, _, _ => none

/-- **The marked checker**: the final clobber set, or `none`. -/
def mtvRun (th : CThread) (st : Stubs) (c : MCert) : Option (List Reg) :=
  match th.split st 0 th.cuts with
  | some (ts, ms) =>
    let pc : Cert := ⟨c.pro, []⟩
    if th.init.rip = th.base ∧ (allRegs.all fun r => th.init.read r == pc.proRegs r) then
      mwalk ts ms c.segs [] (allRegs.filter fun r => decide ((pc.proRegs r).toNat < 2 ^ 32))
    else none
  | none => none

/-! ## Tests -/

/-- A translation-validated C test. `test` holds the locations, the condition and the recorded
verdicts (its `threads` are unused). -/
structure CTest where
  test : Test
  threads : List CThread
  stubs : Stubs
  certs : List MCert
  dom : List Nat
  fuel : Nat

/-- The certificate of thread `k`. -/
def CTest.cert (c : CTest) (k : Nat) : MCert := c.certs.getD k ⟨[], []⟩

/-- **The CIR program** of a C test. -/
def CTest.prog (c : CTest) : Prog :=
  ⟨c.test.locs, c.threads.mapIdx fun k th => ⟨(c.cert k).body (th.marks c.stubs), th.spawned⟩⟩

/-- The x86 traces of every thread. -/
def CTest.xtraces (c : CTest) : Option (List (List XTrace)) :=
  (c.threads.mapIdx fun k th => th.traces c.stubs k c.dom c.fuel).mapM id

/-- **The x86 behaviours** of a C test under `M`: `AxReach` over the marked threads'
traces. -/
def CTest.XBehav (c : CTest) (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop)
    (f : Silmaril.X86.MemoryModel.Litmus.Final) : Prop :=
  ∃ T, c.xtraces = some T ∧ AxReach c.prog.memTest T M f

/-- The clobber sets. -/
def CTest.clobs (c : CTest) : Option (List (List Reg)) :=
  (c.threads.mapIdx fun k th => mtvRun th c.stubs (c.cert k)).mapM id

/-- One certificate per thread, every certificate checks, and observed registers are not
clobbered. -/
def CTest.tvOk (c : CTest) : Bool :=
  c.threads.length == c.certs.length &&
    match c.clobs with
    | some Ks => condAvoids c.test.cond Ks
    | none => false

/-- The domain fits in 32 bits, or no thread reads memory. -/
def CTest.domOk (c : CTest) : Bool :=
  c.certs.all (fun ct => !ct.reads) || c.dom.all fun v => decide (v < 2 ^ 32)

/-- The recorded verdict of a model. -/
def CTest.verdict (c : CTest) : Model → Silmaril.X86.MemoryModel.Litmus.Verdict
  | .sc => c.test.sc.getD c.test.xl
  | .tso => c.test.tso.getD c.test.xl
  | .xl => c.test.xl

/-- The test with the control bytes mapped (for operational TSO). -/
def CTest.opT (c : CTest) : Test := { c.test with locs := c.test.locs ++ c.prog.ctlLocs }

/-- **The CIR verdict checks**: the axiomatic enumerator gives the recorded SC, TSO and XL
verdicts over `dom`, some SC execution exists, and operational TSO gives the recorded TSO
verdict. -/
def CTest.cirCheck (c : CTest) : Bool :=
  (match c.test.axJudge (c.prog.traces c.dom) with
    | some js =>
      c.verdict .sc == c.test.verdictOf (outsBy js Model.sc.sel) &&
        c.verdict .tso == c.test.verdictOf (outsBy js Model.tso.sel) &&
        c.verdict .xl == c.test.verdictOf (outsBy js Model.xl.sel) &&
        !(outsBy js Model.sc.sel).isEmpty
    | none => false) &&
  match c.opT.opOut (c.prog.traces c.dom) with
  | some os => c.verdict .tso == c.test.verdictOf os
  | none => false

/-- Every check of a C test. -/
def CTest.allOk (c : CTest) : Bool := c.tvOk && c.domOk && c.cirCheck && c.xtraces.isSome

open Silmaril.X86.MemoryModel.Litmus (Verdict) in
/-- What a validated C test gives (`Cir.Tv.CTest.transfer_of_allOk`). -/
structure CTest.Transfer (c : CTest) : Prop where
  /-- **Refinement**: every x86 behaviour is a CIR behaviour over the same domain with the same
  witness value. -/
  refines : ∀ (M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop) f, c.XBehav M f →
    ∃ f', BehavIn c.prog c.dom M f' ∧ c.test.witness.eval f' = c.test.witness.eval f
  /-- **The CIR verdicts** under SC, TSO and XL are the recorded ones. -/
  cir : ∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.dom M.Holds)
  /-- The recorded TSO verdict holds for CIR under operational TSO (control bytes mapped). -/
  op : (c.verdict .tso).Holds c.test (OpBehavIn c.prog c.dom)
  /-- Some SC behaviour exists. -/
  sc_some : ∃ f, BehavIn c.prog c.dom Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f
  /-- **Transfer**: every `forbidden` CIR verdict holds for the x86 code. -/
  x86_forbidden : ∀ M : Model, c.verdict M = .forbidden →
    Verdict.forbidden.Holds c.test (c.XBehav M.Holds)

end Silmaril.X86.Concurrency.Cir.Tv
