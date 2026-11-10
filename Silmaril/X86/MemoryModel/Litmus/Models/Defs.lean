module

public import Silmaril.X86.MemoryModel.Litmus.Defs
public import Silmaril.X86.Litmus.Test.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms
public import Silmaril.X86.MemoryModel.Xl.Thms
public import Silmaril.X86.MemoryModel.Tso.Defs

/-!
# Litmus outcomes under operational TSO and axiomatic SC/TSO/XL: definitions

For a corpus test
(`Litmus.Test` and the per-thread candidate traces extracted from its **bytes**
(`X86.Litmus.extract`), this module defines the final states each model reaches and
an executable enumerator for each, whose correctness is proved in
`Silmaril.X86.MemoryModel.Litmus.Models.Thms`.

## Traces

`Test.xthread` places thread `k` at `codeBase k` with the fixed data page, as `Test.thread`
does; `Test.traces` extracts every thread over `Test.domain`, which starts from the initial
values and the condition's values and adds, a bounded number of times, every value an extracted
trace writes. A list `T : List (List XTrace)` gives each thread's candidate traces; the reach
sets below are relative to `T`.

## Operational x86-TSO (`OpReach`)

The byte-granular store-buffer machine `Tso.XStep`/`Tso.XFlush` (`Silmaril.X86.MemoryModel.Tso`).
Each trace is turned into `XEvent`s (`traceX`): a load, a store, a **locked** `rmw` as one atomic
`XEvent.rmw` (which needs the issuing buffer empty), an **unlocked** read-modify-write (`inc m`) as
a load followed by a store, `mfence` as `XEvent.fence`, and `lfence`/`sfence` as nothing (they do
not order anything in x86-TSO). `AStep` runs one thread's next event or one flush. `OpReach t T f`:
some choice of one trace per thread runs to completion from the test's initial memory with empty
buffers, ends with every buffer drained, and `f` is the final registers of the chosen traces with
the final memory.

The enumerator `Test.opOut` explores the same machine level by level (`collect`, with duplicate
states removed) over concrete configurations `CCfg`: per thread the list of candidate traces
still consistent with what it has done (`Cand`), the buffers, and the memory as an association
list. A load only continues the candidates whose recorded bytes are the bytes the machine
returns, so the traces of a thread are explored together rather than per combination.

## Axiomatic SC, x86-TSO and XL (`AxReach`)

For a choice of one trace per thread, `units` builds herd-style access units (`Axiomatic.Ev`):
thread, program position, read/write/fence, footprint, `locked`, annotation (`wb`, or `nt`/`str`
for non-temporal and string stores) and written bytes, with the bytes each read must return.
An access that may tear (misaligned, wider than eight bytes, or overlapping an access of another
footprint) is split into byte units, so that XL can let it tear. `rmwPairs` pairs the halves of
locked read-modify-writes. `AxReach t T M f`: some choice of traces and some **well-formed**
candidate execution `x` over exactly those units (`Exec.Wf`) whose reads return the traces'
bytes (`ReadsOk`) is consistent under `M` (`Exec.Sc`, `Exec.Tso` or `Exec.Xl`), and `f` is the
chosen traces' registers with `x`'s final memory.

The enumerator `Test.axJudge` lists, per choice of traces, the candidates whose `rf` gives each
read unit one source (a write of the same cell, or the initial value) returning its bytes and whose
`co` orders each cell's writes in some order (`arrangements`), and judges each under the three models.
Every unit pair is required to be in one cell or disjoint (`cellsOk`); otherwise the enumerator
gives up (`none`).

## Outcomes and verdicts

Outcomes are the values of the condition's observables (`Test.keys`: registers at a width and
little-endian memory spans), so herd's outcome sets can be compared as finite lists.
`Test.checkTso` / `Test.checkXl` are the per-test Boolean checks behind the verdict theorems.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86 (Reg)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Ann)
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush)

/-- An extracted per-thread trace. -/
abbrev XTrace := Silmaril.X86.Litmus.Trace

/-- One memory action of an extracted trace. -/
abbrev XAct := Silmaril.X86.Litmus.Act

/-! ## Small list functions (structural, so that the kernel evaluates them quickly) -/

/-- Membership, as a Boolean. -/
def memB {α : Type} [DecidableEq α] (a : α) : List α → Bool
  | [] => false
  | b :: l => if a = b then true else memB a l

/-- Add an element unless present. -/
def addU {α : Type} [DecidableEq α] (a : α) (l : List α) : List α := if memB a l then l else a :: l

/-- Remove repetitions. -/
def uniq {α : Type} [DecidableEq α] (l : List α) : List α := l.foldr addU []

/-- No repetitions, as a Boolean. -/
def nodupB {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: l => !memB a l && nodupB l

/-- The cartesian product of a list of lists. -/
def seqL {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | l :: ls => l.flatMap fun a => (seqL ls).map (a :: ·)

/-- The orders of a list without repetitions: its permutations, as the repetition-free lists of
its length over its elements. -/
def arrangements {α : Type} [DecidableEq α] (w : List α) : List (List α) :=
  (seqL (w.map fun _ => w)).filter nodupB

/-! ## Observables and outcomes -/

/-- An observable of a final condition: a register at a width, or a little-endian memory span. -/
inductive Key where
  | reg (thread : Nat) (r : Reg) (bits : Nat)
  | mem (addr size : Nat)
  deriving DecidableEq, Repr

/-- The observable an atom compares. -/
def Atom.key : Atom → Key
  | .reg t r bits _ => .reg t r bits
  | .mem a n _ => .mem a n

/-- The value an atom compares with. -/
def Atom.value : Atom → Nat
  | .reg _ _ _ v => v
  | .mem _ _ v => v

/-- The atoms of a formula. -/
def Cond.atoms : Cond → List Atom
  | .tt => []
  | .atom a => [a]
  | .not p => p.atoms
  | .and p q => p.atoms ++ q.atoms
  | .or p q => p.atoms ++ q.atoms

/-- The value of an observable in a final state. -/
def Key.eval (f : Final) : Key → Option Nat
  | .reg t r bits => some ((f.regs t r).toNat % 2 ^ bits)
  | .mem a n => leValue f.mem a n

/-- A formula evaluated from the values of its observables. -/
def Cond.evalK (g : Key → Option Nat) : Cond → Bool
  | .tt => true
  | .atom a => g a.key == some a.value
  | .not p => !p.evalK g
  | .and p q => p.evalK g && q.evalK g
  | .or p q => p.evalK g || q.evalK g

/-- The observables of a test's condition, without repetition. -/
def Test.keys (t : Test) : List Key := uniq (t.cond.atoms.map Atom.key)

/-- An outcome: the values of the test's observables. -/
abbrev Outcome := List (Option Nat)

/-- The outcome of a final state. -/
def Test.outcome (t : Test) (f : Final) : Outcome := t.keys.map (Key.eval f)

/-- The witness, evaluated on an outcome. -/
def Test.witnessOn (t : Test) (o : Outcome) : Bool :=
  t.witness.evalK fun k => ((t.keys.zip o).lookup k).getD none

/-- The verdict of a list of outcomes: allowed iff one satisfies the witness. -/
def Test.verdictOf (t : Test) (os : List Outcome) : Verdict :=
  if os.any t.witnessOn then .allowed else .forbidden

/-- Two outcome lists have the same members. -/
def sameSet (a b : List Outcome) : Bool := a.all (memB · b) && b.all (memB · a)

/-! ## Threads and traces -/

/-- Thread `k` of a test as an extraction thread: its bytes at `codeBase k`, the data page and
the code pages, and its initial registers. -/
def Test.xthread (t : Test) (k : Nat) (th : Thread) : Silmaril.X86.Litmus.Thread where
  base := Silmaril.X86.Litmus.codeBase k
  code := th.code
  regions := Silmaril.X86.Litmus.testRegions t.threads.length
  init := Silmaril.X86.Litmus.initCore (Silmaril.X86.Litmus.codeBase k)
    (th.regs.map fun p => (p.1, BitVec.ofNat 64 p.2))

/-- Instructions per thread, plus one. -/
def Test.fuel (t : Test) : Nat := t.threads.foldl (fun m th => max m th.insns.length) 0 + 1

/-- Every thread's candidate traces over the value domain `dom`. -/
def Test.extractOver (t : Test) (dom : List Nat) : Option (List (List XTrace)) :=
  (t.threads.mapIdx fun k th => Silmaril.X86.Litmus.extract (t.xthread k th) dom t.fuel).mapM id

/-- The values a trace writes. -/
def XTrace.written (tr : XTrace) : List Nat :=
  tr.acts.filterMap fun a => if a.ev.kind.writes then some a.wval else none

/-- Add every value an extracted trace writes. -/
def Test.domStep (t : Test) (d : List Nat) : List Nat :=
  match t.extractOver d with
  | none => d
  | some T => uniq (d ++ T.flatten.flatMap XTrace.written)

/-- `domStep`, at most `k` times, stopping when nothing new is written. -/
def Test.domIter (t : Test) : Nat → List Nat → List Nat
  | 0, d => d
  | k + 1, d =>
    let d' := t.domStep d
    if d'.length = d.length then d else t.domIter k d'

/-- The value domain: the initial values and the condition's values, extended (at most `n` times,
`n` the number of instructions, stopping early at a fixpoint) by the values the extracted traces
write. For tests with `xadd`/`inc` (for example `SB+lock-xadds` or `RMW+lock-inc+W`) no fixpoint is
reached and the `n`-step bound is what stops it. That this domain contains every value a
consistent execution reads is not proved. -/
def Test.domain (t : Test) : List Nat :=
  t.domIter (t.threads.flatMap Thread.insns).length
    (uniq ((t.locs.map Loc.init) ++ t.cond.atoms.map Atom.value))

/-- The candidate traces of every thread, extracted from the bytes over `Test.domain`. -/
def Test.traces (t : Test) : Option (List (List XTrace)) := t.extractOver t.domain

/-- The final state of a choice of traces, with memory `m`. -/
def finalOf (trs : List XTrace) (m : Nat → Option Byte) : Final :=
  ⟨fun i r => ((trs[i]?).map fun tr => tr.final.read r).getD 0, m⟩

/-! ## Operational x86-TSO -/

/-- The TSO events of one action of thread `i`. -/
def actX (i : Nat) (a : XAct) : List (XEvent Nat) :=
  match a.ev.kind with
  | .load => [.load i a.ev.addr a.rd]
  | .store => [.store i a.ev.addr a.wr]
  | .rmw =>
    if a.ev.locked then [.rmw i a.ev.addr a.rd a.wr]
    else [.load i a.ev.addr a.rd, .store i a.ev.addr a.wr]
  | .fence k => if k = .mfence then [.fence i] else []

/-- The TSO events of a trace of thread `i`. -/
def traceX (i : Nat) (tr : XTrace) : List (XEvent Nat) := tr.acts.flatMap (actX i)

/-- A configuration of the abstract run: each thread's remaining events and the TSO state. -/
structure ACfg where
  rest : List (List (XEvent Nat))
  st : XState Nat

/-- One step: some thread's next event (`Tso.XStep`), or one flush (`Tso.XFlush`). -/
inductive AStep : ACfg → ACfg → Prop
  | ev (rest : List (List (XEvent Nat))) (s s' : XState Nat) (i : Nat) (e : XEvent Nat)
      (es : List (XEvent Nat)) (h : rest[i]? = some (e :: es)) (hs : XStep s e s') :
      AStep ⟨rest, s⟩ ⟨rest.set i es, s'⟩
  | flush (rest : List (List (XEvent Nat))) (s s' : XState Nat) (h : XFlush s s') :
      AStep ⟨rest, s⟩ ⟨rest, s'⟩

/-- The initial TSO state of a test: its memory and empty buffers. -/
def Test.initX (t : Test) : XState Nat := ⟨t.initMem, fun _ => []⟩

/-- **Final states of operational x86-TSO**: one trace per thread runs to completion and every
buffer drains. -/
def OpReach (t : Test) (T : List (List XTrace)) (f : Final) : Prop :=
  ∃ trs : List XTrace, List.Forall₂ (· ∈ ·) trs T ∧ ∃ s : XState Nat,
    Relation.ReflTransGen AStep ⟨trs.mapIdx traceX, t.initX⟩ ⟨trs.map fun _ => [], s⟩ ∧
    (∀ k, s.buffer k = []) ∧ f = finalOf trs s.memory

/-! ### Concrete configurations -/

/-- Memory as an association list. -/
abbrev CMem := List (Nat × Byte)

/-- Read a byte. -/
def cget (m : CMem) (x : Nat) : Option Byte := m.lookup x

/-- Write a byte (in place if present, else appended). -/
def cset (m : CMem) (x : Nat) (b : Byte) : CMem :=
  if m.any (fun p => p.1 == x) then m.map (fun p => if p.1 == x then (x, b) else p)
  else m ++ [(x, b)]

/-- Write bytes from `a` up. -/
def cwrite : CMem → Nat → List Byte → CMem
  | m, _, [] => m
  | m, a, b :: bs => cwrite (cset m a b) (a + 1) bs

/-- The initial memory of the locations. -/
def initCMem (locs : List Loc) : CMem :=
  locs.flatMap fun l => (List.range l.size).map fun j => (l.addr + j, BitVec.ofNat 8 (l.init / 256 ^ j))

/-- The final values of a thread's observed registers. -/
abbrev RegObs := List (Reg × BitVec 64)

/-- A thread's candidates: remaining events and final observed registers. -/
abbrev Cand := List (List (XEvent Nat) × RegObs)

/-- A concrete configuration: per thread the candidates still consistent with what the thread
has done (with their remaining events), the buffers, and the memory. -/
structure CCfg where
  cand : List Cand
  bufs : List (List (Nat × List Byte))
  mem : CMem
  deriving DecidableEq

/-- Equality of configurations, comparing buffers and memory first (`ceq_iff`). -/
def CCfg.ceq (c d : CCfg) : Bool := c.bufs == d.bufs && c.mem == d.mem && c.cand == d.cand

/-- The TSO state a concrete configuration stands for. -/
def CCfg.xs (c : CCfg) : XState Nat := ⟨cget c.mem, fun k => c.bufs.getD k []⟩

/-- The possible next events of a thread. -/
def heads (cd : Cand) : List (XEvent Nat) := uniq (cd.filterMap fun p => p.1.head?)

/-- The candidates whose next event is `e`, after it. -/
def advance (cd : Cand) (e : XEvent Nat) : Cand :=
  cd.filterMap fun p =>
    match p.1 with
    | e' :: r => if e' = e then some (r, p.2) else none
    | [] => none

/-- The effect of an event on buffers and memory, if `Tso.XStep` enables it. -/
def CCfg.fire (c : CCfg) : XEvent Nat → Option CCfg
  | .load k a bs =>
    if k < c.bufs.length ∧ Tso.readView c.xs k a bs.length = some bs then some c else none
  | .store k a bs =>
    if k < c.bufs.length then some { c with bufs := c.bufs.set k (c.bufs.getD k [] ++ [(a, bs)]) }
    else none
  | .rmw k a old new =>
    if k < c.bufs.length ∧ c.bufs.getD k [] = [] ∧ Tso.readMem (cget c.mem) a old.length = some old ∧
        new.length = old.length then some { c with mem := cwrite c.mem a new }
    else none
  | .fence k => if k < c.bufs.length ∧ c.bufs.getD k [] = [] then some c else none

/-- Flush successors: the oldest entry of one buffer reaches memory. -/
def CCfg.flushes (c : CCfg) : List CCfg :=
  (List.range c.bufs.length).filterMap fun k =>
    match c.bufs.getD k [] with
    | (a, bs) :: rest => some { c with mem := cwrite c.mem a bs, bufs := c.bufs.set k rest }
    | [] => none

/-- Event successors: one thread's next event. -/
def CCfg.events (c : CCfg) : List CCfg :=
  (List.range c.cand.length).flatMap fun i =>
    (heads (c.cand.getD i [])).filterMap fun e =>
      (c.fire e).map fun c' => { c' with cand := c.cand.set i (advance (c.cand.getD i []) e) }

/-- All successors. -/
def CCfg.succ (c : CCfg) : List CCfg := c.flushes ++ c.events

/-- The finished candidates of a thread. -/
def finished (cd : Cand) : List RegObs := cd.filterMap fun p => if p.1.isEmpty then some p.2 else none

/-- The final state of finished observed registers. -/
def obsFinal (os : List RegObs) (m : Nat → Option Byte) : Final :=
  ⟨fun i r => ((os.getD i []).lookup r).getD 0, m⟩

/-- The outcomes of a configuration that has finished and drained. -/
def CCfg.outs (t : Test) (c : CCfg) : List Outcome :=
  if c.bufs.all List.isEmpty then
    (seqL (c.cand.map finished)).map fun os => t.outcome (obsFinal os (cget c.mem))
  else []

/-- Membership up to a Boolean equality. -/
def memBy {α : Type} (eq : α → α → Bool) (a : α) : List α → Bool
  | [] => false
  | b :: l => if eq a b then true else memBy eq a l

/-- Remove repetitions up to a Boolean equality. -/
def uniqBy {α : Type} (eq : α → α → Bool) (l : List α) : List α :=
  l.foldr (fun a r => if memBy eq a r then r else a :: r) []

/-- One level of a breadth-first search, without repetitions. -/
def stepL {α : Type} (eq : α → α → Bool) (succ : α → List α) (L : List α) : List α :=
  uniqBy eq (L.flatMap succ)

/-- Collect `fin` over the states reachable from `L`, `k` levels deep; `none` unless the last
level is empty (so every state reachable at all was visited). -/
def collect {α β : Type} (eq : α → α → Bool) (succ : α → List α) (fin : α → List β) :
    Nat → List α → Option (List β)
  | 0, L => if L.isEmpty then some [] else none
  | k + 1, L => (collect eq succ fin k (stepL eq succ L)).map (L.flatMap fin ++ ·)

/-- The registers of thread `i` the condition observes. -/
def Test.obsRegs (t : Test) (i : Nat) : List Reg :=
  t.keys.filterMap fun
    | .reg j r _ => if j = i then some r else none
    | .mem .. => none

/-- The candidates of thread `i`: each trace's events and observed final registers. -/
def Test.candOf (t : Test) (i : Nat) (trs : List XTrace) : Cand :=
  trs.map fun tr => (traceX i tr, (t.obsRegs i).map fun r => (r, tr.final.read r))

/-- The initial concrete configuration: every trace a candidate, empty buffers. -/
def Test.c0 (t : Test) (T : List (List XTrace)) : CCfg :=
  ⟨T.mapIdx t.candOf, T.map fun _ => [], initCMem t.locs⟩

/-- Every event of every candidate names a thread that has a buffer. -/
def CCfg.threadsOk (c : CCfg) : Bool :=
  c.cand.all fun cd => cd.all fun p => p.1.all fun e => decide (e.thread < c.bufs.length)

/-- A bound on the length of every run: each event and each flush is one step. -/
def opBound (T : List (List XTrace)) : Nat :=
  2 * ((T.mapIdx fun i trs => trs.foldl (fun m tr => max m (traceX i tr).length) 0).sum) + 2

/-- **The operational TSO outcomes**, by exhaustive search (`none`: the bound was too small or
an event names a thread that does not exist). -/
def Test.opOut (t : Test) (T : List (List XTrace)) : Option (List Outcome) :=
  if (t.c0 T).threadsOk then
    (collect CCfg.ceq CCfg.succ (CCfg.outs t) (opBound T) [t.c0 T]).map uniq
  else none

/-! ## Axiomatic SC, TSO and XL -/

/-- The annotation of an litmus flavour. -/
def annOf : Silmaril.X86.Litmus.Flavor → Ann
  | .plain => .wb
  | .nonTemporal => .nt
  | .string => .str

/-- The units of one action of thread `i` at program position `p`, each with the bytes it must
read (`[]` for non-reads). A read-modify-write is a read at `p` and a write at `p + 1`. -/
def actUnits (i p : Nat) (a : XAct) : List (Ev × List Byte) :=
  let u (k : Nat) (act : Axiomatic.Act) (d : List Byte) : Ev :=
    { tid := i, pos := p + k, act, addr := a.ev.addr, size := a.ev.size, locked := a.ev.locked,
      ann := annOf a.flavor, data := d }
  match a.ev.kind with
  | .load => [(u 0 .read [], a.rd)]
  | .store => [(u 0 .write a.wr, [])]
  | .rmw => [(u 0 .read [], a.rd), (u 1 .write a.wr, [])]
  | .fence k => [({ tid := i, pos := p, act := .fence k }, [])]

/-- The units of a thread's actions from position `p`. -/
def threadUnits (i : Nat) : Nat → List XAct → List (Ev × List Byte)
  | _, [] => []
  | p, a :: as => actUnits i p a ++ threadUnits i (p + (actUnits i p a).length) as

/-- The unsplit units of a choice of traces. -/
def accUnits (trs : List XTrace) : List (Ev × List Byte) :=
  (trs.mapIdx fun i tr => threadUnits i 0 tr.acts).flatten

/-- An access that may tear: misaligned or wide, or overlapping an access of another footprint. -/
def tearAcc (us : List (Ev × List Byte)) (u : Ev) : Bool :=
  u.isM && (!u.singleCopy ||
    us.any fun v => v.1.isM && u.accOverlap v.1 && (u.addr != v.1.addr || u.size != v.1.size))

/-- Split a unit into byte units (same thread, position and access footprint). -/
def splitUnit (u : Ev × List Byte) : List (Ev × List Byte) :=
  u.1.bytes.map fun y =>
    ({ u.1 with addr := y, size := 1, data := if u.1.act == .write then [u.1.byte y] else [] },
      if u.1.isR then [(u.2[y - u.1.addr]?).getD 0] else [])

/-- The units of a choice of traces: tearable accesses split into bytes. -/
def units (trs : List XTrace) : List (Ev × List Byte) :=
  let us := accUnits trs
  us.flatMap fun u => if tearAcc us u.1 then splitUnit u else [u]

/-- The unit the axiomatic models use out of range (`Exec.evN`). -/
def dummyEv : Ev := { tid := 0, pos := 0, act := .fence .lfence }

/-- The indices of the units satisfying `p`. -/
def idxs (evs : List Ev) (p : Ev → Bool) : List Nat :=
  (List.range evs.length).filter fun i => p (evs.getD i dummyEv)

/-- The locked read-modify-write pairs: a locked read and the locked write right after it in its
thread, on the same bytes. -/
def rmwPairs (evs : List Ev) : List (Nat × Nat) :=
  evs.zipIdx.flatMap fun qa =>
    if qa.1.isR && qa.1.locked then
      evs.zipIdx.filterMap fun qb =>
        if qb.1.isW && qb.1.locked && qa.1.tid == qb.1.tid && qb.1.pos == qa.1.pos + 1 &&
            qa.1.addr == qb.1.addr && qa.1.size == qb.1.size then some (qa.2, qb.2) else none
    else []

/-- Two memory units are in one cell or touch disjoint bytes. -/
def cellsOk (evs : List Ev) : Bool :=
  let ms := evs.filter Ev.isM
  ms.all fun a => ms.all fun b =>
    (a.addr == b.addr && a.size == b.size) ||
      !(decide (a.addr < b.addr + b.size) && decide (b.addr < a.addr + a.size))

/-- The cells: footprints of memory units. -/
def cellsOf (evs : List Ev) : List (Nat × Nat) :=
  uniq ((evs.filter Ev.isM).map fun e => (e.addr, e.size))

/-- The write units of a cell. -/
def writesIn (evs : List Ev) (c : Nat × Nat) : List Nat :=
  idxs evs fun e => e.isW && e.addr == c.1 && e.size == c.2

/-- The read units. -/
def readsOf (evs : List Ev) : List Nat := idxs evs Ev.isR

/-- The initial byte at an address (`0` if unmapped). -/
def Test.initB (t : Test) (y : Nat) : Byte := (t.initMem y).getD 0

/-- The bytes read unit `r` gets from source `s` (`none`: the initial value). -/
def srcBytes (t : Test) (evs : List Ev) (r : Nat) (s : Option Nat) : List Byte :=
  (evs.getD r dummyEv).bytes.map fun y =>
    match s with
    | none => t.initB y
    | some w => (evs.getD w dummyEv).byte y

/-- The sources of read unit `r` that give it its expected bytes. -/
def rfChoices (t : Test) (evs : List Ev) (exps : List (List Byte)) (r : Nat) : List (Option Nat) :=
  (none :: (writesIn evs ((evs.getD r dummyEv).addr, (evs.getD r dummyEv).size)).map some).filter
    fun s => srcBytes t evs r s == exps.getD r []

/-- The execution of an `rf` choice per read unit and a `co` order per cell. -/
def mkExec (evs : List Ev) (rmw : List (Nat × Nat)) (rfA : List (Nat × Option Nat))
    (coA : List ((Nat × Nat) × List Nat)) : Exec where
  evs := evs
  rf := fun r _ => (rfA.lookup r).getD none
  co := fun y =>
    ((coA.find? fun p => decide (p.1.1 ≤ y) && decide (y < p.1.1 + p.1.2)).map Prod.snd).getD []
  rmw := rmw

/-- The candidate executions over a list of units. -/
def candidates (t : Test) (evs : List Ev) (exps : List (List Byte)) (rmw : List (Nat × Nat)) :
    List Exec :=
  let rs := readsOf evs
  let cs := cellsOf evs
  (seqL (rs.map (rfChoices t evs exps))).flatMap fun rfc =>
    (seqL (cs.map fun c => arrangements (writesIn evs c))).map fun coc =>
      mkExec evs rmw (rs.zip rfc) (cs.zip coc)

/-- Every read unit returns its expected bytes. -/
def ReadsOk (t : Test) (x : Exec) (exps : List (List Byte)) : Prop :=
  ∀ r < x.n, (x.evN r).isR = true → x.readBytes t.initB r = exps.getD r []

/-- `ReadsOk` as a Boolean. -/
def readsOkB (t : Test) (x : Exec) (exps : List (List Byte)) : Bool :=
  (List.range x.n).all fun r => !(x.evN r).isR || x.readBytes t.initB r == exps.getD r []

/-- Some write unit covers byte `y`. -/
def writtenByte (x : Exec) (y : Nat) : Bool := x.evs.any fun e => e.isW && e.covers y

/-- The final state of a candidate: the chosen traces' registers; a written byte is its
coherence-last write, any other byte its initial value. -/
def finalAx (t : Test) (trs : List XTrace) (x : Exec) : Final :=
  finalOf trs fun y => if writtenByte x y then some (x.finalByte t.initB y) else t.initMem y

/-- **Final states of an axiomatic model** `M`: one trace per thread and a well-formed candidate
over their units whose reads return the traces' bytes, consistent under `M`. -/
def AxReach (t : Test) (T : List (List XTrace)) (M : Exec → Prop) (f : Final) : Prop :=
  ∃ trs : List XTrace, List.Forall₂ (· ∈ ·) trs T ∧ ∃ x : Exec,
    x.evs = (units trs).map Prod.fst ∧ x.rmw = rmwPairs ((units trs).map Prod.fst) ∧
    x.Wf = true ∧ ReadsOk t x ((units trs).map Prod.snd) ∧ M x ∧ f = finalAx t trs x

/-- A judged candidate: consistent under SC, TSO, XL, and its outcome. -/
structure Judged where
  sc : Bool
  tso : Bool
  xl : Bool
  out : Outcome
  deriving DecidableEq, Repr

/-- Judge a candidate (only well-formed XL-consistent candidates whose reads are right). On a
tame candidate XL is TSO (`Exec.xl_iff_tso_of_tame`), so XL is only checked on the others. -/
def judge (t : Test) (trs : List XTrace) (exps : List (List Byte)) (x : Exec) : Option Judged :=
  let tso := decide x.Tso
  let xl := tso || (!decide x.Tame && decide x.Xl)
  if xl && x.Wf && readsOkB t x exps then
    some ⟨tso && decide x.Sc, tso, xl, t.outcome (finalAx t trs x)⟩
  else none

/-- The judged candidates of one choice of traces (`none` if two units overlap partially). -/
def judgeCombo (t : Test) (trs : List XTrace) : Option (List Judged) :=
  let us := units trs
  let evs := us.map Prod.fst
  let exps := us.map Prod.snd
  if cellsOk evs then some ((candidates t evs exps (rmwPairs evs)).filterMap (judge t trs exps))
  else none

/-- **The judged candidates of every choice of traces.** -/
def Test.axJudge (t : Test) (T : List (List XTrace)) : Option (List Judged) :=
  ((seqL T).mapM (judgeCombo t)).map List.flatten

/-- The outcomes of the judged candidates consistent under a model. -/
def outsBy (js : List Judged) (p : Judged → Bool) : List Outcome :=
  uniq ((js.filter p).map Judged.out)

/-- The three axiomatic models. -/
inductive Model where
  | sc
  | tso
  | xl
  deriving DecidableEq, Repr

/-- The consistency predicate of a model. -/
def Model.Holds : Model → Exec → Prop
  | .sc => Exec.Sc
  | .tso => Exec.Tso
  | .xl => Exec.Xl

/-- The flag of a judged candidate for a model. -/
def Model.sel : Model → Judged → Bool
  | .sc => Judged.sc
  | .tso => Judged.tso
  | .xl => Judged.xl

/-! ## Per-test checks -/

/-- The check behind a TSO-covered test's verdict theorem: the operational TSO outcomes and the
axiomatic TSO outcomes are the same set, and the TSO, SC and XL verdicts are the recorded ones.
The SC outcome list must be nonempty, so that no `forbidden` verdict holds vacuously (for example
because a thread has no trace or the operational machine gets stuck). -/
def Test.checkTso (t : Test) (T : List (List XTrace)) : Bool :=
  match t.opOut T, t.axJudge T with
  | some os, some js =>
    sameSet os (outsBy js Model.tso.sel) &&
      t.tso == some (t.verdictOf (outsBy js Model.tso.sel)) &&
      t.sc == some (t.verdictOf (outsBy js Model.sc.sel)) &&
      t.xl == t.verdictOf (outsBy js Model.xl.sel) &&
      !(outsBy js Model.sc.sel).isEmpty
  | _, _ => false

/-- `checkTso` on the traces extracted from the bytes. -/
def Test.checkTsoBytes (t : Test) : Bool :=
  match t.traces with
  | some T => t.checkTso T
  | none => false

/-- The check behind a loose-corner test's verdict theorem: the XL verdict is the recorded one. -/
def Test.checkXl (t : Test) (T : List (List XTrace)) : Bool :=
  match t.axJudge T with
  | some js => t.xl == t.verdictOf (outsBy js Model.xl.sel)
  | none => false

/-- The check behind a loose corner whose writer is given by hand: the XL verdict is the
recorded one, axiomatic TSO and SC forbid the witness, and the SC outcome list is nonempty (so
the `forbidden` verdicts are not vacuous). -/
def Test.checkLoose (t : Test) (T : List (List XTrace)) : Bool :=
  match t.axJudge T with
  | some js =>
    t.xl == t.verdictOf (outsBy js Model.xl.sel) &&
      t.verdictOf (outsBy js Model.tso.sel) == .forbidden &&
      t.verdictOf (outsBy js Model.sc.sel) == .forbidden &&
      !(outsBy js Model.sc.sel).isEmpty
  | none => false

/-- The check behind a plain loose-corner test (mixed-size or misaligned, no non-temporal or
string stores): operational and axiomatic TSO have the same outcomes and forbid the witness,
axiomatic SC forbids it, the XL verdict is the recorded one, and the SC outcome list is nonempty. -/
def Test.checkPlainLoose (t : Test) (T : List (List XTrace)) : Bool :=
  match t.opOut T, t.axJudge T with
  | some os, some js =>
    sameSet os (outsBy js Model.tso.sel) &&
      t.verdictOf (outsBy js Model.tso.sel) == .forbidden &&
      t.xl == t.verdictOf (outsBy js Model.xl.sel) &&
      t.verdictOf (outsBy js Model.sc.sel) == .forbidden &&
      !(outsBy js Model.sc.sel).isEmpty
  | _, _ => false

/-- What a TSO-covered test's verdict theorem states, for the trace sets `T`: operational TSO
and axiomatic TSO have the same outcomes; the recorded TSO verdict holds in both; the recorded SC
verdict holds in axiomatic SC; the recorded XL verdict holds in XL. -/
structure TsoVerdicts (t : Test) (T : List (List XTrace)) : Prop where
  op_eq_ax : ∀ o, (∃ f, OpReach t T f ∧ t.outcome f = o) ↔
    (∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o)
  tso_op : ∀ v, t.tso = some v → v.Holds t (OpReach t T)
  tso_ax : ∀ v, t.tso = some v → v.Holds t (AxReach t T Exec.Tso)
  sc_ax : ∀ v, t.sc = some v → v.Holds t (AxReach t T Exec.Sc)
  xl_ax : t.xl.Holds t (AxReach t T Exec.Xl)
  /-- Some SC execution exists, so the verdicts are not vacuous (with `op_eq_ax` and SC ⊆ TSO,
  operational TSO reaches some final state too). -/
  sc_some : ∃ f, AxReach t T Exec.Sc f

end Silmaril.X86.MemoryModel.Litmus
