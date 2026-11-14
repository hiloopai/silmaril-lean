module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs

/-!
# CIR: a small concurrency IR — syntax, event semantics, concurrent machine

CIR is the IR that
x86 code with atomics, fences, futexes and threads is translation-validated into, so that all
concurrency reasoning (litmus verdicts, C11 correspondence, separation logic, primitives,
programs) is done on small CIR programs instead of on the decoded machine.

## Syntax (`Stmt`)

* `load dst m sz fl a`, `store m sz fl a v`: an access of `sz` bytes at address `a`, with a
  C11 **mode** `m` (`na`, `rlx`, `acq`, `rel`, `sc`) and an x86 **flavour** `fl` (write-back,
  non-temporal, string; `Axiomatic.Ann`);
* `rmw dst m sz op a arg`: a locked read-modify-write (`xchg`, `fadd`, `cas expected`, or a
  generic locked binary operation); `dst` gets the old value;
* `fence k`: an x86 fence (`mfence`, `lfence`, `sfence`);
* `futexWait dst a v`, `futexWake a n`; `spawn t`, `join t`;
* `assign`, `seq`, `ite`, and **bounded** loops `loop n c body` (at most `n` iterations of
  `while c do body`; a run that would need more is not a run);
* `local B`: an opaque thread-local block, summarised by a sequential contract `B.spec` over an
  owned footprint (cells read `B.ins`, cells written `B.outs`, registers `B.rin`/`B.rout`).

Registers are the sixteen x86 GPR names with 64-bit values: translation validation from x86 then
needs no register map.

## Modes are annotations

The x86 meaning of an access is its **op**: `load`/`store` are plain `mov`s, `rmw` is a locked
instruction, and fences are explicit. The mode is the C11 intent, kept in the trace for the later
C11 correspondence and for race-freedom (`na` accesses must not race); it does not change the
x86 events. That a mode is implemented correctly (for example, an `sc` store followed by
`mfence`, or done by `xchg`) is a separate, later check.

## Event semantics (`run`)

`run dom s rs` lists the runs of `s` from registers `rs` in which every read returns a value of
the **domain** `dom` (that fits in the access): each run is its trace of labels (`Lab`) and its
final registers. A trace records the values read and written. The thread semantics is "some
domain": `ThreadRun s rs tr rs' := ∃ dom, (tr, rs') ∈ run dom s rs`; every finite run reads
finitely many values, so this is every run. The litmus checker fixes one domain.

## Lowering to candidate-execution events

`Lab.acts` lowers a label to litmus memory actions (`X86.Litmus.Act`), and `units` turns those
into herd-style access units (`Axiomatic.Ev`), so CIR runs are judged by exactly the
SC/TSO/XL machinery:

* loads/stores: one plain access; `rmw`: one locked RMW (read and write units, paired by
  `rmwPairs`); fences: one fence unit;
* **sync events** on two ghost **control bytes** per thread, outside every location: the start
  byte `ctlAddr t` and the end byte `endAddr t`. `spawn t` is a locked RMW `0 → 1` of the start
  byte and the child's start is `1 → 2`; the child's end is a locked RMW `0 → 1` of the end
  byte and `join t` is `1 → 2`. Locked RMWs order everything around them in all three models
  (`lockXl`, `implied`), and `rf` from the spawn to the start (and from the end to the join)
  gives the happens-before edges of `spawn`/`join` (`Cir.Sync`: the explicit
  edges are implied). Two bytes with two writes each, rather than one byte with four
  (`0 → 1 → 2 → 3 → 4`), cut the coherence orders the enumerator tries per
  thread from `4! = 24` to `2 · 2 = 4`.
* **futexes** (`Cir.Futex`): every futex word `a` has a ghost one-byte **waiter
  queue** `qAddr a` (`1`: a waiter is queued), outside every location. The kernel's check is a
  sequentially consistent access: a plain load of the word between full barriers.
  - `futexWait a v` when the word is not `v`: `mfence; load a; mfence`, and the result is
    `EAGAIN` (11);
  - when the word is `v`: `mfence; store q 1` (enqueue) `; mfence; load a` (the check)
    `; rmw q r → 0` (dequeue) and the result is `0`. The dequeue reads `r = 0` when a wake
    emptied the queue (**woken**: `rf` from the wake, the `sw` edge `Exec.fsw`) and `r = 1`
    when nothing did (**spurious** wake-up, which Linux allows);
  - `futexWake a n`: `mfence; rmw q _ → 0; mfence` (empty the queue);
  - a wait that **never returns** (label `fblock`, only at the end of a blocked thread's trace,
    `Futex.Prog.btraces`): `mfence; store q 1; mfence; load a`. A final queue byte `1` after a
    blocked waiter means no wake came after its enqueue: a **lost wake-up**.

  Enqueue-then-check is the Dekker handshake that makes wake-ups not get lost: if a wake's
  `rmw q` is coherence-before the waiter's enqueue, every store before the wake is visible to
  the check. The queue is one byte per word, so it is exact when at most one thread waits on
  a word at a time.
* `local B`: plain reads of `B.ins`, then plain writes of `B.outs`. Under ownership (the
  footprint is not touched by other threads) the order inside the block is unobservable.

## Concurrent machine

`Prog`: locations (`Litmus.Loc`) and threads, each a body and whether it is `spawned`
(it then starts with the start event and ends with the end event). `BehavIn P dom M f`:
`AxReach` over the per-thread traces `P.traces dom` under the axiomatic model `M`;
`Behav P M f := ∃ dom, BehavIn P dom M f`.

## Sequential semantics

`SeqRun s rs m tr rs' m'`: a thread run whose trace replays on one flat memory (`replay`:
every read returns the current bytes, writes update them). The statement that a single-thread,
spawn-free program's SC behaviours are its sequential runs is `Task.cirSeqSc`
(proved: `Cir.Seq.cirSeqSc`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus (Byte Loc Final Test XTrace XAct seqL leValue initByte AxReach)
open Silmaril.X86.MemoryModel.Axiomatic (Exec Ann)
open Silmaril.X86.Atomic9 (FenceKind)
open Silmaril.X86.MemEvent (Event Kind)

/-! ## Syntax -/

/-- Registers: the x86 general-purpose registers. -/
abbrev Reg := Silmaril.X86.Reg

/-- A register value. -/
abbrev Word := BitVec 64

/-- A register file. -/
abbrev Regs := Reg → Word

/-- All registers zero. -/
def Regs.zero : Regs := fun _ => 0

/-- Set one register. -/
def Regs.set (rs : Regs) (r : Reg) (v : Word) : Regs := fun q => if q = r then v else rs q

/-- Set several registers. -/
def Regs.setMany (rs : Regs) : List Reg → List Nat → Regs
  | r :: l, v :: vs => (rs.set r (BitVec.ofNat 64 v)).setMany l vs
  | _, _ => rs

/-- C11 access modes. `acqRel` is the mode of an acquire-release read-modify-write
(`__ATOMIC_ACQ_REL`): its read is acquire and its write release. -/
inductive Mode where
  | na
  | rlx
  | acq
  | rel
  | sc
  | acqRel
  deriving DecidableEq, Repr

/-- The x86 flavour of an access: write-back, non-temporal, string. -/
abbrev Flav := Ann

/-- Binary operations on register values. -/
inductive BinOp where
  | add
  | sub
  | and
  | or
  | xor
  | eq
  | ne
  | ltu
  deriving DecidableEq, Repr

/-- Evaluate a binary operation (comparisons give `1` or `0`). -/
def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .ltu, a, b => if a.toNat < b.toNat then 1 else 0

/-- Register expressions. -/
inductive Expr where
  | lit (v : Nat)
  | reg (r : Reg)
  | bin (o : BinOp) (a b : Expr)
  deriving DecidableEq, Repr

/-- Evaluate an expression. -/
def Expr.eval (rs : Regs) : Expr → Word
  | .lit v => BitVec.ofNat 64 v
  | .reg r => rs r
  | .bin o a b => o.eval (a.eval rs) (b.eval rs)

/-- The read-modify-write operations. -/
inductive RmwOp where
  /-- `xchg`: write the argument. -/
  | xchg
  /-- `lock xadd`: add the argument. -/
  | fadd
  /-- `lock cmpxchg`: write the argument if the old value is `expected`; otherwise write the
  old value back (x86 always writes). -/
  | cas (expected : Expr)
  /-- A generic locked operation `old ∘ arg` (`lock and/or/xor/sub ...`). -/
  | op (o : BinOp)
  deriving DecidableEq, Repr

/-- An opaque thread-local block: a sequential contract over an owned footprint. `spec`
relates the values of `rin` then `ins` (cells, in order) to the values of `rout` then `outs`. -/
structure Block where
  name : String
  ins : List (Nat × Nat)
  outs : List (Nat × Nat)
  rin : List Reg
  rout : List Reg
  spec : List Nat → List Nat → Prop
  dec : ∀ a b, Decidable (spec a b)

/-- CIR statements. -/
inductive Stmt where
  | skip
  | assign (dst : Reg) (e : Expr)
  | load (dst : Reg) (m : Mode) (sz : Nat) (fl : Flav) (a : Expr)
  | store (m : Mode) (sz : Nat) (fl : Flav) (a : Expr) (v : Expr)
  | rmw (dst : Reg) (m : Mode) (sz : Nat) (op : RmwOp) (a : Expr) (arg : Expr)
  | fence (k : FenceKind)
  | futexWait (dst : Reg) (a : Expr) (v : Expr)
  | futexWake (a : Expr) (n : Expr)
  | spawn (t : Nat)
  | join (t : Nat)
  | local (b : Block)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  | loop (n : Nat) (c : Expr) (body : Stmt)

/-- Sequence a list of statements. -/
def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: l => .seq s (Stmt.block l)

/-! ## Labels -/

/-- One event of a thread trace. Values are the little-endian values of the bytes. -/
inductive Lab where
  | rd (m : Mode) (fl : Flav) (a sz v : Nat)
  | wr (m : Mode) (fl : Flav) (a sz v : Nat)
  | rmw (m : Mode) (a sz old new : Nat)
  | fence (k : FenceKind)
  /-- A futex wait on `a` expecting `exp`, which saw `seen`; when it slept (`seen = exp`), its
  dequeue read `r` from the queue byte (`0`: woken, `1`: spurious). -/
  | fwait (a exp seen r : Nat)
  /-- A futex wake of `n` waiters on `a`, which read `q` from the queue byte. -/
  | fwake (a n q : Nat)
  /-- A futex wait on `a` expecting `exp` that saw `exp` and never returns (only as the last
  label of a blocked thread). -/
  | fblock (a exp : Nat)
  | spawn (t : Nat)
  | join (t : Nat)
  /-- A local block, with the (address, size, value) of each cell read and written and the
  values of its output registers. -/
  | blk (name : String) (ins outs : List (Nat × Nat × Nat)) (rvs : List Nat)
  deriving DecidableEq, Repr

/-- The values a label writes, and the output register values of a local block (the values
that do not come from a read; for the domain iteration). -/
def Lab.written : Lab → List Nat
  | .wr _ _ _ _ v => [v]
  | .rmw _ _ _ _ n => [n]
  | .blk _ _ outs rvs => outs.map (fun c => c.2.2) ++ rvs
  | .fwait _ e s _ => if s = e then [1, 0] else []
  | .fwake _ _ _ => [0]
  | .fblock _ _ => [1]
  | _ => []

/-! ## Thread semantics -/

/-- The values of `dom` that fit in `sz` bytes. -/
def pick (dom : List Nat) (sz : Nat) : List Nat := dom.filter fun v => decide (v < 2 ^ (8 * sz))

/-- The values a futex queue byte may hold: `0` and `1` (of the domain). Only futex operations
write queue bytes, and they write `0` or `1`. -/
def qpick (dom : List Nat) : List Nat := (pick dom 1).filter fun v => decide (v < 2)

/-- Runs: traces with final registers. -/
abbrev Res := List (List Lab × Regs)

/-- Continue every run with `k`. -/
def Res.bind (x : Res) (k : Regs → Res) : Res :=
  x.flatMap fun p => (k p.2).map fun q => (p.1 ++ q.1, q.2)

/-- A value is true (nonzero). -/
def truthy (w : Word) : Bool := w != 0

/-- `while c do body`, at most `n` times; no run if `c` still holds after `n` iterations. -/
def iter (body : Regs → Res) (c : Expr) : Nat → Regs → Res
  | 0, rs => if truthy (c.eval rs) then [] else [([], rs)]
  | n + 1, rs =>
    if truthy (c.eval rs) then Res.bind (body rs) (iter body c n) else [([], rs)]

/-- The new value of a read-modify-write. -/
def RmwOp.result (rs : Regs) (sz old : Nat) (arg : Word) : RmwOp → Nat
  | .xchg => arg.toNat % 2 ^ (8 * sz)
  | .fadd => (old + arg.toNat) % 2 ^ (8 * sz)
  | .cas e => if old = (e.eval rs).toNat % 2 ^ (8 * sz) then arg.toNat % 2 ^ (8 * sz) else old
  | .op o => (o.eval (BitVec.ofNat 64 old) arg).toNat % 2 ^ (8 * sz)

/-- `EAGAIN`. -/
def eagain : Nat := 11

/-- Pair cells with values. -/
def cellVals : List (Nat × Nat) → List Nat → List (Nat × Nat × Nat)
  | c :: cs, v :: vs => (c.1, c.2, v) :: cellVals cs vs
  | _, _ => []

/-- The runs of a local block: input cell values and outputs from the domain, kept when the
contract relates them. -/
def runBlock (dom : List Nat) (b : Block) (rs : Regs) : Res :=
  let rin := b.rin.map fun r => (rs r).toNat
  (seqL (b.ins.map fun c => pick dom c.2)).flatMap fun ivs =>
    (seqL (b.rout.map fun _ => dom)).flatMap fun rvs =>
      (seqL (b.outs.map fun c => pick dom c.2)).filterMap fun ovs =>
        if @decide (b.spec (rin ++ ivs) (rvs ++ ovs)) (b.dec _ _) then
          some ([.blk b.name (cellVals b.ins ivs) (cellVals b.outs ovs) rvs], rs.setMany b.rout rvs)
        else none

/-- **The runs of a statement** in which every read returns a value of `dom`. -/
def run (dom : List Nat) : Stmt → Regs → Res
  | .skip, rs => [([], rs)]
  | .assign d e, rs => [([], rs.set d (e.eval rs))]
  | .load d m sz fl a, rs =>
    (pick dom sz).map fun v => ([.rd m fl (a.eval rs).toNat sz v], rs.set d (BitVec.ofNat 64 v))
  | .store m sz fl a v, rs => [([.wr m fl (a.eval rs).toNat sz ((v.eval rs).toNat % 2 ^ (8 * sz))], rs)]
  | .rmw d m sz op a arg, rs =>
    (pick dom sz).map fun old =>
      ([.rmw m (a.eval rs).toNat sz old (op.result rs sz old (arg.eval rs))],
        rs.set d (BitVec.ofNat 64 old))
  | .fence k, rs => [([.fence k], rs)]
  | .futexWait d a v, rs =>
    (pick dom 4).flatMap fun seen =>
      let exp := (v.eval rs).toNat % 2 ^ 32
      if seen = exp then
        (qpick dom).map fun r => ([.fwait (a.eval rs).toNat exp seen r], rs.set d 0)
      else [([.fwait (a.eval rs).toNat exp seen 0], rs.set d (BitVec.ofNat 64 eagain))]
  | .futexWake a n, rs =>
    (qpick dom).map fun q => ([.fwake (a.eval rs).toNat (n.eval rs).toNat q], rs)
  | .spawn t, rs => [([.spawn t], rs)]
  | .join t, rs => [([.join t], rs)]
  | .local b, rs => runBlock dom b rs
  | .seq s t, rs => Res.bind (run dom s rs) (run dom t)
  | .ite c s t, rs => if truthy (c.eval rs) then run dom s rs else run dom t rs
  | .loop n c body, rs => iter (run dom body) c n rs

/-- **The thread semantics**: some domain gives the run. -/
def ThreadRun (s : Stmt) (rs : Regs) (tr : List Lab) (rs' : Regs) : Prop :=
  ∃ dom, (tr, rs') ∈ run dom s rs

/-! ## Lowering to memory actions -/

/-- The little-endian bytes of `v` at size `sz`. -/
def natBytes (v sz : Nat) : List Byte := (List.range sz).map fun j => BitVec.ofNat 8 (v / 256 ^ j)

/-- The litmus flavour of an annotation. -/
def flavOf : Ann → Silmaril.X86.Litmus.Flavor
  | .wb => .plain
  | .nt => .nonTemporal
  | .str => .string

/-- A plain load action. -/
def ldAct (fl : Flav) (a sz v : Nat) : XAct := ⟨⟨.load, a, sz, false⟩, flavOf fl, natBytes v sz, []⟩

/-- A plain store action. -/
def stAct (fl : Flav) (a sz v : Nat) : XAct := ⟨⟨.store, a, sz, false⟩, flavOf fl, [], natBytes v sz⟩

/-- A locked read-modify-write action. -/
def rmwAct (a sz old new : Nat) : XAct := ⟨⟨.rmw, a, sz, true⟩, .plain, natBytes old sz, natBytes new sz⟩

/-- A fence action. -/
def fenceAct (k : FenceKind) : XAct := ⟨⟨.fence k, 0, 0, false⟩, .plain, [], []⟩

/-- The ghost start byte of thread `t` (above every litmus location). -/
def ctlAddr (t : Nat) : Nat := 0x7f0000 + 64 * t

/-- The ghost waiter-queue byte of the futex word at `a` (above every control byte of the first
`2 ^ 16` threads;. -/
def qAddr (a : Nat) : Nat := 0x1000000 + a

/-- The ghost end byte of thread `t` (in the same 64-byte slot as its start byte). -/
def endAddr (t : Nat) : Nat := ctlAddr t + 32

/-- A start-byte event of thread `t`: a locked RMW of its start byte from `o` to `n`. -/
def ctlAct (t o n : Nat) : XAct := rmwAct (ctlAddr t) 1 o n

/-- An end event of thread `t`: a locked RMW of its end byte from `o` to `n`. -/
def endAct (t o n : Nat) : XAct := rmwAct (endAddr t) 1 o n

/-- **The memory actions of a label.** -/
def Lab.acts : Lab → List XAct
  | .rd _ fl a sz v => [ldAct fl a sz v]
  | .wr _ fl a sz v => [stAct fl a sz v]
  | .rmw _ a sz o n => [rmwAct a sz o n]
  | .fence k => [fenceAct k]
  | .fwait a e seen r =>
    if seen = e then
      [fenceAct .mfence, stAct .wb (qAddr a) 1 1, fenceAct .mfence, ldAct .wb a 4 seen,
        rmwAct (qAddr a) 1 r 0]
    else [fenceAct .mfence, ldAct .wb a 4 seen, fenceAct .mfence]
  | .fwake a _ q => [fenceAct .mfence, rmwAct (qAddr a) 1 q 0, fenceAct .mfence]
  | .fblock a e => [fenceAct .mfence, stAct .wb (qAddr a) 1 1, fenceAct .mfence, ldAct .wb a 4 e]
  | .spawn t => [ctlAct t 0 1]
  | .join t => [endAct t 1 2]
  | .blk _ ins outs _ =>
    ins.map (fun c => ldAct .wb c.1 c.2.1 c.2.2) ++ outs.map fun c => stAct .wb c.1 c.2.1 c.2.2

/-! ## Programs and the concurrent machine -/

/-- A thread: its body, and whether another thread starts it with `spawn`. -/
structure Thread where
  body : Stmt
  spawned : Bool := false

/-- A program: its shared locations (each with an initial value) and its threads. -/
structure Prog where
  locs : List Loc
  threads : List Thread

/-- The memory actions of thread `i`'s trace (with start and end events if it is spawned). -/
def Thread.acts (th : Thread) (i : Nat) (tr : List Lab) : List XAct :=
  (if th.spawned then [ctlAct i 1 2] else []) ++ tr.flatMap Lab.acts ++
    (if th.spawned then [endAct i 0 1] else [])

/-- The x86 core a CIR register file stands for (for the final state). -/
def coreOf (rs : Regs) : Silmaril.X86.State :=
  { regs := rs, rip := 0, flags := ⟨none, none, none, none, none, none⟩ }

/-- A CIR run of thread `i` as a litmus trace: one step with all its actions. -/
def Thread.xtrace (th : Thread) (i : Nat) (p : List Lab × Regs) : XTrace :=
  ⟨[⟨th.acts i p.1, coreOf p.2⟩], coreOf p.2⟩

/-- The candidate traces of every thread over `dom`. -/
def Prog.traces (P : Prog) (dom : List Nat) : List (List XTrace) :=
  P.threads.mapIdx fun i th => (run dom th.body Regs.zero).map (th.xtrace i)

/-- The memory of a program as a litmus test (only `locs` matters to `AxReach`). -/
def Prog.memTest (P : Prog) : Test where
  name := ""
  source := ""
  doc := ""
  locs := P.locs
  threads := []
  quant := .exists_
  cond := .tt
  coverage := .tso
  tso := none
  xl := .allowed
  sc := none
  basis := ""

/-- **Behaviours over a domain**: final states of a choice of one run per thread (reads in
`dom`) and a well-formed candidate execution over their events consistent under `M`. -/
def BehavIn (P : Prog) (dom : List Nat) (M : Exec → Prop) (f : Final) : Prop :=
  AxReach P.memTest (P.traces dom) M f

/-- **Behaviours** of a program under the axiomatic model `M`. -/
def Behav (P : Prog) (M : Exec → Prop) (f : Final) : Prop := ∃ dom, BehavIn P dom M f

/-- Every behaviour under `M` satisfies `Q`. -/
def Safe (P : Prog) (M : Exec → Prop) (Q : Final → Prop) : Prop := ∀ f, Behav P M f → Q f

/-! ## The model order -/

/-- `M ⊑ M'`: every execution consistent under `M` is consistent under `M'` (`M` is stronger). -/
def MLe (M M' : Exec → Prop) : Prop := ∀ x, M x → M' x

@[inherit_doc] scoped infix:50 " ⊑ " => MLe

/-! ## Sequential semantics -/

/-- A flat memory (unmapped bytes read as `0`, as in `AxReach`). -/
abbrev Mem := Nat → Option Byte

/-- The value of `sz` bytes at `a`. -/
def Mem.val (m : Mem) (a sz : Nat) : Option Nat := leValue (fun y => some ((m y).getD 0)) a sz

/-- Write the `sz` bytes of `v` at `a`. -/
def Mem.put (m : Mem) (a sz v : Nat) : Mem :=
  fun y => if a ≤ y ∧ y < a + sz then some (BitVec.ofNat 8 (v / 256 ^ (y - a))) else m y

/-- Replay one label on a flat memory: reads must return the current value. -/
def Lab.replay (m : Mem) : Lab → Option Mem
  | .rd _ _ a sz v => if m.val a sz = some v then some m else none
  | .wr _ _ a sz v => some (m.put a sz v)
  | .rmw _ a sz o n => if m.val a sz = some o then some (m.put a sz n) else none
  | .fwait a e seen r =>
    if seen = e then
      let m1 := m.put (qAddr a) 1 1
      if m1.val a 4 = some seen ∧ m1.val (qAddr a) 1 = some r then some (m1.put (qAddr a) 1 0)
      else none
    else if m.val a 4 = some seen then some m else none
  | .fwake a _ q => if m.val (qAddr a) 1 = some q then some (m.put (qAddr a) 1 0) else none
  | .fblock a e =>
    let m1 := m.put (qAddr a) 1 1
    if m1.val a 4 = some e then some m1 else none
  | .blk _ ins outs _ =>
    if ins.all fun c => m.val c.1 c.2.1 == some c.2.2 then
      some (outs.foldl (fun m c => m.put c.1 c.2.1 c.2.2) m)
    else none
  | _ => some m

/-- Replay a trace. -/
def replay (m : Mem) : List Lab → Option Mem
  | [] => some m
  | l :: ls => (l.replay m).bind fun m' => replay m' ls

/-- **The sequential semantics**: a thread run that replays on one flat memory. -/
def SeqRun (s : Stmt) (rs : Regs) (m : Mem) (tr : List Lab) (rs' : Regs) (m' : Mem) : Prop :=
  ThreadRun s rs tr rs' ∧ replay m tr = some m'

/-- No `spawn` or `join`. -/
def Stmt.threadFree : Stmt → Bool
  | .spawn _ | .join _ => false
  | .seq s t | .ite _ s t => s.threadFree && t.threadFree
  | .loop _ _ b => b.threadFree
  | _ => true

/-- Every access has a positive size (a size-`0` access has no memory unit that `Exec.Wf`
accepts, so it has no axiomatic behaviour, yet it replays sequentially). -/
def Stmt.posSizes : Stmt → Bool
  | .load _ _ sz _ _ | .store _ sz _ _ _ | .rmw _ _ sz _ _ _ => decide (0 < sz)
  | .local b => (b.ins ++ b.outs).all fun c => decide (0 < c.2)
  | .seq s t | .ite _ s t => s.posSizes && t.posSizes
  | .loop _ _ b => b.posSizes
  | _ => true

/-! ## Frozen statements -/

/-- **Single-thread lift** (PROVED: `Silmaril.X86.Concurrency.Cir.Seq.cirSeqSc`, in
`Cir/Seq/Thms.lean`): the SC behaviours of a one-thread, spawn-free program are
its sequential runs from the initial memory. Proof idea: from an SC execution, `po` is total and
`acyclic (po ∪ com;sm)` forces every read byte to come from the `po`-latest write of that byte
(or the initial value) and `co` to follow `po`, which is `replay`; conversely build `rf`/`co`
from the replay and show `scRel` is contained in `po`. Without `posSizes` the statement is
false: a size-`0` store at address `0` replays but has no well-formed candidate
(`Cir.not_cirSeqSc_without_posSizes`). -/
def Task.cirSeqSc : Prop :=
  ∀ (locs : List Loc) (s : Stmt), s.threadFree = true → s.posSizes = true → ∀ f : Final,
    Behav ⟨locs, [⟨s, false⟩]⟩ Exec.Sc f ↔
      ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧
        f = ⟨fun i r => if i = 0 then rs r else 0, m⟩

/-! ## Value domains -/

/-- The values the runs of every thread over `dom` write. -/
def Prog.written (P : Prog) (dom : List Nat) : List Nat :=
  P.threads.flatMap fun th => (run dom th.body Regs.zero).flatMap fun p => p.1.flatMap Lab.written

/-- The domain is closed: every value a run over `dom` writes is in `dom`, and so is every
initial value. -/
def Prog.closedB (P : Prog) (dom : List Nat) : Bool :=
  (P.written dom).all (Silmaril.X86.MemoryModel.Litmus.memB · dom) &&
    P.locs.all fun l => Silmaril.X86.MemoryModel.Litmus.memB l.init dom

/-- Every access is write-back, at a literal address, and exactly one of the cells `cs`. -/
def Stmt.onCells (cs : List (Nat × Nat)) : Stmt → Bool
  | .load _ _ sz fl (.lit a) => fl == .wb && cs.contains (a, sz)
  | .store _ sz fl (.lit a) _ => fl == .wb && cs.contains (a, sz)
  | .rmw _ _ sz _ (.lit a) _ => cs.contains (a, sz)
  | .futexWait _ (.lit a) _ => cs.contains (a, 4)
  | .load .. | .store .. | .rmw .. | .futexWait .. => false
  | .local b => (b.ins ++ b.outs).all cs.contains
  | .seq s t | .ite _ s t => s.onCells cs && t.onCells cs
  | .loop _ _ b => b.onCells cs
  | _ => true

/-- The locations are aligned cells of 1, 2, 4 or 8 bytes, pairwise disjoint, below the
control bytes, with initial values that fit. -/
def locsOk (locs : List Loc) : Bool :=
  locs.all (fun l => [1, 2, 4, 8].contains l.size && l.addr % l.size == 0 &&
    decide (l.init < 2 ^ (8 * l.size)) && decide (l.addr + l.size ≤ ctlAddr 0)) &&
  (List.range locs.length).all fun i => (List.range locs.length).all fun j =>
    i == j || (match locs[i]?, locs[j]? with
      | some l, some l' => decide (l.addr + l.size ≤ l'.addr) || decide (l'.addr + l'.size ≤ l.addr)
      | _, _ => true)

/-- **Uniform programs**: aligned disjoint locations, and every access of every thread is
write-back and exactly one location (so no access tears and every value read is a value
written to that location, or its initial value). -/
def Prog.uniformB (P : Prog) : Bool :=
  locsOk P.locs && P.threads.all fun th => th.body.onCells (P.locs.map fun l => (l.addr, l.size))

/-- The local blocks of a statement. -/
def Stmt.blocks : Stmt → List Block
  | .local b => [b]
  | .seq s t | .ite _ s t => s.blocks ++ t.blocks
  | .loop _ _ b => b.blocks
  | _ => []

/-- The local blocks are closed over `dom`: whenever a block's input cells hold values of
`dom`, every output its contract allows (registers and cells) is in `dom`. A block chooses its
outputs (they are not reads), so `closedB`, which only sees runs over `dom`, cannot check this:
a block whose contract forces an output outside `dom` has no run over `dom` at all
(`Cir.not_cirDomain_without_blocksClosed`). -/
def Prog.BlocksClosed (P : Prog) (dom : List Nat) : Prop :=
  ∀ th ∈ P.threads, ∀ b ∈ th.body.blocks, ∀ rv iv o, rv.length = b.rin.length →
    (∀ v ∈ iv, v ∈ dom) → b.spec (rv ++ iv) o → ∀ v ∈ o, v ∈ dom

/-- No futex operation. -/
def Stmt.futexFree : Stmt → Bool
  | .futexWait .. | .futexWake .. => false
  | .seq s t | .ite _ s t => s.futexFree && t.futexFree
  | .loop _ _ b => b.futexFree
  | _ => true

/-- The partial runs of `while c do body` (at most `n` iterations), given the runs `body` and
the partial runs `pbody` of the body. -/
def preIter (body : Regs → Res) (pbody : Regs → List (List Lab)) (c : Expr) :
    Nat → Regs → List (List Lab)
  | 0, _ => [[]]
  | n + 1, rs =>
    if truthy (c.eval rs) then
      pbody rs ++ (body rs).flatMap fun p => (preIter body pbody c n p.2).map (p.1 ++ ·)
    else [[]]

/-- **Partial runs** over `dom`: the traces of the runs over `dom` stopped after any label
(including the complete runs and the empty trace). A partial run need not extend to a complete
run over `dom`: a later bounded loop or local block may have no run (it acts as an `assume`). -/
def preRuns (dom : List Nat) : Stmt → Regs → List (List Lab)
  | .seq s t, rs =>
    preRuns dom s rs ++ (run dom s rs).flatMap fun p => (preRuns dom t p.2).map (p.1 ++ ·)
  | .ite c s t, rs => if truthy (c.eval rs) then preRuns dom s rs else preRuns dom t rs
  | .loop n c body, rs => preIter (run dom body) (preRuns dom body) c n rs
  | s, rs => [] :: (run dom s rs).map Prod.fst

/-- The values the partial runs of every thread over `dom` write. -/
def Prog.preWritten (P : Prog) (dom : List Nat) : List Nat :=
  P.threads.flatMap fun th =>
    (preRuns dom th.body Regs.zero).flatMap fun tr => tr.flatMap Lab.written

/-- **The domain is closed under partial runs**: every value a partial run over `dom` writes
is in `dom`, so is every initial value, and if the program uses futexes then `0` and `1` (the
values of the ghost waiter queues) are in `dom`. `closedB` (complete runs only) is not enough
(`Cir.not_cirDomain_closedB`). -/
def Prog.preClosedB (P : Prog) (dom : List Nat) : Bool :=
  (P.preWritten dom).all (Silmaril.X86.MemoryModel.Litmus.memB · dom) &&
    P.locs.all (fun l => Silmaril.X86.MemoryModel.Litmus.memB l.init dom) &&
    (P.threads.all (·.body.futexFree) ||
      (Silmaril.X86.MemoryModel.Litmus.memB 0 dom && Silmaril.X86.MemoryModel.Litmus.memB 1 dom))

/-- **Domain closure** (proved as `Cir.cirDomain` in `Cir/Domain/Thms.lean`):
for a uniform program and a domain closed under partial runs (`preClosedB`), with closed local
blocks, every behaviour under SC, TSO or XL is a behaviour over that domain, by the same
choice of runs and the same candidate execution. Proof: in a well-formed candidate of a uniform
program every read takes all its bytes from one write of its location or from the initial value
(two sources would give a `com` two-cycle, which XL's coherence forbids); then by induction
along the acyclic `po ∪ rf` (`Exec.thinAir`, part of XL) every value read from a location is in
`dom`: the source write's label ends a partial run over `dom`. By `BlocksClosed` so is every
block output, and the futex queue values are `0`/`1`, so each thread's run is a run over `dom`.

A statement with `closedB` (values written by complete runs over `dom`) in place of
`preClosedB` is **false**: `store x 7; load r x; loop 0 (r ≠ 7) skip` has no complete run
over `[0]`, so `[0]` is `closedB`, yet it has an SC behaviour reading `7`. Without
`BlocksClosed` it is false too (`Cir.not_cirDomain_without_blocksClosed`). -/
def Task.cirDomain : Prop :=
  ∀ (P : Prog) (dom : List Nat), P.uniformB = true → P.preClosedB dom = true →
    P.BlocksClosed dom → ∀ (M : Silmaril.X86.MemoryModel.Litmus.Model) (f : Final),
      Behav P M.Holds f → BehavIn P dom M.Holds f

end Silmaril.X86.Concurrency.Cir
