module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.MemoryModel.OpAx.Defs

/-!
# CIR spawn and join: synchronisation edges and operational TSO

CIR's `spawn t` and
`join t` have a memory-model meaning:

* everything the parent does before `spawn t` happens before everything child `t` does;
* everything child `t` does happens before everything the parent does after `join t`.

## How CIR lowers spawn and join

`Cir.Defs` lowers the thread operations to locked read-modify-writes of two ghost control bytes
of the child, outside every location. On the start byte `ctlAddr t`, `spawn t` is `0 → 1` and
the child's start is `1 → 2`. On the end byte `endAddr t`, the child's end is `0 → 1` and
`join t` is `1 → 2`. A child can only start by reading the `1` that the spawn wrote, and a join
can only complete by reading the `1` that the child's end wrote, so `rf` links spawn to start
and end to join. (An earlier lowering used one byte, `0 → 1 → 2 → 3 → 4`; it was split, see
`Cir.Defs`.)

## Explicit synchronisation edges (`Exec.sw`, `Exec.swHb`)

This module states the meaning directly, as extra edges of the axiomatic models:

* `Exec.sw`: **synchronises-with**. An external `rf` edge between two locked units of control
  bytes: from the spawn's write to the child's start read, and from the child's end write to
  the join's read.
* `Exec.swHb`: the happens-before edges between memory units, `po? ; sw ; po?`. A memory unit
  `po`-before (or equal to) the synchronising write is ordered before every memory unit
  `po`-after (or equal to) the synchronising read.
* `Exec.ScS`, `Exec.TsoS`, `Exec.XlS`: SC, x86-TSO and XL with these edges added to their
  global orders. SC adds them to `po | com;sm`, TSO to `ghb`, and XL to its `ghbXl`.

`Silmaril.X86.Concurrency.Cir.Sync.Thms` proves that adding the edges changes nothing: every
`swHb` edge is already a path of the model's own order (`Exec.scS_iff`, `Exec.tsoS_iff`,
`Exec.xlS_iff`). So the ghost-byte lowering *implements* the synchronisation, and SC ⊑ TSO ⊑ XL
and monotonicity hold for the synchronising models too.

## Operational TSO (`OpBehavIn`)

`Prog.opTest` is the program's memory with one mapped control byte (initially `0`) per spawned
thread. `OpBehavIn P dom f` is the operational store-buffer machine (`Litmus.OpReach`) over
the program's traces. In that machine every control event is an `XEvent.rmw`, and an `rmw`
needs its thread's buffer empty. So:

* `spawn t` drains the parent's buffer before the child can start (`Cir.spawn_step_drained`);
* `join t` is enabled only once the end byte holds `1` (`Cir.join_step_needs_end`). In every
  reachable configuration where it holds `1`, child `t` has finished all its events and its
  buffer is empty (`Cir.end_finished`, under
  `CtlOk`: only the thread operations touch control bytes, and `OpAx.ThreadsOk`: every event
  of thread `i` names thread `i`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Sync

/-- A control byte: at or above the first thread's control byte. -/
def isCtlAddr (a : Nat) : Bool := decide (ctlAddr 0 ≤ a)

end Silmaril.X86.Concurrency.Cir.Sync

namespace Silmaril.X86.MemoryModel.Axiomatic.Exec
variable (x : Exec)

/-- **Synchronises-with**: an external `rf` edge between two locked units of control bytes (the
spawn's write to the child's start read, the child's end write to the join's read). -/
def sw : BRel x.n := fun w r =>
  x.rfe w r && (x.ev w).isA && (x.ev r).isA &&
    Silmaril.X86.Concurrency.Cir.Sync.isCtlAddr (x.ev w).addr &&
    Silmaril.X86.Concurrency.Cir.Sync.isCtlAddr (x.ev r).addr

/-- `a = b` or `a` is `po`-before `b`. -/
def poq : BRel x.n := fun a b => decide (a = b) || x.po a b

/-- **The happens-before edges of spawn and join**: between memory units, `po? ; sw ; po?`. -/
def swHb : BRel x.n := fun a b =>
  (x.ev a).isM && (x.ev b).isM && ((x.poq.seq x.sw).seq x.poq) a b

/-- SC with the synchronisation edges. -/
def ScS : Prop := x.Sc ∧ BRel.Acyclic (x.scRel.union x.swHb)

/-- x86-TSO with the synchronisation edges. -/
def TsoS : Prop := x.Tso ∧ BRel.Acyclic (x.ghb.union x.swHb)

/-- XL with the synchronisation edges. -/
def XlS : Prop := x.Xl ∧ BRel.Acyclic (x.ghbXl.union x.swHb)

end Silmaril.X86.MemoryModel.Axiomatic.Exec

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Axiomatic (Exec BRel Ev)
open Silmaril.X86.MemoryModel.Litmus (Loc Test Final OpReach)

/-! ## Operational TSO -/

/-- The control locations of thread `i`: its start and end bytes, initially `0`. -/
def threadCtlLocs (i : Nat) : List Loc := [⟨s!"start{i}", ctlAddr i, 1, 0⟩, ⟨s!"end{i}", endAddr i, 1, 0⟩]

/-- The control locations of the spawned threads. -/
def Prog.ctlLocs (P : Prog) : List Loc :=
  (P.threads.zipIdx.filter fun p => p.1.spawned).flatMap fun p => threadCtlLocs p.2

/-- The memory of the operational machine: the locations and the control bytes. -/
def Prog.opTest (P : Prog) : Test := { P.memTest with locs := P.locs ++ P.ctlLocs }

/-- **Operational x86-TSO behaviours over a domain**: the store-buffer machine on the program's
traces, with the control bytes mapped. -/
def OpBehavIn (P : Prog) (dom : List Nat) (f : Final) : Prop := OpReach P.opTest (P.traces dom) f

open Silmaril.X86.MemoryModel.Tso (XEvent)

/-- The `XEvent` footprint of an event: its address and size (a fence touches nothing). -/
def evFoot : XEvent Nat → Option (Nat × Nat)
  | .load _ a bs => some (a, bs.length)
  | .store _ a bs => some (a, bs.length)
  | .rmw _ a old _ => some (a, old.length)
  | .fence _ => none

/-- The event touches byte `y`. -/
def evCovers (e : XEvent Nat) (y : Nat) : Prop :=
  ∃ a n, evFoot e = some (a, n) ∧ a ≤ y ∧ y < a + n

/-- **Only thread operations touch end byte `t`.** Among the events `es` of the threads, an
event that touches `endAddr t` is a one-byte `rmw` of exactly that byte, and one that writes
`1` there is the last event of thread `t` (its end). -/
def CtlOk (es : List (List (XEvent Nat))) (t : Nat) : Prop :=
  ∀ i l, es[i]? = some l → ∀ k e, l[k]? = some e → evCovers e (endAddr t) →
    ∃ o n, e = .rmw i (endAddr t) [o] [n] ∧ (n = 1 → i = t ∧ k + 1 = l.length)

end Silmaril.X86.Concurrency.Cir
