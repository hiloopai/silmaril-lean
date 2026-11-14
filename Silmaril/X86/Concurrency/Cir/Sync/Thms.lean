module

public import Silmaril.X86.Concurrency.Cir.Sync.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Sync

/-!
# CIR spawn and join: what is proved

All statements are PROVED with the standard axioms. The proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/Sync.lean`.

## Axiomatic

* `Exec.swHb_sc`, `Exec.swHb_ghb`, `Exec.swHb_ghbXl`: every spawn/join happens-before edge
  (`po? ; sw ; po?` between memory units) is a path of the model's own global order:
  * SC: `po`, then `rf` lifted through `sm`, then `po`;
  * TSO: `ppo`, then `rfe` lifted through `sm`, then `ppo`;
  * XL: `lockXl`, then `rfe` lifted through `smT`, then `lockXl`.

  XL needs the locks, because a weak (non-temporal) store before a spawn has no `ppoXl`
  edge. TSO and SC need only that `sw` is `rf` from a write to a read.
* `Exec.scS_iff`, `Exec.tsoS_iff`, `Exec.xlS_iff`: so adding the edges changes no model, and
  the ghost-byte lowering implements spawn/join synchronisation.
* `scS_le_tsoS`, `tsoS_le_xlS`, `scS_le_xlS`: SC ⊑ TSO ⊑ XL with synchronisation edges.
* `behavIn_scS_iff`, `behavIn_tsoS_iff`, `behavIn_xlS_iff`: CIR behaviours under the
  synchronising models are the behaviours under the plain ones. With `behavIn_mono`, this gives
  monotonicity for the synchronising models.

## Operational TSO

* `spawn_step_drained`: a `spawn t` step of thread `i` needs `i`'s store buffer empty. The same
  holds for every control event, since each is an `XEvent.rmw`.
* `start_step_needs_spawn`: the child's start step needs its start byte to hold `1` in memory.
* `join_step_needs_end`: a `join t` step needs `t`'s end byte to hold `1` in memory.
* `end_finished`, `join_after_child`: from the initial configuration, in every reachable
  configuration where end byte `t` holds `1`, thread `t` has no events left and an empty
  buffer. This needs `CtlOk` (only the thread operations touch the byte, and only `t`'s last
  event writes `1`), `OpAx.ThreadsOk`, and an initial value other than `1`. So a join waits
  until the child has finished and drained.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Axiomatic (Exec BRel)
open Silmaril.X86.MemoryModel.Litmus (Final ACfg AStep axReach_mono)
open Silmaril.X86.MemoryModel.Tso (XStep XState Byte)
open Relation

/-- **SC**: a spawn/join edge is a path of `po | com;sm`. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.swHb_sc {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.scRel.Holds a b := Silmaril.Proofs.X86.Concurrency.Cir.Sync.swHb_sc h

/-- **TSO**: a spawn/join edge is a `ghb` path. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.swHb_ghb {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.ghb.Holds a b := Silmaril.Proofs.X86.Concurrency.Cir.Sync.swHb_ghb h

/-- **XL**: a spawn/join edge is a `ghbXl` path. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.swHb_ghbXl {x : Exec} {a b : Fin x.n} (h : x.swHb a b = true) :
    TransGen x.ghbXl.Holds a b := Silmaril.Proofs.X86.Concurrency.Cir.Sync.swHb_ghbXl h

/-- Adding the synchronisation edges to SC changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.scS_iff (x : Exec) : x.ScS ↔ x.Sc := Silmaril.Proofs.X86.Concurrency.Cir.Sync.scS_iff x

/-- Adding the synchronisation edges to TSO changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.tsoS_iff (x : Exec) : x.TsoS ↔ x.Tso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Sync.tsoS_iff x

/-- Adding the synchronisation edges to XL changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.xlS_iff (x : Exec) : x.XlS ↔ x.Xl := Silmaril.Proofs.X86.Concurrency.Cir.Sync.xlS_iff x

/-- SC ⊑ TSO, with synchronisation edges. -/
theorem scS_le_tsoS : Exec.ScS ⊑ Exec.TsoS := fun x h =>
  (x.tsoS_iff).mpr (sc_le_tso x ((x.scS_iff).mp h))

/-- TSO ⊑ XL, with synchronisation edges. -/
theorem tsoS_le_xlS : Exec.TsoS ⊑ Exec.XlS := fun x h =>
  (x.xlS_iff).mpr (tso_le_xl x ((x.tsoS_iff).mp h))

/-- SC ⊑ XL, with synchronisation edges. -/
theorem scS_le_xlS : Exec.ScS ⊑ Exec.XlS := scS_le_tsoS.trans tsoS_le_xlS

theorem behavIn_congr {P : Prog} {dom : List Nat} {M M' : Exec → Prop} (h : ∀ x, M x ↔ M' x)
    {f : Final} : BehavIn P dom M f ↔ BehavIn P dom M' f :=
  ⟨axReach_mono fun x => (h x).mp, axReach_mono fun x => (h x).mpr⟩

/-- CIR behaviours under SC with synchronisation edges are the SC behaviours. -/
theorem behavIn_scS_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.ScS f ↔ BehavIn P dom Exec.Sc f := behavIn_congr Exec.scS_iff

/-- CIR behaviours under TSO with synchronisation edges are the TSO behaviours. -/
theorem behavIn_tsoS_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.TsoS f ↔ BehavIn P dom Exec.Tso f := behavIn_congr Exec.tsoS_iff

/-- CIR behaviours under XL with synchronisation edges are the XL behaviours. -/
theorem behavIn_xlS_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.XlS f ↔ BehavIn P dom Exec.Xl f := behavIn_congr Exec.xlS_iff

/-! ## Operational TSO -/

/-- **Spawn drains the parent's buffer**: a `spawn t` step of thread `i` (the locked `0 → 1` of
`t`'s start byte) needs `i`'s buffer empty. -/
theorem spawn_step_drained {s s' : XState Nat} {i t : Nat}
    (h : XStep s (.rmw i (ctlAddr t) [0] [1]) s') : s.buffer i = [] :=
  Silmaril.Proofs.X86.Concurrency.Cir.Sync.Op.rmw_drained h

/-- **The child starts after the spawn**: its start step (the locked `1 → 2` of its start byte)
needs the start byte to hold `1` in memory, which only a spawn writes. -/
theorem start_step_needs_spawn {s s' : XState Nat} {t : Nat}
    (h : XStep s (.rmw t (ctlAddr t) [1] [2]) s') : s.memory (ctlAddr t) = some 1 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Sync.Op.rmw_reads h

/-- **Join needs the child's end**: a `join t` step (the locked `1 → 2` of `t`'s end byte) needs
the end byte to hold `1` in memory, and the joining thread's buffer empty. -/
theorem join_step_needs_end {s s' : XState Nat} {i t : Nat}
    (h : XStep s (.rmw i (endAddr t) [1] [2]) s') :
    s.memory (endAddr t) = some 1 ∧ s.buffer i = [] :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.Sync.Op.rmw_reads h,
    Silmaril.Proofs.X86.Concurrency.Cir.Sync.Op.rmw_drained h⟩

/-- **A `1` in end byte `t` means child `t` has finished and drained**: in every configuration
reachable from the events `es` with empty buffers, when only the thread operations touch the
byte and every event names its own thread. -/
theorem end_finished {es : List (List (Silmaril.X86.MemoryModel.Tso.XEvent Nat))} {t : Nat}
    (hok : CtlOk es t) (htag : Silmaril.X86.MemoryModel.OpAx.ThreadsOk es)
    {m0 : Silmaril.X86.MemoryModel.Tso.Mem} (h0 : m0 (endAddr t) ≠ some 1) {c : ACfg}
    (hr : ReflTransGen AStep ⟨es, ⟨m0, fun _ => []⟩⟩ c)
    (h1 : c.st.memory (endAddr t) = some 1) : c.rest[t]? = some [] ∧ c.st.buffer t = [] :=
  Silmaril.Proofs.X86.Concurrency.Cir.Sync.Op.end_finished hok htag h0 hr h1

/-- **Join waits for the finished, drained child**: a `join t` step from a reachable
configuration happens only when thread `t` has no events left and an empty buffer. -/
theorem join_after_child {es : List (List (Silmaril.X86.MemoryModel.Tso.XEvent Nat))} {t i : Nat}
    (hok : CtlOk es t) (htag : Silmaril.X86.MemoryModel.OpAx.ThreadsOk es)
    {m0 : Silmaril.X86.MemoryModel.Tso.Mem} (h0 : m0 (endAddr t) ≠ some 1) {c : ACfg}
    (hr : ReflTransGen AStep ⟨es, ⟨m0, fun _ => []⟩⟩ c) {s' : XState Nat}
    (hj : XStep c.st (.rmw i (endAddr t) [1] [2]) s') :
    c.rest[t]? = some [] ∧ c.st.buffer t = [] :=
  end_finished hok htag h0 hr (join_step_needs_end hj).1

end Silmaril.X86.Concurrency.Cir
