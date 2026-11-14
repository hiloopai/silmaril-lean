module

public import Silmaril.Process.Mt.Csl.Defs

/-!
# Read-only sharing for the thread-modular decomposition

`Csl.Safe` lets a plain step of a thread run only on addresses that thread owns (its footprint
`fp` must be owned), and `Csl.Race` counts two plain accesses of one address by two threads as a
race even when both only read it. As stated, two threads can therefore never run the same library
code (instruction fetches are reads of the code bytes) or read the same constant.

`roT U RO` fixes a heap `RO` of **read-only** cells, shared by every thread and owned by none:

* the steps of `roT U RO` start and end in memories agreeing with `RO`;
* footprints leave out `RO`'s addresses, so reading `RO` needs no ownership and is not a race;
* a step of `U` that would change `RO` (a plain or atomic step, or a `clone`) is a fault of
  `roT U RO`.

A thread is then proved safe for `roT U RO` (its per-thread problem may read `RO` freely, and
must not write it). `Csl.Ro.Thms` (`ro_adequacy`) shows the decomposition stays sound: from a
start agreeing with `RO` and decomposed for `roT U RO`, every run of `U` is a run of `roT U RO`,
never faults, keeps `RO`, and ends `Good` for `roT U RO` (no race outside `RO`).

Promoted from erebor-lean's `Erebor.Mt.roT` (multithreaded problems).
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V}

/-- **The thread machine `U` with the read-only heap `RO` fixed** (module doc). -/
def roT (U : TIsa S) (RO : Heap A V) : TIsa S where
  St := U.St
  step t s m s' m' := S.Agrees RO m ∧ U.step t s m s' m' ∧ S.Agrees RO m'
  fault t s m := S.Agrees RO m ∧ (U.fault t s m ∨ (∃ s' m', U.step t s m s' m' ∧ ¬ S.Agrees RO m') ∨
    ∃ u s₁ s₂ m', U.spawn t u s m s₁ s₂ m' ∧ ¬ S.Agrees RO m')
  fp t s m a := S.Agrees RO m ∧ U.fp t s m a ∧ RO a = none
  atom t s m s' m' := S.Agrees RO m ∧ U.atom t s m s' m' ∧ S.Agrees RO m'
  afault t s m := S.Agrees RO m ∧ (U.afault t s m ∨ ∃ s' m', U.atom t s m s' m' ∧ ¬ S.Agrees RO m')
  spawn t u s m s₁ s₂ m' := S.Agrees RO m ∧ U.spawn t u s m s₁ s₂ m' ∧ S.Agrees RO m'
  done := U.done

/-- A configuration of `U` as one of `roT U RO` (the same threads and memory). -/
def cfgRo {U : TIsa S} (RO : Heap A V) (C : Cfg U) : Cfg (roT U RO) := ⟨C.th, C.mem⟩

end Silmaril.Process.Mt.Csl
