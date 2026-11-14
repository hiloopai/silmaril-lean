module

public import Silmaril.Process.Mt.Csl.Example.Defs
public import Silmaril.Process.Mt.Csl.Thms
import Silmaril.Proofs.Process.Mt.Csl.Example

/-!
# The mutex-protected counter: what is proved

PROVED (proofs in `Silmaril/Proofs/Process/Mt/Csl/Example.lean`):

* `safe_start`: a thread at pc 0 owning nothing is safe (its single-threaded problem);
* `ginv_start`: the start of `n` threads satisfies the compatibility conditions;
* `good`: every reachable configuration is `Good` (`Csl.adequacy`);
* `excl`: **mutual exclusion**: no two threads are at pc 1 at once, from `Csl.no_race`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl.Example

/-- The single-threaded problem of each thread holds. -/
theorem safe_start (t : Nat) : Safe thr inv post t (0 : Nat) Heap.empty :=
  Silmaril.Proofs.Process.Mt.Csl.Example.safe_start t

/-- The start satisfies the compatibility conditions. -/
theorem ginv_start (n v : Nat) :
    GInv thr inv post (start n v) (fun _ => Heap.empty) (unlocked v) :=
  Silmaril.Proofs.Process.Mt.Csl.Example.ginv_start n v

/-- Every reachable configuration is `Good`. -/
theorem good {n v : Nat} {C : Cfg thr} (r : Reach thr (start n v) C) : Good thr inv post C :=
  adequacy (ginv_start n v) r

/-- **Mutual exclusion.** -/
theorem excl {n v : Nat} {C : Cfg thr} (r : Reach thr (start n v) C) {t u : Nat} (htu : t ≠ u)
    (ht : C.th t = some (1 : Nat)) (hu : C.th u = some (1 : Nat)) : False :=
  (good r).2.1 ⟨t, u, _, _, ctr, htu, ht, hu, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Silmaril.Process.Mt.Csl.Example
