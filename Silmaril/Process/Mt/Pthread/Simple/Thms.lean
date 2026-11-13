module

public import Silmaril.Process.Mt.Pthread.Simple.Defs
import Silmaril.Proofs.Process.Mt.Pthread.Simple

/-!
# The simple pthread model: results

* **`Impl.refines`** (proved): given the glibc obligations in linearization form (`Impl.Lin`:
  every call of an implemented pthread function takes exactly one specification step, at its
  linearization point, and touches no client cell), the full model of a program (its
  instructions, with the primitives run by their implementations, sequentially consistent)
  refines the simple model: every run stands for a run of `tisa P`.
* `noUB_full`, `deterministic_full` (proved): so absence of undefined behaviour and a
  deterministic output, proved on the simple model, hold of the full model.

Under x86-TSO and XL the full model also has store buffers; for programs that are race free in
the simple model (`RaceFree`), the memory-model bridge of `Silmaril.Process.Mt.Drf` (`drf_sc`)
reduces it to the sequentially consistent full model, given the implementations' correctness
per memory model (`Drf.Prim.PrimsCorrect`, `Pthread/Glibc`). That composition is not done here.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread.Simple

open Silmaril.Process.Mt.Csl

variable {ι : Type} {P : Prog} {I : Impl ι}

/-- **The full model refines the simple model**, given the linearization obligations. -/
theorem Impl.refines (hl : I.Lin) : Refines (Impl.model P I) :=
  Silmaril.Proofs.Process.Mt.Pthread.Simple.refines hl

/-- Every run of the full model stands for a run of the simple model. -/
theorem Impl.reach (hl : I.Lin) {c₀ c : CCfg I.St ι} (r : Star (Impl.model P I).step c₀ c) :
    Reach (tisa P) (absC P I c₀) (absC P I c) :=
  Silmaril.Proofs.Process.Mt.Pthread.Simple.reach_abs hl r

/-- **No undefined behaviour transfers** to the full model. -/
theorem noUB_full (hl : I.Lin) (h : NoUB P) {c₀ c : CCfg I.St ι} (h₀ : absC P I c₀ = start P)
    (r : Star (Impl.model P I).step c₀ c) : ¬ (Impl.model P I).fault c := by
  have := Impl.reach hl r
  rw [h₀] at this
  exact h _ this

/-- **A deterministic output transfers** to the full model: once `main` has finished, the
full model has printed `o`. -/
theorem deterministic_full (hl : I.Lin) {o : List Nat} (h : Deterministic P o) {c₀ c : CCfg I.St ι}
    (h₀ : absC P I c₀ = start P) (r : Star (Impl.model P I).step c₀ c) (hd : MainDone (absC P I c)) :
    c.out = o := by
  have := Impl.reach hl r
  rw [h₀] at this
  exact h.2 _ this hd

end Silmaril.Process.Mt.Pthread.Simple
