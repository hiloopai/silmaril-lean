module

public import Silmaril.Project.Defs
public import Silmaril.Process.Mt.Csl.Defs

/-!
# Standard problem shapes: multi-threaded programs, decomposed

A multi-threaded verification problem is stated on the thread-modular system of
`Silmaril.Process.Mt.Csl` (a thread machine `U` over a store `S`, a resource invariant `I`,
postconditions `Q`) and **decomposed** into one single-threaded problem per thread plus
compatibility conditions; trusted primitives are atomic steps with abstract specs, and their
implementations are proved against those specs per memory model, separately.

| name | statement |
|---|---|
| `silmaril.shapes.mt.thread` | `Thread U I Q t s h`: thread `t` in state `s`, owning `h`, is safe under `I` and ends in `Q` (the single-threaded problem, `Csl.Safe`) |
| `silmaril.shapes.mt.decomposed` | `Decomposed U I Q C₀`: for some owned heaps and invariant heap, the start `C₀` meets the compatibility conditions and every thread its single-threaded problem (`Csl.GInv`) |
| `silmaril.shapes.mt.safe` | `MtSafe U I Q C₀`: every configuration reachable from `C₀` (SC interleaving, atomic primitives) is `Good`: no fault, no data race, the invariant, the postconditions of finished threads |
| `silmaril.shapes.mt.sound` | `ModelSound X I Q`: the concrete model `X` (store buffers, primitive code) refines SC with atomic steps on programs certified for `I`, `Q` (`Csl.Model.Sound`; for a memory model, a DRF theorem) |
| `silmaril.shapes.mt.primitive` | `Primitive sp X`: the model `X` of the most general client of `sp`, which runs the primitive's implementation under a memory model, refines its atomic spec for every client invariant |

`Mt/Thms`: `decomposed` gives `safe` (`Csl.adequacy`), and through a sound model the concrete
system is fault-free with `Good` abstractions (`Csl.adequacy_model`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Mt

open Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V}

/-- **The single-threaded problem of one thread.** -/
@[problem "silmaril.shapes.mt.thread"
  (title := "One thread is safe on what it owns under a resource invariant")]
def Thread (U : TIsa S) (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (t : Nat) (s : U.St)
    (h : Heap A V) : Prop :=
  Safe U I Q t s h

/-- **A multi-threaded problem, decomposed**: per-thread problems plus compatibility. -/
@[problem "silmaril.shapes.mt.decomposed"
  (title := "A multi-threaded start decomposes into safe threads with disjoint ownership and an invariant")]
def Decomposed (U : TIsa S) (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (C₀ : Cfg U) :
    Prop :=
  ∃ hs hI, GInv U I Q C₀ hs hI

/-- **The multi-threaded property.** -/
@[problem "silmaril.shapes.mt.safe"
  (title := "Every reachable configuration of a multi-threaded system is fault-free, race-free, in the invariant")]
def MtSafe (U : TIsa S) (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) (C₀ : Cfg U) :
    Prop :=
  ∀ C, Reach U C₀ C → Good U I Q C

/-- **A concrete model refines SC with atomic steps** on certified programs. -/
@[problem "silmaril.shapes.mt.sound"
  (title := "A concrete multi-threaded model refines SC with atomic steps on certified programs")]
def ModelSound {U : TIsa S} (X : Model U) (I : HProp A V) (Q : Nat → U.St → Heap A V → Prop) :
    Prop :=
  X.Sound I Q

/-- **A primitive's implementation meets its spec under a memory model**: `X` is a concrete
model of the most general client of `sp` (running the implementation under the memory model),
sound for every client invariant. -/
@[problem "silmaril.shapes.mt.primitive"
  (title := "A primitive implementation meets its logically atomic spec under a memory model")]
def Primitive (sp : PrimSpec M) (X : Model (TIsa.mgc (S := S) sp)) : Prop :=
  ∀ I Q, X.Sound I Q

end Silmaril.Project.Shapes.Mt
