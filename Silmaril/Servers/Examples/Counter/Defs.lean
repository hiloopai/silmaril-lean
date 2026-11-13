module

public import Silmaril.Servers.Core.Defs

/-!
# A counter server: overlapping requests and linearizability

The simplest stateful server: each request is answered with the number of requests handled
before it (`counter`, a machine of `counterSig` whose state is the count). Two traces:

* `overlap`: the requests `a` and `b` arrive on two connections before either is answered, and
  `b` is answered `0`, then `a` is answered `1`. Linearizable: `b`'s handler ran first;
* `early`: `a` arrives and is answered `1` before any other request. Not linearizable: the
  first handler run answers `0`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Examples.Counter

/-- The counter interface: a request carries nothing, a response is a number. -/
def counterSig : Sig := ⟨Unit, Nat⟩

/-- **The counter**: answer the count, then increment it. -/
def counter : Machine counterSig Nat := fun q _ (n : Nat) q' => n = q ∧ q' = q + 1

/-- The first request on connection `0`. -/
def a : ReqId := ⟨0, 0⟩

/-- The first request on connection `1`. -/
def b : ReqId := ⟨1, 0⟩

/-- Two overlapping requests, answered `0` (the second to arrive) and `1`. -/
def overlap : Trace counterSig :=
  [.recv a (), .recv b (), .send b (0 : Nat), .send a (1 : Nat)]

/-- One request answered `1`. -/
def early : Trace counterSig := Trace.seq [(a, (), (1 : Nat))]

end Silmaril.Servers.Examples.Counter
