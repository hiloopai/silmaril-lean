module

public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# Setting up a network with the built-ins

`Net.initStore net` is given directly: the store after creating the `m` streams and the `k`
waitable sets and joining every end to its node's set. Here the setup is a **program of
built-ins** run from the empty store (`Silmaril.Wasm.Component.Streams.Setup.Thms` proves it yields
`initStore net`, and the handles it returns are those the nodes use):

* `stream.new`, `m` times (stream `c` gets the ends `rh c = 2c+1` and `wh c = 2c+2`);
* `waitable-set.new`, `k` times (node `i` gets the set `net.ws i = 2m+1+i`);
* for each stream `c`, `waitable.join (rh c) (ws (rd c))` and `waitable.join (wh c) (ws (wr c))`.

`runOps st ops` runs built-ins in order (`none` if one traps) and collects their results.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Setup

open Silmaril.Wasm.Component.Async (Res)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

/-- Run built-ins in order, collecting their results (`none`: one of them trapped). -/
def runOps : DStore → List DOp → Option (DStore × List Res)
  | st, [] => some (st, [])
  | st, op :: ops => (dstep st op).bind fun p =>
      (runOps p.1 ops).map fun q => (q.1, p.2 :: q.2)

/-- The joins of the ends of streams `0 … n-1`. -/
def joinOps (net : Network) (n : Nat) : List DOp :=
  (List.range n).flatMap fun c => [.join (rh c) (net.ws (net.rd c)), .join (wh c) (net.ws (net.wr c).1)]

/-- **The setup program** of a network. -/
def setupOps (net : Network) : List DOp :=
  List.replicate net.m .streamNew ++ List.replicate net.k .wsNew ++ joinOps net net.m

/-- The results the setup program returns: the ends of every stream, every set, then `unit` for
every join. -/
def setupRes (net : Network) : List Res :=
  (List.range net.m).map (fun c => .ends (rh c) (wh c)) ++
    (List.range net.k).map (fun i => .nat (net.ws i)) ++ List.replicate (2 * net.m) .unit

end Silmaril.Wasm.Component.Streams.Setup
