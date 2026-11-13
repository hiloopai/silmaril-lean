module

public import Silmaril.Wasm.Component.Streams.Net.Defs

/-!
# Liveness of stream networks: definitions

The networks of `Silmaril.Wasm.Component.Streams.Net` (nodes over the drop-faithful stream
built-ins) **terminate**: every step of every node strictly decreases a potential `pot`, a natural
number computed from the nodes' states alone, so there is no infinite run whatever the scheduler
does. With **progress** (a reachable system in which some node has not finished can step) this
gives liveness under every scheduler, fair or not (`Silmaril.Wasm.Component.Streams.Live.Thms`).

* `NSt.Finished`: the node has dropped its readable end and closed every writable end.
* `Sys.AllDone`: every node has finished.
* `Network.Topo`: the nodes are numbered along the streams (a stream's writer has a smaller index
  than its reader); checked by evaluation with `Network.topoCheck`.
* `pot B Bo s`: the potential, given a bound `B i` on the items node `i` reads and `Bo i` on the
  items each output of node `i` acknowledges. Per input: `3 * (B - |got|)` plus a weight of the
  input's state (`idle` 3, `busy` 2, `ended` 1, `gone` 0); per output: `3 * (Bo - |ack|)` plus a
  weight of its state (`idle` 3, `busy` 2, `dead` 1, `closed` 0).
* `Exec net r`: a maximal execution under an arbitrary scheduler: from the initial system, each
  step is a step of the network, or, when no node can step, the system stays as it is.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Net

/-- The node has dropped its readable end and closed every writable end. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.NSt.Finished {σ : Type} (x : NSt σ) : Prop :=
  (∃ b, x.rd = .gone b) ∧ ∀ o ∈ x.outs, ∃ d, o.st = .closed d

/-- Every node has finished. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.Sys.AllDone {net : Network} (s : Sys net) : Prop :=
  ∀ i, (s.ns i).Finished

/-- The nodes are numbered along the streams. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.Network.Topo (net : Network) : Prop :=
  ∀ c, c < net.m → (net.wr c).1.val < (net.rd c).val

/-- A Boolean check of `Network.Topo`. -/
def _root_.Silmaril.Wasm.Component.Streams.Net.Network.topoCheck (net : Network) : Bool :=
  (List.range net.m).all fun c => decide ((net.wr c).1.val < (net.rd c).val)

/-- The weight of an input state. -/
def rdW : RV → Nat
  | .idle => 3
  | .busy => 2
  | .ended => 1
  | .gone _ => 0

/-- The weight of an output state. -/
def osW : OS → Nat
  | .idle _ => 3
  | .busy _ _ => 2
  | .dead => 1
  | .closed _ => 0

/-- The potential of an output, for the bound `bo` on its acknowledged items. -/
def oPot (bo : Nat) (o : Out) : Nat := 3 * (bo - o.ack.length) + osW o.st

/-- The potential of a list of outputs. -/
def outsPot (bo : Nat) (os : List Out) : Nat := (os.map (oPot bo)).sum

/-- The potential of a node, for the bounds `b` (items read) and `bo` (items acknowledged). -/
def nodePot {σ : Type} (b bo : Nat) (x : NSt σ) : Nat :=
  3 * (b - x.got.length) + rdW x.rd + outsPot bo x.outs

/-- **The potential of a system.** -/
def pot {net : Network} (B Bo : Fin net.k → Nat) (s : Sys net) : Nat :=
  (List.finRange net.k).foldr (fun i a => nodePot (B i) (Bo i) (s.ns i) + a) 0

/-- The bounds hold in `s`. -/
def Bounded {net : Network} (B Bo : Fin net.k → Nat) (s : Sys net) : Prop :=
  ∀ i, (s.ns i).got.length ≤ B i ∧ ∀ o ∈ (s.ns i).outs, o.ack.length ≤ Bo i

/-- Some node can step. -/
def Enabled (net : Network) (s : Sys net) : Prop := ∃ s', Step net s s'

/-- **A maximal execution under an arbitrary scheduler.** -/
def Exec (net : Network) (r : Nat → Sys net) : Prop :=
  r 0 = init net ∧ ∀ n, Step net (r n) (r (n + 1)) ∨ (¬ Enabled net (r n) ∧ r (n + 1) = r n)

end Silmaril.Wasm.Component.Streams.Live
