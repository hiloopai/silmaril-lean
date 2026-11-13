module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Chain

/-!
# Generated stream modules are correct under the Component Model's drop behaviour

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KDrop.{Exec,Pieces,Drops,Reads,Events,Writes,Main,Chain}`.

The modules of `genD k N` (`KDrop.Defs`), run by the callback runtime `DRStep` over the
drop-faithful stream built-ins of `Silmaril.Wasm.Component.Streams.Drop` (an idle end is notified
`DROPPED` when its peer drops, and a later copy on it traps; a copy can end `DROPPED` with a count
and its items), implement the generic node program of `Silmaril.Wasm.Component.Streams.Net`:

* **`step_sim`**: every step of the runtime from a machine related (`RelD`) to a node state is a
  step `NStep` of the node `node k c c'` (input stream `c`, output stream `c'`) to a related
  state, or a step that changes neither the store nor the node. `init_rel`: the machine after the
  lift is related to the node's initial state.
* **`kchain_correct`** / **`kchain_safe`**: in a chain `source → genD k₁ → … → genD kₙ → sink`
  (`kchain`, `KReach`; every read size in `1..256`, every interleaving, every chunking of the
  copies), once the sink has dropped its input it holds `runs ks xs`, the kernels' runs in
  order, and at every point a prefix of it.
* `kchain_wf`: the chain is a well-formed network.

What is modelled, not proved: the fragment's semantics (`KCore.exec`, here `dexec`) stands for
WebAssembly's, as in `KCore`; the runtime delivers only well-formed events (`wfD`), and a
`stream.read` result delivers as many items as its count says; the lift's prologue
(`stream.new`, `waitable-set.new`, `task.return`, the joins) is the network's setup store
(`Net.initStore`), not run. Liveness (no premature trap) is not proved here: the module traps on
events the node program cannot produce at that point; the wasmtime runs of
`tools/wasm-jco/tests/kdrop.sh` all finish.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KDrop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KCore (MS trV)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net (NSt NStep rh wh)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)

/-- **The simulation**: a step of the generated module is a step of the `Net` node program. -/
theorem step_sim {k : KM} {N c c' s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt KSt} (hR : RelD (rh c) (wh c') s ms x)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ (NStep (node k c c') s st x st' x' ∨ (st' = st ∧ x' = x)) :=
  Silmaril.Proofs.Wasm.JcoTool.KDrop.step_sim hN hs hR h

/-- The machine after the lift is related to the node's initial state. -/
theorem init_rel (k : KM) (c c' s : Nat) :
    RelD (rh c) (wh c') s (initMSD k (rh c) (wh c') s) (NSt.init (node k c c')) :=
  Silmaril.Proofs.Wasm.JcoTool.KDrop.init_rel k c c' s

/-- The chain of generated modules is a well-formed network. -/
theorem kchain_wf (xs : List Val) (ks : List KM) : (kchain xs ks).WF :=
  Silmaril.Proofs.Wasm.JcoTool.KDrop.kchain_wf xs ks

/-- **Correctness of a chain of generated modules** under the drop semantics. -/
theorem kchain_correct {xs : List Val} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26) {c : KSys ks.length}
    (h : KReach xs ks Nb c) {b : Bool} (hb : c.snk.rd = .gone b) : c.snk.got = runs ks xs :=
  Silmaril.Proofs.Wasm.JcoTool.KDrop.kchain_correct hN hws h hb

/-- **Safety**: at every point the sink holds a prefix of the composite. -/
theorem kchain_safe {xs : List Val} {ks : List KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26) {c : KSys ks.length}
    (h : KReach xs ks Nb c) : c.snk.got <+: runs ks xs :=
  Silmaril.Proofs.Wasm.JcoTool.KDrop.kchain_safe hN hws h

/-- **A single generated module** between a source and a sink. -/
theorem kdrop_pipe_correct {xs : List Val} {k : KM} {Nb : Nat → Nat}
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) {c : KSys [k].length} (h : KReach xs [k] Nb c) {b : Bool}
    (hb : c.snk.rd = .gone b) : c.snk.got = (trV k).run xs :=
  kchain_correct hN (by simp) h hb

end Silmaril.Wasm.JcoTool.KDrop
