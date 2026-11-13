module

public import Silmaril.Wasm.JcoTool.KTee.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KTee.Main

/-!
# The generated tee refines the tee node of `Net`

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KTee.{Basic,Exec,Rel,Ready,Drops,Events,Main}`.

The module `genT N` (`KTee.Defs`), run by the callback runtime `KDrop.DRStep` over the
drop-faithful stream built-ins of `Silmaril.Wasm.Component.Streams.Drop`, implements the generic
node program of `Silmaril.Wasm.Component.Streams.Net` for a node with one input and two outputs
(`teeNode a b c`, transformer `trB`: every item as the `u8` of its byte):

* **`step_sim`**: every step of the runtime from a machine related (`RelT`) to a node state is
  a step `NStep` of `teeNode a b c` to a related state (a write of either output, a read, a drop
  of the input or of an output, or the handling of an event of any of the three ends: the
  pending copy's result, or `DROPPED` on an idle end), or a step that changes neither the store
  nor the node (`EXIT`, `WAIT`).
* **`init_rel`**: the machine after the lift is related to the node's initial state.

Every interleaving, every chunking of the copies and every order of the events is covered: the
theorem is about any step from any related state. What is modelled, not proved, is as for
`KDrop.genD`: `dexec` stands for the module's WebAssembly; the runtime delivers well-formed
events (`wfD`); the lift's prologue (`entryT`) is the network's setup store.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTee

open Silmaril.Wasm.JcoTool.KCore (MS)
open Silmaril.Wasm.JcoTool.KDrop (DRStep)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net (NSt NStep rh wh)

/-- **The simulation**: a step of the generated tee is a step of the tee node, or changes neither
the store nor the node. -/
theorem step_sim {N a b c s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Unit} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (h : DRStep (genT N) st ms st' ms') :
    ∃ x', RelT (rh a) (wh b) (wh c) s ms' x' ∧
      (NStep (teeNode a b c) s st x st' x' ∨ (st' = st ∧ x' = x)) :=
  Silmaril.Proofs.Wasm.JcoTool.KTee.step_sim hN hs hR h

/-- The machine after the lift is related to the node's initial state. -/
theorem init_rel (a b c s : Nat) :
    RelT (rh a) (wh b) (wh c) s (initMST (rh a) (wh b) (wh c) s) (NSt.init (teeNode a b c)) :=
  Silmaril.Proofs.Wasm.JcoTool.KTee.init_rel a b c s

end Silmaril.Wasm.JcoTool.KTee
