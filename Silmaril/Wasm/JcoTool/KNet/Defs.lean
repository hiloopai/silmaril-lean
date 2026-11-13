module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Wasm.Component.Streams.Pipes.Defs

/-!
# Networks with generated modules: tees and any other shape

`KDrop.kchain` puts generated modules (`KDrop.genD`) in a chain between a source and a sink. This
module puts them in **any** `Net` network: an `MNet` is a network together with the nodes that
run as generated modules (`gen i = some (k, N)`: node `i` is the module `genD k N`, its node in
the network must be `KDrop.node k c c'`); the other nodes run the generic node program `NStep`
(sources, tees, sinks, other transformers). `MStep` is a step of one node: `NStep` for a network
node, `DRStep` (the callback runtime over the drop-faithful built-ins) for a module.

`ktee xs k₁ k₂ N₁ N₂` is `Pipes.teeNet xs (trV k₁) (trV k₂)` with its two branches run as
generated modules: **a tee of generated modules** (source → tee → (`genD k₁` → sink₁,
`genD k₂` → sink₂)). `kchain2` is `Pipes.chain` with both stages generated.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (MS trV)
open Silmaril.Wasm.JcoTool.KDrop

/-- **A network with generated modules**: the nodes `i` with `gen i = some (k, N)` run as
`genD k N`. -/
structure MNet where
  net : Network
  gen : Fin net.k → Option (KM × Nat)

/-- The module nodes are well placed: their node is `KDrop.node k c c'` (one input `c`, one
output `c'`, the kernel's transformer), their read size is in `1..256`, and the waitable sets
fit in the handle range. -/
structure MNet.OK (M : MNet) : Prop where
  node : ∀ i k N, M.gen i = some (k, N) → ∃ c c', M.net.node i = KDrop.node k c c'
  size : ∀ i k N, M.gen i = some (k, N) → 0 < N ∧ N ≤ 256
  ws : 2 * M.net.m + 1 + M.net.k < 2 ^ 28
  wf : M.net.WF

/-- The store, the state of every network node, the machine of every module. -/
structure MSys (net : Network) where
  st : DStore
  ns : (i : Fin net.k) → NSt (net.node i).σ
  ms : Fin net.k → MS

/-- **One step**: of a network node (`NStep`) or of a module (`DRStep`). -/
inductive MStep (M : MNet) : MSys M.net → MSys M.net → Prop where
  | node {s : MSys M.net} (i : Fin M.net.k) {st' x'} : M.gen i = none →
      NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' →
      MStep M s ⟨st', Function.update s.ns i x', s.ms⟩
  | mod {s : MSys M.net} (i : Fin M.net.k) {k N st' m'} : M.gen i = some (k, N) →
      DRStep (genD k N) s.st (s.ms i) st' m' →
      MStep M s ⟨st', s.ns, Function.update s.ms i m'⟩

/-- Steps, iterated. -/
inductive MSteps (M : MNet) : MSys M.net → MSys M.net → Prop where
  | refl (s : MSys M.net) : MSteps M s s
  | tail {s s' s''} : MSteps M s s' → MStep M s' s'' → MSteps M s s''

/-- The machine of a module after its lift (on its node's input and output streams). -/
def initM (M : MNet) (i : Fin M.net.k) : MS :=
  match M.gen i with
  | some (k, _) => initMSD k (rh ((M.net.node i).inp.getD 0)) (wh ((M.net.node i).outs.headD 0))
      (M.net.ws i)
  | none => ⟨fun _ => 0, fun _ => 0, none, .exited⟩

/-- The start: the network's setup store, every node initial, every module after its lift. -/
def MSys.init (M : MNet) : MSys M.net := ⟨initStore M.net, fun i => NSt.init (M.net.node i), initM M⟩

/-- The reachable systems. -/
def MReach (M : MNet) (s : MSys M.net) : Prop := MSteps M (MSys.init M) s

/-! ## Tees and chains of generated modules -/

open Silmaril.Wasm.Component.Streams.Pipes (teeNet chain)

/-- **A tee of generated modules**: `teeNet` with nodes `2` and `3` (the branches) run as
`genD k₁ N₁` and `genD k₂ N₂`. -/
def ktee (xs : List Val) (k₁ k₂ : KM) (N₁ N₂ : Nat) : MNet where
  net := teeNet xs (trV k₁) (trV k₂)
  gen i := if i.val = 2 then some (k₁, N₁) else if i.val = 3 then some (k₂, N₂) else none

/-- **Two generated modules in a chain**: `Pipes.chain` with nodes `1` and `2` run as modules. -/
def kchain2 (xs : List Val) (k₁ k₂ : KM) (N₁ N₂ : Nat) : MNet where
  net := chain xs (trV k₁) (trV k₂)
  gen i := if i.val = 1 then some (k₁, N₁) else if i.val = 2 then some (k₂, N₂) else none

end Silmaril.Wasm.JcoTool.KNet
