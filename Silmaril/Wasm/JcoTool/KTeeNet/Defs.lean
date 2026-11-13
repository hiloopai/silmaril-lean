module

public import Silmaril.Wasm.JcoTool.KTee.Defs
public import Silmaril.Wasm.JcoTool.KNet.Defs

/-!
# Networks with generated kernels and generated tees

`KNet.MNet` runs generated kernel modules (`KDrop.genD`) as nodes of a `Net` network. A `GNet`
also runs **generated tees** (`KTee.genT`): node `i` with `gen i = some (.kern k N)` is the
module `genD k N` (its node must be `KDrop.node k c c'`), with `gen i = some (.tee N)` the module
`genT N` (its node must be `KTee.teeNode a b c`); the other nodes run the node program `NStep`.

`gtee xs N k₁ k₂ N₁ N₂` is **a tee network whose tee and both branches are generated modules**:
source → `genT N` → (`genD k₁ N₁` → sink₁, `genD k₂ N₂` → sink₂), the network `teeNetB` (as
`Pipes.teeNet`, with the byte tee `teeNode` in place of `Pipes.tee`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (MS Prog trV)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD initMSD)
open Silmaril.Wasm.JcoTool.KTee (genT initMST teeNode)
open Silmaril.Wasm.JcoTool.KNet (MSys)

/-- What a module node runs: a kernel or a tee, with its read size. -/
inductive Gen where
  | kern (k : KM) (N : Nat)
  | tee (N : Nat)

/-- The read size. -/
def Gen.N : Gen → Nat
  | .kern _ N => N
  | .tee N => N

/-- The generated program. -/
def Gen.prog : Gen → Prog
  | .kern k N => genD k N
  | .tee N => genT N

/-- **A network with generated kernels and tees.** -/
structure GNet where
  net : Network
  gen : Fin net.k → Option Gen

/-- The module nodes are well placed. -/
structure GNet.OK (M : GNet) : Prop where
  kern : ∀ i k N, M.gen i = some (.kern k N) → ∃ c c', M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c'
  tee : ∀ i N, M.gen i = some (.tee N) → ∃ a b c, M.net.node i = teeNode a b c
  size : ∀ i g, M.gen i = some g → 0 < g.N ∧ g.N ≤ 256
  ws : 2 * M.net.m + 1 + M.net.k < 2 ^ 28
  wf : M.net.WF

/-- **One step**: of a network node (`NStep`) or of a module (`DRStep`). -/
inductive GStep (M : GNet) : MSys M.net → MSys M.net → Prop where
  | node {s : MSys M.net} (i : Fin M.net.k) {st' x'} : M.gen i = none →
      NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' →
      GStep M s ⟨st', Function.update s.ns i x', s.ms⟩
  | mod {s : MSys M.net} (i : Fin M.net.k) {g st' m'} : M.gen i = some g →
      DRStep g.prog s.st (s.ms i) st' m' →
      GStep M s ⟨st', s.ns, Function.update s.ms i m'⟩

/-- Steps, iterated. -/
inductive GSteps (M : GNet) : MSys M.net → MSys M.net → Prop where
  | refl (s : MSys M.net) : GSteps M s s
  | tail {s s' s''} : GSteps M s s' → GStep M s' s'' → GSteps M s s''

/-- The machine of a module after its lift (on its node's streams). -/
def initG (M : GNet) (i : Fin M.net.k) : MS :=
  let nd := M.net.node i
  match M.gen i with
  | some (.kern k _) => initMSD k (rh (nd.inp.getD 0)) (wh (nd.outs.headD 0)) (M.net.ws i)
  | some (.tee _) =>
    initMST (rh (nd.inp.getD 0)) (wh (nd.outs.getD 0 0)) (wh (nd.outs.getD 1 0)) (M.net.ws i)
  | none => ⟨fun _ => 0, fun _ => 0, none, .exited⟩

/-- The start: the network's setup store, every node initial, every module after its lift. -/
def GSys.init (M : GNet) : MSys M.net := ⟨initStore M.net, fun i => NSt.init (M.net.node i), initG M⟩

/-- The reachable systems. -/
def GReach (M : GNet) (s : MSys M.net) : Prop := GSteps M (GSys.init M) s

/-! ## The generated tee network -/

/-- **Source → byte tee → (`T` → sink₁, `U` → sink₂)**: `Pipes.teeNet` with `teeNode 0 1 2`. -/
abbrev teeNetB {σ τ : Type} (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) : Network where
  k := 6
  node i := if i.val = 0 then Silmaril.Wasm.Component.Streams.Pipes.src xs 0 else if i.val = 1 then teeNode 0 1 2
    else if i.val = 2 then Silmaril.Wasm.Component.Streams.Pipes.stage T 1 3
    else if i.val = 3 then Silmaril.Wasm.Component.Streams.Pipes.stage U 2 4
    else if i.val = 4 then Silmaril.Wasm.Component.Streams.Pipes.sink 3 else Silmaril.Wasm.Component.Streams.Pipes.sink 4
  m := 5
  wr c := if c = 0 then (0, 0) else if c = 1 then (1, 0) else if c = 2 then (1, 1)
    else if c = 3 then (2, 0) else (3, 0)
  rd c := if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 3 then 4 else 5

/-- **A tee whose tee and branches are generated modules.** -/
def gtee (xs : List Val) (N : Nat) (k₁ k₂ : KM) (N₁ N₂ : Nat) : GNet where
  net := teeNetB xs (trV k₁) (trV k₂)
  gen i := if i.val = 1 then some (.tee N) else if i.val = 2 then some (.kern k₁ N₁)
    else if i.val = 3 then some (.kern k₂ N₂) else none

end Silmaril.Wasm.JcoTool.KTeeNet
