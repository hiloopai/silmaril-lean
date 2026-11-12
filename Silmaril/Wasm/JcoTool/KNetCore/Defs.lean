module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.JcoTool.KNet.Defs

/-!
# Networks of generated modules running on Core 3.0

`KNet.MNet` runs the generated modules of a `Net` network under the model runtime `KDrop.DRStep`
(the callback's body executed by the fragment semantics `KDrop.dexec`). `KRead` replaced `dexec`
by Core 3.0 (`KRead.CRStepU`: Core invocations of the callback, the built-ins as host calls over
the drop store) for **one** module between a source and a sink. Here every module of any network
runs on Core 3.0:

* `CSys H net`: the shared drop store, the state of every network node, and for every module its
  Core store, pending read and runtime mode;
* `CStep o hb ma mi a M`: a step of a network node (`Net.NStep`), or a step `CRStepU` of a
  module's runtime on Core 3.0 (deterministic profile `o`), its instance `mi i` holding the
  callback at function address `a i` and its memory at `ma i`;
* `CRel M m c`: the Core system `c` stands for the model system `m`: the same store and nodes,
  and every module's Core store holds the model machine's globals and memory (`KCoreRun.InstR`)
  and the callback (`KCoreRun.CbAt`).

`KNetCore.Thms` (`creach_abs`): every reachable Core system of a live network stands for a
reachable model system, so every theorem about `MNet` networks holds when the modules run on Core.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KNetCore

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.JcoTool.KCore (BI MS Mode)
open Silmaril.Wasm.JcoTool.KDrop (genD)
open Silmaril.Wasm.JcoTool.KNet (MNet MSys)
open Silmaril.Wasm.JcoTool.KCoreRun (InstR CbAt)
open Silmaril.Wasm.JcoTool.KRead (CRStepU)

/-- **A network with its modules on Core 3.0.** -/
structure CSys (H : Type) (net : Network) where
  st : DStore
  ns : (i : Fin net.k) → NSt (net.node i).σ
  cs : Fin net.k → Store H
  rp : Fin net.k → Option (Nat × Nat)
  md : Fin net.k → Mode

variable {H : Type}

/-- **One step**: of a network node, or of a module's runtime on Core 3.0. -/
inductive CStep (o : GrowKind → Nat → Nat → Nat → Bool) (hb : BI → H) (ma : Nat) (M : MNet)
    (a : Fin M.net.k → Nat) : CSys H M.net → CSys H M.net → Prop where
  | node {s : CSys H M.net} (i : Fin M.net.k) {st' x'} : M.gen i = none →
      NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' →
      CStep o hb ma M a s ⟨st', Function.update s.ns i x', s.cs, s.rp, s.md⟩
  | mod {s : CSys H M.net} (i : Fin M.net.k) {k N st' cs' rp' md'} : M.gen i = some (k, N) →
      CRStepU (Profile.deterministic o) hb ma (a i) (s.st, s.cs i, s.rp i, s.md i) (st', cs', rp', md') →
      CStep o hb ma M a s ⟨st', s.ns, Function.update s.cs i cs', Function.update s.rp i rp',
        Function.update s.md i md'⟩

/-- Steps, iterated. -/
inductive CSteps (o : GrowKind → Nat → Nat → Nat → Bool) (hb : BI → H) (ma : Nat) (M : MNet)
    (a : Fin M.net.k → Nat) : CSys H M.net → CSys H M.net → Prop where
  | refl (s : CSys H M.net) : CSteps o hb ma M a s s
  | tail {s s' s''} : CSteps o hb ma M a s s' → CStep o hb ma M a s' s'' → CSteps o hb ma M a s s''

/-- **The Core system stands for the model system.** -/
def CRel (hb : BI → H) (ma : Nat) (M : MNet) (mi : Fin M.net.k → ModuleInst) (a : Fin M.net.k → Nat)
    (m : MSys M.net) (c : CSys H M.net) : Prop :=
  c.st = m.st ∧ c.ns = m.ns ∧ ∀ i k N, M.gen i = some (k, N) →
    c.rp i = (m.ms i).rp ∧ c.md i = (m.ms i).mode ∧ InstR hb ma (c.cs i) (mi i) (m.ms i).g (m.ms i).m ∧
      CbAt (c.cs i) (mi i) (genD k N) (a i)

end Silmaril.Wasm.JcoTool.KNetCore
