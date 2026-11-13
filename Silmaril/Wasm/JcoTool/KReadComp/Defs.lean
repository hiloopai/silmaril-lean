module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.JcoTool.KLive.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Defs
public import Silmaril.Wasm.Component.Streams.Alg.Defs

/-!
# Generated modules as core modules of the component algebra, read on Core

`KRead.Obs.game` is the strategy reading of a runtime (`KRead.core_game`: for a generated module
on Core 3.0, the stream game of its kernel). This module makes such readings the core semantics
of the component algebra, so that the network and algebra theorems (`NetGame`, `KGame`), stated
for every core semantics `C` and realisations `StreamGame.Realizes C c T`, apply to concrete
components whose core module is a generated module read on Core:

* `Obs` is a core module type with one import `in` and one export `out` (each a stream end);
* `obsSem : CoreSem Obs`: the strategy of a module is its reading `O.game`, seen at one import
  and one export (`atSizes 1 1`);
* `obsComp O`: the component with one import, one core instance of `O` wired to it, and its one
  export re-exported (the shape `stage` has in `Streams.Alg`);
* `CoreGen`: a generated module instantiated on Core 3.0, `CoreGen.obs` its observation,
  `CoreGen.OK` its side conditions.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KReadComp

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Algebra (reexport)
open Silmaril.Wasm.JcoTool.KRead (Obs coreObs Inst0 FlushNil)
open Silmaril.Wasm.JcoTool.KCore (BI)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- An observed runtime is a core module with one import and one export. -/
instance : CoreModule Obs := ⟨fun _ => [("in", ⟨[], []⟩)], fun _ => [("out", ⟨[], []⟩)]⟩

/-- **The core semantics of observed runtimes**: their strategy readings. -/
noncomputable def obsSem : CoreSem Obs where
  sem O := atSizes 1 1 O.game

/-- **The component of an observed runtime**: one import, the core instance on it, one export. -/
def obsComp (O : Obs) : Comp Obs :=
  .mk [("in", Streams.Alg.ftS)] [.core O [Impl.fwd 0]] (reexport 1 [⟨"out", Streams.Alg.ftS, Impl.fwd 0⟩])

/-- **A generated module instantiated on Core 3.0**: the host functions `hb` of the built-ins,
the instance's memory `ma` and callback address `a`, the kernel `k`, the read size `N`, the
module instance `mi` and the Core store `cs₀` after instantiation. -/
structure CoreGen where
  H : Type
  hb : BI → H
  ma : Nat
  a : Nat
  k : KM
  N : Nat
  mi : Silmaril.Wasm.Execution.Core.ModuleInst
  cs₀ : Silmaril.Wasm.Execution.Core.Store H

/-- Its observation on Core 3.0, in the deterministic profile with grow oracle `o`. -/
noncomputable def CoreGen.obs (o : GrowKind → Nat → Nat → Nat → Bool) (g : CoreGen) : Obs :=
  coreObs (Profile.deterministic o) g.hb g.ma g.a g.k g.cs₀

/-- It is well formed: distinct built-ins are distinct host functions, the read size is in
`1..256`, the store holds the module with the lift's globals (`Inst0`), the kernel's flush is
empty when it is done, and the kernel's bounds hold (`KLive.KFits`: it never overflows the module's
fixed buffers; true of every `KFit.Small` kernel). -/
def CoreGen.OK (g : CoreGen) : Prop :=
  Function.Injective g.hb ∧ (0 < g.N ∧ g.N ≤ 256) ∧ Inst0 g.hb g.ma g.a g.k g.N g.mi g.cs₀ ∧
    FlushNil g.k ∧ Silmaril.Wasm.JcoTool.KLive.KFits g.k g.N

end Silmaril.Wasm.JcoTool.KReadComp
