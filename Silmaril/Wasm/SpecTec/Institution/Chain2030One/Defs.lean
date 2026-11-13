module

public import Silmaril.Wasm.SpecTec.Institution.Chain2030.Defs

/-!
# The chain wasm-2.0 → wasm-3.0 where one V2 step is one Core step: definitions

an earlier chain (`Chain2030.chain`) carries only value-blind sentences, because
`Step.toCore` matches one V2 step by a *run* of Core steps. This header names the sub-fragment
of `Chain2030.PairDom` on which the run has length one in both directions, and the witnesses of
An earlier step.

* `SimV hn`: the relation between SpecTec values that encode `Sim`-related configurations, the
  V2 one by `Sim20.configV`, the Core one by `Sim.configV`.
* `OneFwd`, `OneBwd`: every V2 step of the first component is matched by one Core step of the
  second, with `Sim`-related results, and conversely.
* `PairDom1`: `PairDom`, `OneFwd` and `OneBwd`. `m20Chart1`, `v2PChart1` are an earlier charts on
  it.
* `CodeNil`: the encoded code is empty, a value-sensitive predicate.
* `coreNop`, `coreNop1`, `coreDone`, `v2Nop1`, `v2Done`, `nopPair`, `nop1Pair`: `nop nop`, `nop` and the
  empty code, on the empty store, in Core and V2.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Chain2030

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Institution

variable {H : Type}

/-- **Values of `Sim`-related configurations**: `w` encodes a V2 configuration (`Sim20.configV`)
and `w'` a Core configuration (`Sim.configV`) that simulates it. -/
def SimV (hn : H → String) (w w' : Value) : Prop :=
  ∃ (c : Silmaril.Wasm.V2.Execution.Config H) (cc : Silmaril.Wasm.Execution.Core.Config H),
    Silmaril.Wasm.V2.Execution.Sim c cc ∧ w = Silmaril.Wasm.SpecTec.Sim20.configV hn c ∧
      w' = Silmaril.Wasm.SpecTec.Sim.configV hn cc

/-- **One V2 step is one Core step**: every V2 successor of `p.1` is simulated by a Core
successor of `p.2`. -/
def OneFwd (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (p : Pair H) : Prop :=
  ∀ c', Silmaril.Wasm.V2.Execution.Step P host p.1 c' →
    ∃ cc', Silmaril.Wasm.Execution.Core.Step P tgt p.2 cc' ∧ Silmaril.Wasm.V2.Execution.Sim c' cc'

/-- **One Core step is one V2 step**: every Core successor of `p.2` simulates a V2 successor of
`p.1`. -/
def OneBwd (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (p : Pair H) : Prop :=
  ∀ cc', Silmaril.Wasm.Execution.Core.Step P tgt p.2 cc' →
    ∃ c', Silmaril.Wasm.V2.Execution.Step P host p.1 c' ∧ Silmaril.Wasm.V2.Execution.Sim c' cc'

/-- **The one-step sub-fragment of the chain's domain.** -/
def PairDom1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (p : Pair H) : Prop :=
  PairDom P tgt p ∧ OneFwd P host tgt p ∧ OneBwd P host tgt p

/-- The wasm-2.0 model's step chart on the one-step sub-fragment. -/
noncomputable def m20Chart1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) : Chart :=
  BChart (Pair H) Unit Value (PairDom1 P host tgt) fun p _ =>
    {w | (Wasm20.stepModel20 (Silmaril.Wasm.SpecTec.Sim.Floats.floatIntB P)).D "Step" "%~>%" []
      (.tuple [Silmaril.Wasm.SpecTec.Sim20.configV hn p.1, w])}

/-- The V2 step chart on the one-step sub-fragment. -/
def v2PChart1 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) : Chart :=
  BChart (Pair H) Unit Value (PairDom1 P host tgt) fun p u => Wasm20.v2Obs P host hn p.1 u

/-- **The encoded code is empty**: a value-sensitive predicate on SpecTec configurations, read
the same way off both encodings (`state; instr*` with `instr* = []`). -/
def CodeNil (w : Value) : Prop := ∃ st, w = .case "%;%" (.tuple [st, .list []])

/-! ## Witnesses -/

/-- `nop nop` in Core, on the empty store, in a frame over the empty module. -/
def coreNop : Silmaril.Wasm.Execution.Core.Config H :=
  ⟨{}, ⟨[], {}⟩, [.plain .nop, .plain .nop]⟩

/-- `nop` in Core. -/
def coreNop1 : Silmaril.Wasm.Execution.Core.Config H := ⟨{}, ⟨[], {}⟩, [.plain .nop]⟩

/-- The empty code in Core. -/
def coreDone : Silmaril.Wasm.Execution.Core.Config H := ⟨{}, ⟨[], {}⟩, []⟩

/-- The empty code in V2. -/
def v2Done : Silmaril.Wasm.V2.Execution.Config H := ⟨{}, {}, []⟩

/-- `nop nop` in V2 and Core. -/
def nopPair : Pair H := (Wasm20.nopCfg, coreNop)

/-- `nop` in V2. -/
def v2Nop1 : Silmaril.Wasm.V2.Execution.Config H := ⟨{}, {}, [.plain .nop]⟩

/-- `nop` in V2 and Core. -/
def nop1Pair : Pair H := (v2Nop1, coreNop1)

end Silmaril.Wasm.SpecTec.Institution.Chain2030
