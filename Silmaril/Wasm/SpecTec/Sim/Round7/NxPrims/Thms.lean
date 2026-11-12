module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxPrims.Call2
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Thms

/-!
# Round 7, REH route 2: the primitives conform (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims`; see `docs/projects/spectec/README.md`.

* `builtinsVT_BI : BuiltinsVT sigX tsigFixed (envBI P hn host)`: round 4's primitives
  (`Prims.builtins`, with `$utf8`) answer conforming values. Round 3's strictness lemmas
  (`EraseAll.oks_call`, `oks_utf8Call`) cover every primitive except `$hostcall`, `$blocktype_`
  and `$sx`. `$blocktype_` answers an instruction type (`na_blocktype`), `$sx` answers `ε`, and
  `$hostcall` answers `outcomeV` images, which conform at `hostcallresult` (`vtB_outcomeV`,
  through `vtB_storeV`, `vtB_funcInst`, `vtB_moduleInst`).
* `defsVT_BI`: with `NxFlow.flowSound`, definitions conform at every fuel in `envBI P hn host`,
  with no hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

/-- **Definitions conform at every fuel at round 4's primitives.** -/
theorem defsVT_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : HostSemantics H) (n : Nat) : DefsVT sigX tsigFixed (envBI P hn host) n :=
  NxFlow.flowSound _ (builtinsVT_BI P hn host) n

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims.defsVT_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms defsVT_BI

end Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims
