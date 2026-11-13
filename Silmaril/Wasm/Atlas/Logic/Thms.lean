module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Logic.Defs
public import Silmaril.Wasm.Logic.VC.Thms

/-!
# The program-logic charts: results

`Logic.vcToHoare P host`: the identity on code and postconditions from the VC chart to the
Hoare chart, preserving every sentence (`VC.wpc_sound`, every profile and host).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Logic

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (HostSemantics)

/-- **VC soundness as a transition** (preserves every sentence). -/
def vcToHoare (P : Profile) {H : Type} (host : HostSemantics H) :
    Transition (vcChart H) (hoareChart P host) where
  pt x := x
  sen Q := Q
  cls _ := True
  dir := .preserves
  dom_pt _ h := h
  sat x Q _ _ := ⟨fun _ ⟨inv, k, h⟩ => Silmaril.Wasm.Logic.VC.wpc_sound (P := P) (host := host)
      inv k x.2.2.2 Q x.1 x.2.1 x.2.2.1 h, fun e => absurd e (by decide)⟩

end Silmaril.Wasm.Atlas.Logic
