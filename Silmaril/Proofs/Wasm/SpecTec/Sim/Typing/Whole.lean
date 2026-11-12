module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Facts
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Ctrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Types
public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs

/-!
# The typing parts of `Whole.Assumptions`, discharged

`assumptions_of`: `Whole.Assumptions B hn host` follows from its non-typing fields alone (plus
the block-type typing hypothesis of `exnTyping_simEnv`). The typing fields `typing`, `state`,
`rTyping`, `ctrlTyping` are proved for every `B` (`typingFacts_simEnv`, `stateTyping_simEnv`,
`rTyping_simEnv`, `ctrlTyping_simEnv`), and so is `exnTyping` (`exnTyping_simEnv'`);
`assumptions_of'` needs only the non-typing fields.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- **`Whole.Assumptions` from its non-typing fields.** -/
theorem assumptions_of {H : Type} (B : Builtins) (hn : H → String) (host : HostSemantics H)
    (hbt : ∀ bt : BlockType, TypedV (simEnv B) Exn.blocktypeT (Encode.toValue bt))
    (intB : IntNumeric.IntB B) (rFuns : RefsGC.RFuns (simEnv B))
    (rStore : RefsGC.RStoreFuns (simEnv B)) (refOk : RefsGC.RefOkBridge (simEnv B))
    (ctrlState : CtrlState (simEnv B) hn) (ctrlCall : CtrlCall (simEnv B))
    (ctrlHost : CtrlHost (simEnv B) hn host) (exnHelpers : Exn.Helpers (simEnv B) hn) :
    Whole.Assumptions B hn host where
  typing := typingFacts_simEnv B hn
  intB := intB
  state := stateTyping_simEnv B
  rTyping := rTyping_simEnv B
  rFuns := rFuns
  rStore := rStore
  refOk := refOk
  ctrlTyping := ctrlTyping_simEnv B
  ctrlState := ctrlState
  ctrlCall := ctrlCall
  ctrlHost := ctrlHost
  exnTyping := exnTyping_simEnv B hbt
  exnHelpers := exnHelpers

/-- **`Whole.Assumptions` from its non-typing fields alone**: every typing field is proved. -/
theorem assumptions_of' {H : Type} (B : Builtins) (hn : H → String) (host : HostSemantics H)
    (intB : IntNumeric.IntB B) (rFuns : RefsGC.RFuns (simEnv B))
    (rStore : RefsGC.RStoreFuns (simEnv B)) (refOk : RefsGC.RefOkBridge (simEnv B))
    (ctrlState : CtrlState (simEnv B) hn) (ctrlCall : CtrlCall (simEnv B))
    (ctrlHost : CtrlHost (simEnv B) hn host) (exnHelpers : Exn.Helpers (simEnv B) hn) :
    Whole.Assumptions B hn host :=
  assumptions_of B hn host typedV_blocktype intB rFuns rStore refOk ctrlState ctrlCall ctrlHost
    exnHelpers

end Silmaril.Wasm.SpecTec.Sim.Typing
