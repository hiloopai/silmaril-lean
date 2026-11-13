module

public import Silmaril.Wasm.Models.V2CoreInstHostFn.Thms

/-!
# The 2.0 instantiation models at every host type: definitions

`V2CoreSpec.v20instHT P`, `V2CoreInstImp.domInstP P`, `V2CoreInstImp.ImportsTransport` and
`V2CoreInstHostFn.domInstHost P` are stated at points `Pt Nat`. The underlying model
`V2CoreInst.v20instG P H` and every ingredient of the domains (`V2Core.dom`, `HostEmbV`,
`GlobalsNamed`, `ptCore`, `closedV`) are generic in the host type `H`. The definitions below are
the same statements at every `H`; at `H = Nat` they are the originals by definition
(`v20instHTG_nat`, `domInstPG_nat_iff`, `domInstHostG_nat_iff`, `importsTransportG_nat_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstGen

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec Silmaril.Wasm.Models.V2CoreInst

/-- **`v20instHT P` at every host type.** -/
def v20instHTG (P : Profile) (H : Type) : WasmModel where
  feats := (v20instG P H).feats
  Module := (v20instG P H).Module
  Valid := (v20instG P H).Valid
  Pt := (v20instG P H).Pt
  Call := (v20instG P H).Call
  Obs := (v20instG P H).Obs
  obs := (v20instG P H).obs
  dom p := dom p ∧ HostEmbV p.2 ∧ GlobalsNamed (ptCore p).1

/-- **`domInstP P` at every host type**: behaviours read at the closed host. -/
def domInstPG (P : Profile) {H : Type} (p : Pt H) : Prop :=
  (v20instHTG P H).dom p ∧
    ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
      (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
      Silmaril.Wasm.V2.Validation.ModuleValid m → Silmaril.Wasm.V2.Module.toCore m = some cm →
      (∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (ptCore p).2 (ptCore p).1 cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
      ∃ c, Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf P closedV c).Nonempty

/-- **`domInstHost P` at every host type**: behaviours read at the point's own host. -/
def domInstHostG (P : Profile) {H : Type} (p : Pt H) : Prop :=
  (v20instHTG P H).dom p ∧
    ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
      (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
      Silmaril.Wasm.V2.Validation.ModuleValid m → Silmaril.Wasm.V2.Module.toCore m = some cm →
      (∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (ptCore p).2 (ptCore p).1 cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
      ∃ c, Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf P p.2 c).Nonempty

/-- **`ImportsTransport` at every host type.** -/
def ImportsTransportG {H : Type} (p : Pt H) : Prop :=
  ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr)
    (ixt xt : List Silmaril.Wasm.V2.ExternType)
    (xtI xtE : List Silmaril.Wasm.Validation.CExternType),
    Silmaril.Wasm.V2.Validation.ModuleOk m ixt xt → Silmaril.Wasm.V2.Module.toCore m = some cm →
    Silmaril.Wasm.Validation.ModuleOk cm ⟨xtI, xtE⟩ →
    List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore p).1)
      (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) xtI →
    List.Forall₂ (Silmaril.Wasm.V2.Execution.ExternAddrOk p.1) xas ixt

end Silmaril.Wasm.Models.V2CoreInstGen
