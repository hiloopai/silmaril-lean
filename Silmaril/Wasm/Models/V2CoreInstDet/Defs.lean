module

public import Silmaril.Wasm.Models.V2CoreSpecImg.Thms
public import Silmaril.Wasm.Models.V2CoreInst.Thms

/-!
# The instantiation model at the deterministic profile: definitions

An earlier step asks for the reverse inclusion `coreInst ⊆ v20instG` of the instantiation embedding
`v20InstEmbHU`. As stated, with the call map `instCall`, it is false. A 2.0 module with no Core
image is sent to the empty Core module, which Core instantiates, while `v20instG` observes
nothing on it (`Silmaril.Wasm.Models.V2CoreInstDet.instCall_not_eq`). The definitions below are the
restatement that the header proves:

* `badModule`: a Core module with a start function and no functions, so it has no instantiation;
* `instCallE`: `instCall` on 2.0-valid modules with a Core image, and `badModule` on the
  others;
* `domInstDet g`: points of `v20instHT`'s domain at which every image call of a 2.0-valid
  module that Core instantiates has a 2.0 instantiation run whose closed-host behaviours are
  not empty. This is the instantiation form of the call model's `domDet`. The same condition
  over all modules with a Core image holds at no point (`DomInstDetU`, `not_domInstDetU`): Core
  instantiates the image of a 2.0 module with two memories, which 2.0 rejects;
* `v20instDet g`: `v20instG` at `Profile.deterministic g` on `domInstDet g`.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstDet

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreInst
  Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- A Core module with a start function and no functions: it is not valid, so it has no
instantiation. -/
def badModule : Silmaril.Wasm.Module := { start := some ⟨0⟩ }

open Classical in
/-- **The call map of the deterministic instantiation embedding**: the image call when the module
is 2.0-valid and has a Core image, and an uninstantiable call otherwise. 2.0 instantiation
requires 2.0 validity, so `v20instG` observes nothing on the other calls. -/
noncomputable def instCallE
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr :=
  match Silmaril.Wasm.V2.Module.toCore mx.1 with
  | some cm =>
    if Silmaril.Wasm.V2.Validation.ModuleValid mx.1 then
      (cm, mx.2.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore)
    else (badModule, [])
  | none => (badModule, [])

/-- **The domain of the deterministic instantiation embedding**: `v20instHT`'s domain, and every
image call of a 2.0-valid module that Core instantiates has a 2.0 instantiation run whose
closed-host behaviours are not empty. Without the validity premise no point satisfies the
condition (`Silmaril.Wasm.Models.V2CoreInstDet.not_domInstDetU`). -/
def domInstDet (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) : Prop :=
  (v20instHT (Profile.deterministic g)).dom p ∧
    ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
      (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
      Silmaril.Wasm.V2.Validation.ModuleValid m → Silmaril.Wasm.V2.Module.toCore m = some cm →
      (∃ C, Silmaril.Wasm.Execution.Core.Instantiate (Profile.deterministic g) (ptCore p).2
        (ptCore p).1 cm (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
      ∃ c, Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV c).Nonempty

/-- `domInstDet`'s condition without the validity premise. No point satisfies it
(`Silmaril.Wasm.Models.V2CoreInstDet.not_domInstDetU`). -/
def DomInstDetU (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) : Prop :=
  ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
    Silmaril.Wasm.V2.Module.toCore m = some cm →
    (∃ C, Silmaril.Wasm.Execution.Core.Instantiate (Profile.deterministic g) (ptCore p).2
      (ptCore p).1 cm (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
    ∃ c, Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c ∧
      (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV c).Nonempty

/-- **The 2.0 instantiation model at the deterministic profile** on `domInstDet g`. -/
def v20instDet (g : GrowKind → Nat → Nat → Nat → Bool) : WasmModel where
  feats := (v20instG (Profile.deterministic g) Nat).feats
  Module := (v20instG (Profile.deterministic g) Nat).Module
  Valid := (v20instG (Profile.deterministic g) Nat).Valid
  Pt := (v20instG (Profile.deterministic g) Nat).Pt
  Call := (v20instG (Profile.deterministic g) Nat).Call
  Obs := (v20instG (Profile.deterministic g) Nat).Obs
  obs := (v20instG (Profile.deterministic g) Nat).obs
  dom := domInstDet g

end Silmaril.Wasm.Models.V2CoreInstDet
