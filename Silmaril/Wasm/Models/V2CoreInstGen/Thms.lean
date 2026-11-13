module

public import Silmaril.Wasm.Models.V2CoreInstGen.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstGen.Main

/-!
# The 2.0 instantiation models at every host type, and `domInstP` at a host-function store

Proofs in `Silmaril.Proofs.Wasm.Models.V2CoreInstGen.{StartHost,Main}`. See `docs/projects/spectec/README.md`,
"v10-inst".

* `v20instHTG P H`, `domInstPG P`, `domInstHostG P`, `ImportsTransportG`: 's and an earlier
  `v20instHT P`, `domInstP P`, `domInstHost P`, `ImportsTransport` at every host type `H`; at
  `Nat` they are the originals by definition.
* **`importsTransportG_all`**, **`domInstHostG_of_storeOk`**, **`domInstPG_of_storeOk_any`**: the
  domain theorems at every host type.
* **`not_domInstP_hostDivPt`**: `hostDivPt` (one host function, host `divV`) is **not** in
  `domInstP P`, at every profile. The witness `startMod` imports the host function and starts
  with it; Core instantiates its image, and every 2.0 instantiation is stuck at `CALL_ADDR 0`
  under `closedV`. So `domInstP` and `domInstHost` differ, and the host-free hypothesis of
  `domInstPG_of_storeOk_any` cannot be dropped.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstGen.not_domInstP_hostDivPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.Models.V2CoreInstGen.not_domInstP_hostDivPt

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstGen.importsTransportG_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.Models.V2CoreInstGen.importsTransportG_all

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstGen.domInstHostG_of_storeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.Models.V2CoreInstGen.domInstHostG_of_storeOk

/-- info: 'Silmaril.Proofs.Wasm.Models.V2CoreInstGen.domInstPG_of_storeOk_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.Models.V2CoreInstGen.domInstPG_of_storeOk_any
