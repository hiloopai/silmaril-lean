module

public import Silmaril.Wasm.Component.Lime1RefE.Defs
public import Silmaril.Wasm.Component.Lime1Ref.Thms
public import Silmaril.Wasm.Component.Lime1Bridge.Thms
import Silmaril.Proofs.Wasm.Component.Lime1RefE.Facts

/-!
# The machine half for the Lime1 engine: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.Lime1RefE.{Relabel,Prepare,Facts}` and, for the
engine-generic re-run of `refToSpec_of_arity`, `Silmaril.Wasm.Component.EngineRef`.

* `refToSpecE_lime1_of` (proved): **`Lime1Ref.RefToSpecELime1` follows from
  `Lime1InstOk` and `Lime1TypedOk`**;
* `refToSpec_lime1_of_E'` (proved): the corrected `RefToSpec lime1G`
  (`Lime1Ref.RefToSpecLime1`) follows from `Lime1InstOk`, `Lime1TypedOk` and the
  store-level bridge `Lime1Bridge.InstBridgeE`.

Open: `Lime1InstOk` and `Lime1TypedOk` (see `Defs`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RefE

open Silmaril.Wasm.Component.Lime1Ref

/-- **The machine half for Lime1 from the two open engine facts.** -/
theorem refToSpecE_lime1_of (hI : Lime1InstOk) (hT : Lime1TypedOk) :
    Lime1Ref.RefToSpecELime1 :=
  Silmaril.Proofs.Wasm.Component.Lime1RefE.refToSpecE_lime1_of hI hT

/-- **The corrected `RefToSpec lime1G` from the two engine facts and the relational
instantiation statement** `Lime1Bridge.InstBridgeE`. -/
theorem refToSpec_lime1_of_E' (hI : Lime1InstOk) (hT : Lime1TypedOk)
    (hB : Silmaril.Wasm.Component.Lime1Bridge.InstBridgeE) : Lime1Ref.RefToSpecLime1 :=
  Silmaril.Wasm.Component.Lime1Bridge.refToSpec_lime1_of_E (refToSpecE_lime1_of hI hT) hB

end Silmaril.Wasm.Component.Lime1RefE
