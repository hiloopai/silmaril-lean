module

public import Silmaril.Wasm.Component.Lime1RefE.Thms
public import Silmaril.Wasm.Component.Lime1Inst.Thms

/-!
# `RefToSpec lime1G` from the two open Lime1 engine facts

Joins the two pass-2 lime results: `Lime1RefE.refToSpecE_lime1_of` reduces the machine half
`Lime1Ref.RefToSpecELime1` to `Lime1RefE.Lime1InstOk` and `Lime1RefE.Lime1TypedOk`,
and `Lime1Inst.instBridgeE` proves the store-level bridge `Lime1Bridge.InstBridgeE`.

* `refToSpec_lime1_of_engine` (proved): **`Lime1Ref.RefToSpecLime1` follows from
  `Lime1InstOk` and `Lime1TypedOk` alone.**

New statement; no new proof content.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RefAll

/-- **The corrected `RefToSpec lime1G` from the two open Lime1 engine facts.** -/
theorem refToSpec_lime1_of_engine (hI : Lime1RefE.Lime1InstOk)
    (hT : Lime1RefE.Lime1TypedOk) : Lime1Ref.RefToSpecLime1 :=
  Lime1RefE.refToSpec_lime1_of_E' hI hT Lime1Inst.instBridgeE

/-- info: 'Silmaril.Wasm.Component.Lime1RefAll.refToSpec_lime1_of_engine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refToSpec_lime1_of_engine

end Silmaril.Wasm.Component.Lime1RefAll
