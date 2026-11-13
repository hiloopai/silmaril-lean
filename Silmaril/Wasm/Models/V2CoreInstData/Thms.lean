module

public import Silmaril.Wasm.Models.V2CoreInstDom.Thms
public import Silmaril.Proofs.Wasm.Models.V2CoreInstData.Main

/-!
# The deterministic instantiation domain at a non-empty store

`V2CoreInstDom` put the empty 2.0 store in `domInstDet g`. Here:

* **`instantiate_noImports`**: a valid 2.0 module without imports instantiates in every 2.0
  store, under every host and at every profile (given `$instantiate`'s segment bounds); the
  store it starts from is host-free when the given one is. This generalises
  `V2CoreInstDom.instantiate_empty` from the empty store.
* **`domInstDet_dataPt`**: the store with one empty data segment and the closed host is in
  `domInstDet g` at every grow policy; `domInstDet_nonempty_store` packages it as a point with a
  non-empty store.

The point holds nothing importable (no function, table, memory or global), so Core instantiates
only import-free modules there. Points at which a module **imports** something are still open:
they need Core's import typing at image addresses (`ExternAddrOk`, deftype matching) to transfer
back to 2.0's `ExternTypeOk`, and 2.0 instantiation progress with imported globals in the
initialisers.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstData

open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreInstDet

/-- **A valid import-free 2.0 module instantiates in every store**, under every host, at every
profile, given the segment bounds `$instantiate` assumes. -/
theorem instantiate_noImports {H : Type} (P : Profile) {m : Silmaril.Wasm.V2.Module}
    {xt : List Silmaril.Wasm.V2.ExternType} (hm : Silmaril.Wasm.V2.Validation.ModuleOk m [] xt)
    (hb : Silmaril.Proofs.Wasm.Models.V2CoreInstDom.SegBounded m)
    (s : Silmaril.Wasm.V2.Execution.Store H) (hs : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree s) :
    ∃ c : Silmaril.Wasm.V2.Execution.Config H,
      (∀ host, Silmaril.Wasm.V2.Execution.Instantiate P host s m [] c) ∧
        Silmaril.Proofs.Wasm.Models.V2Sound.HostFree c.store :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstData.instantiate_noImports P hm hb s hs

/-- The 2.0 store with one empty data segment, with the closed host. -/
abbrev dataPt : Pt Nat := Silmaril.Proofs.Wasm.Models.V2CoreInstData.dataPt

/-- **`dataPt` is in `domInstDet g`.** -/
theorem domInstDet_dataPt (g : GrowKind → Nat → Nat → Nat → Bool) : domInstDet g dataPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstData.domInstDet_dataPt g

/-- **`domInstDet g` has a point with a non-empty store.** -/
theorem domInstDet_nonempty_store (g : GrowKind → Nat → Nat → Nat → Bool) :
    ∃ p : Pt Nat, domInstDet g p ∧ p.1.datas ≠ [] :=
  ⟨dataPt, domInstDet_dataPt g, Silmaril.Proofs.Wasm.Models.V2CoreInstData.dataStore_ne_empty⟩

/-! The axiom audit. -/

/--
info: 'Silmaril.Wasm.Models.V2CoreInstData.instantiate_noImports' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms instantiate_noImports

/--
info: 'Silmaril.Wasm.Models.V2CoreInstData.domInstDet_nonempty_store' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms domInstDet_nonempty_store

end Silmaril.Wasm.Models.V2CoreInstData
