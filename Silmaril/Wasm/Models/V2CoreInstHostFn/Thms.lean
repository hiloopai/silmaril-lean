module

public import Silmaril.Wasm.Models.V2CoreInstHostFn.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.Main

/-!
# Instantiation into stores with host functions, and into stores of any host type

Proofs in `Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.Main`. See `docs/projects/spectec/README.md`,
"v10-inst".

* **`instantiate_behaviours`**: at every host type `H`, every typed 2.0 store (host functions
  allowed), every host satisfying 2.0's `HostOk` and every profile, a valid module whose imports
  are typed instantiates with a behaviour under that host. the earlier `instantiate_imports`
  assumed `HostFree`, and the domain theorems fixed `Store Nat`.
* **`domInstHost_of_storeOk`**: every typed point of `v20instHT P`'s domain with a well-behaved
  host is in `domInstHost P`, the domain with behaviours read at the point's own host.
* **`domInstHost_hostDivPt`**: a store with a host function (`not_hostFree_hostFnStore`) under
  `divV` is such a point.

Still at `Pt Nat`: the models `v20instHT` and `domInstP`/`domInstHost`, which are defined over
`Store Nat`; only the instantiation statement is generic in `H`.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstHostFn

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec

/-- **2.0 instantiation with a behaviour at every host type and every well-behaved host.** -/
theorem instantiate_behaviours {H : Type} (P : Profile)
    {s : Silmaril.Wasm.V2.Execution.Store H} (hs : Silmaril.Wasm.V2.Execution.StoreOk s)
    {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
    (hh : Silmaril.Wasm.V2.Execution.HostOk host)
    {m : Silmaril.Wasm.V2.Module} {ixt xt : List Silmaril.Wasm.V2.ExternType}
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    (hm : Silmaril.Wasm.V2.Validation.ModuleOk m ixt xt)
    (hx : List.Forall₂ (Silmaril.Wasm.V2.Execution.ExternAddrOk s) xas ixt)
    (hb : Silmaril.Proofs.Wasm.Models.V2CoreInstDom.SegBounded m) :
    ∃ c : Silmaril.Wasm.V2.Execution.Config H,
      Silmaril.Wasm.V2.Execution.Instantiate P host s m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf P host c).Nonempty :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.instantiate_behaviours P hs hh hm hx hb

/-- **Typed points with a well-behaved host are in `domInstHost P`.** -/
theorem domInstHost_of_storeOk {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hs : Silmaril.Wasm.V2.Execution.StoreOk p.1) (hh : Silmaril.Wasm.V2.Execution.HostOk p.2) :
    domInstHost P p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.domInstHost_of_storeOk hd hs hh

/-- **A store with a host function is in `domInstHost P`.** -/
theorem domInstHost_hostDivPt (P : Profile) : domInstHost P hostDivPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.domInstHost_hostDivPt P

/-- It is not host-free. -/
theorem not_hostFree_hostFnStore : ¬ Silmaril.Proofs.Wasm.Models.V2Sound.HostFree hostFnStore :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn.not_hostFree_hostFnStore

/-- info: 'Silmaril.Wasm.Models.V2CoreInstHostFn.instantiate_behaviours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms instantiate_behaviours

/-- info: 'Silmaril.Wasm.Models.V2CoreInstHostFn.domInstHost_of_storeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstHost_of_storeOk

/-- info: 'Silmaril.Wasm.Models.V2CoreInstHostFn.domInstHost_hostDivPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstHost_hostDivPt

end Silmaril.Wasm.Models.V2CoreInstHostFn
