module

public import Silmaril.Wasm.Models.V2CoreInstFn.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstFn.Point

/-!
# The instantiation domain at stores with functions

An earlier step transported Core's import typing back to 2.0 for memories, globals and tables,
so only at stores without functions (`V2CoreInstImp.importsTransport_noF`). Here:

* **Function imports** (`funcImport_transport`): if Core types the image of a function address
  at the image of a 2.0 function type, 2.0 types the address at that type. Core's chain of
  `Externtype_sub` steps collapses to one defined-type `Sub` from the instance's type; the
  instance's type is the image of its 2.0 type (`Store.toCore` maps every function instance);
  and between images of 2.0 function types Core's defined-type subtyping is 2.0's equality
  (silmaril-lean's `FuncType.toDefType_sub_iff`: the image is a final, parent-free singleton
  group).
* **Every import, every store** (`importsTransport_all`): `ImportsTransport p` holds at every point
  whose store has a Core image. Core's import types of a module image are the images of the
  module's 2.0 import types.
* **The domain**: every typed, host-free point of `v20instHT P`'s domain with the closed host is
  in `domInstP P` (`domInstP_of_storeOk`), at every profile. `fnPt`, a store with one Wasm
  function of type `[] → []`, is such a point (`domInstP_fnPt`, `domInstDet_fnPt`), and its
  function is importable in both semantics (`fnPt_importable`).

* **Any host in the domain** (`domInstP_of_storeOk_any`): instantiation calls no host
  (`instantiate_imports` holds at every host) and `domInstP` reads behaviours at the closed host,
  so the closed-host condition of `domInstP_of_transport` is not needed. `fnDivPt`, `fnStore`
  with `divV` (every host call diverges), is in `domInstP P` (`domInstP_fnDivPt`).

**Not covered.** Host functions in the store (`HostFree`), and stores at types other than
`Nat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstFn

open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstImp (domInstP ImportsTransport)

/-- **Core's typing of an image function address transports back to 2.0.** -/
theorem funcImport_transport {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Silmaril.Wasm.V2.Execution.Store.toCore s = some cs) {a : Nat}
    {ft : Silmaril.Wasm.V2.FuncType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.func a) (.func ft.toDefType)) :
    Silmaril.Wasm.V2.Execution.ExternAddrOk s (.func a) (.func ft) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.funcImport_transport hcs h

/-- **Core's typing of an image address at the image of a 2.0 external type is 2.0's.** -/
theorem addr_transport {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Silmaril.Wasm.V2.Execution.Store.toCore s = some cs)
    {xa : Silmaril.Wasm.V2.Execution.ExternAddr} {it : Silmaril.Wasm.V2.ExternType}
    (hok : Silmaril.Wasm.V2.ExternType.Ok it)
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa.toCore it.toCore) :
    Silmaril.Wasm.V2.Execution.ExternAddrOk s xa it :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.addr_transport hcs hok h

/-- **Import typing transports at every point whose store has a Core image.** -/
theorem importsTransport_all {p : Pt Nat}
    (hd : (Silmaril.Wasm.V2.Execution.Store.toCore p.1).isSome) : ImportsTransport p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.importsTransport_all hd

/-- **Every typed, host-free point of the domain with the closed host is in `domInstP P`.** -/
theorem domInstP_of_storeOk {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hc : p.2 = closedV) (hs : Silmaril.Wasm.V2.Execution.StoreOk p.1)
    (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) : domInstP P p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.domInstP_of_storeOk hd hc hs hfree

/-- **Every typed, host-free point of the domain is in `domInstP P`, at any host.** -/
theorem domInstP_of_storeOk_any {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hs : Silmaril.Wasm.V2.Execution.StoreOk p.1)
    (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) : domInstP P p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.domInstP_of_storeOk_any hd hs hfree

/-- **`fnDivPt` (a function, and a host whose calls diverge) is in `domInstP P`.** -/
theorem domInstP_fnDivPt (P : Profile) :
    domInstP P Silmaril.Proofs.Wasm.Models.V2CoreInstFn.fnDivPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.domInstP_fnDivPt P

/-- **`fnPt` is in `domInstP P`** at every profile. -/
theorem domInstP_fnPt (P : Profile) : domInstP P fnPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.domInstP_fnPt P

/-- **`fnPt` is in `domInstDet g`** at every grow policy. -/
theorem domInstDet_fnPt (g : GrowKind → Nat → Nat → Nat → Bool) :
    V2CoreInstDet.domInstDet g fnPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.domInstDet_fnPt g

/-- **`fnPt` has a function to import**, in Core and in 2.0. -/
theorem fnPt_importable :
    Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore fnPt).1 (.func 0)
        (Silmaril.Wasm.V2.ExternType.toCore (.func nopType)) ∧
      Silmaril.Wasm.V2.Execution.ExternAddrOk fnPt.1 (.func 0) (.func nopType) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstFn.fnPt_importable

/-! The axiom audit. -/

/-- info: 'Silmaril.Wasm.Models.V2CoreInstFn.importsTransport_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms importsTransport_all

/-- info: 'Silmaril.Wasm.Models.V2CoreInstFn.domInstP_of_storeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstP_of_storeOk

/-- info: 'Silmaril.Wasm.Models.V2CoreInstFn.domInstP_fnDivPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstP_fnDivPt

/-- info: 'Silmaril.Wasm.Models.V2CoreInstFn.domInstDet_fnPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstDet_fnPt

end Silmaril.Wasm.Models.V2CoreInstFn
