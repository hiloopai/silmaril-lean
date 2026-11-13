module

public import Silmaril.Wasm.Models.V2CoreInstImp.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstImp.Dom

/-!
# The instantiation domain with imports, at every profile

An earlier step put two points without anything importable in `domInstDet g` (`emptyPt`,
`dataPt`). Here:

* **2.0 instantiation progress with imports** (`instantiate_imports`): a valid 2.0 module
  instantiates in every typed store whose addresses match its imports (2.0's `ExternAddrOk`),
  under every host and at every profile. The initialisers may read imported globals and imported
  functions.
* **Core import typing back to 2.0, at memories, globals and tables** (`memImport_transport`,
  `globalImport_transport`, `tableImport_transport`): if Core types the image of a memory, global
  or table address at the image of a 2.0 type, 2.0 types the address at that type. Core's chains
  of `Externtype_sub` steps collapse (`ExternSub.trans`); between images of 2.0 value and
  reference types Core's subtyping is equality (`V2Core.Reflect.toC_sub_toC`, `refToC_sub'`).
* **At stores with no function** (`importsTransport_noF`), this transports the whole import
  list. Such a point with the closed host, a typed host-free store and `v20instHT P`'s
  domain is in `domInstP P` (`domInstP_of_transport`).
* **Points**: `emptyPt`, `dataPt` and `impPt` (an importable memory, immutable `i32` global and
  `funcref` table) are in `domInstP P` at every profile `P`. At the deterministic profiles
  `domInstP` is `domInstDet` (`domInstDet_iff`), so `impPt` is a point of `domInstDet g` at which
  modules import a memory, a global and a table (`domInstDet_impPt`, `impPt_importable`).

**Not covered.** Points whose stores hold functions. Their import typing needs Core's subtyping
between the defined types of 2.0 function types (and the store's function instances to be
images) to transport back to 2.0's equality of function types.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstImp

open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec

/-- **2.0 instantiation progress with imports.** -/
theorem instantiate_imports {H : Type} (P : Profile) {s : Silmaril.Wasm.V2.Execution.Store H}
    (hs : Silmaril.Wasm.V2.Execution.StoreOk s) (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree s)
    {m : Silmaril.Wasm.V2.Module} {ixt xt : List Silmaril.Wasm.V2.ExternType}
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    (hm : Silmaril.Wasm.V2.Validation.ModuleOk m ixt xt)
    (hx : List.Forall₂ (Silmaril.Wasm.V2.Execution.ExternAddrOk s) xas ixt)
    (hb : Silmaril.Proofs.Wasm.Models.V2CoreInstDom.SegBounded m) :
    ∃ c : Silmaril.Wasm.V2.Execution.Config H,
      (∀ host, Silmaril.Wasm.V2.Execution.Instantiate P host s m xas c) ∧
        Silmaril.Proofs.Wasm.Models.V2Sound.HostFree c.store :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.instantiate_imports P hs hfree hm hx hb

/-- **Core's typing of an image global address transports back to 2.0.** -/
theorem globalImport_transport {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Silmaril.Wasm.V2.Execution.Store.toCore s = some cs) {a : Nat}
    {g : Silmaril.Wasm.V2.GlobalType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.global a)
      (.global (Silmaril.Wasm.V2.Execution.ToCore.globalToC g))) :
    Silmaril.Wasm.V2.Execution.ExternAddrOk s (.global a) (.global g) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.globalImport_transport hcs h

/-- **Core's typing of an image memory address transports back to 2.0.** -/
theorem memImport_transport {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Silmaril.Wasm.V2.Execution.Store.toCore s = some cs) {a : Nat}
    {mt : Silmaril.Wasm.V2.MemoryType} (hok : Silmaril.Wasm.V2.ExternType.Ok (.memory mt))
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.mem a) (.mem mt.toCore)) :
    Silmaril.Wasm.V2.Execution.ExternAddrOk s (.mem a) (.memory mt) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.memImport_transport hcs hok h

/-- **Import typing transports at every point whose store has no function.** -/
theorem importsTransport_noF {p : Pt Nat}
    (hd : (Silmaril.Wasm.V2.Execution.Store.toCore p.1).isSome) (hf : NoFuncs p.1) :
    ImportsTransport p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.importsTransport_noF hd hf

/-- **Core's typing of an image table address transports back to 2.0.** -/
theorem tableImport_transport {H : Type} {s : Silmaril.Wasm.V2.Execution.Store H}
    {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Silmaril.Wasm.V2.Execution.Store.toCore s = some cs) {a : Nat}
    {t : Silmaril.Wasm.V2.TableType} (hok : Silmaril.Wasm.V2.ExternType.Ok (.table t))
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.table a)
      (.table (Silmaril.Wasm.V2.Execution.ToCore.tableToC t))) :
    Silmaril.Wasm.V2.Execution.ExternAddrOk s (.table a) (.table t) :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.tableImport_transport hcs hok h

/-- **A point at which import typing transports is in `domInstP P`.** -/
theorem domInstP_of_transport {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hc : p.2 = closedV) (hs : Silmaril.Wasm.V2.Execution.StoreOk p.1)
    (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) (ht : ImportsTransport p) :
    domInstP P p :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.domInstP_of_transport hd hc hs hfree ht

/-- `domInstDet g` is `domInstP` at the deterministic profile. -/
theorem domInstDet_iff (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) :
    V2CoreInstDet.domInstDet g p ↔ domInstP (Profile.deterministic g) p :=
  Iff.rfl

/-- **The empty point is in `domInstP P` at every profile.** -/
theorem domInstP_emptyPt (P : Profile) : domInstP P Silmaril.Proofs.Wasm.Models.V2CoreInstDom.emptyPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.domInstP_emptyPt P

/-- **The data point is in `domInstP P` at every profile.** -/
theorem domInstP_dataPt (P : Profile) : domInstP P V2CoreInstData.dataPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.domInstP_dataPt P

/-- **The import point is in `domInstP P` at every profile.** -/
theorem domInstP_impPt (P : Profile) : domInstP P impPt :=
  Silmaril.Proofs.Wasm.Models.V2CoreInstImp.domInstP_impPt P

/-- **`impPt` is in `domInstDet g`** at every grow policy. -/
theorem domInstDet_impPt (g : GrowKind → Nat → Nat → Nat → Bool) :
    V2CoreInstDet.domInstDet g impPt :=
  (domInstDet_iff g impPt).2 (domInstP_impPt _)

/-- **`impPt` has a memory, a global and a table to import**: Core types the three addresses, and
so does 2.0. -/
theorem impPt_importable :
    (∃ xt, Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore impPt).1 (.mem 0) xt) ∧
      (∃ xt, Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore impPt).1 (.global 0) xt) ∧
      (∃ xt, Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore impPt).1 (.table 0) xt) ∧
      (∃ xt, Silmaril.Wasm.V2.Execution.ExternAddrOk impPt.1 (.mem 0) xt) ∧
      (∃ xt, Silmaril.Wasm.V2.Execution.ExternAddrOk impPt.1 (.global 0) xt) ∧
      ∃ xt, Silmaril.Wasm.V2.Execution.ExternAddrOk impPt.1 (.table 0) xt :=
  ⟨⟨_, .mem rfl⟩, ⟨_, .global rfl⟩, ⟨_, .table rfl⟩, ⟨_, .mem rfl⟩, ⟨_, .global rfl⟩,
    ⟨_, .table rfl⟩⟩

/-! The axiom audit. -/

/-- info: 'Silmaril.Wasm.Models.V2CoreInstImp.instantiate_imports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms instantiate_imports

/-- info: 'Silmaril.Wasm.Models.V2CoreInstImp.domInstP_impPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstP_impPt

/-- info: 'Silmaril.Wasm.Models.V2CoreInstImp.domInstDet_impPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domInstDet_impPt

end Silmaril.Wasm.Models.V2CoreInstImp
