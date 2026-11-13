module

public import Silmaril.Wasm.Models.V2CoreInstFn.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstFn.Transport

/-!
# A point with a function in the instantiation domain

`fnPt` holds one Wasm function of type `[] → []` and nothing else, with the closed host.

* `fnPt_dom`: it is in `v20instHT P`'s domain at every profile;
* `storeOk_fnStore`, `hostFree_fnStore`: its store is typed and has no host function;
* `domInstP_of_storeOk`: every typed, host-free point of the domain with the closed host is in
  `domInstP P`, whatever its store holds;
* `domInstP_of_storeOk_any`: the same with any host relation in the domain, since instantiation
  calls no host;
* `domInstP_fnPt`: so, with `importsTransport_all`, it is in `domInstP P` at every profile, and in
  `domInstDet g` at every grow policy;
* `fnPt_importable`: Core types the address `FUNC 0` at the image of `nopType`, and so does 2.0.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstFn

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstImp (domInstP domInstP_of_transport)
open Silmaril.Wasm.Models.V2CoreInstFn (nopType nopModInst nopFunc fnStore fnPt)

theorem fnStore_toCore_isSome : (Store.toCore fnStore).isSome := rfl

/-- `fnPt` is in `v20instHT`'s domain at every profile. -/
theorem fnPt_dom (P : Profile) : (v20instHT P).dom fnPt := by
  refine ⟨⟨⟨fun i fi h => ?_, fun _ _ h => by simp [fnPt, fnStore] at h,
    fun _ _ h => by simp [fnPt, fnStore] at h, fun _ _ h => by simp [fnPt, fnStore] at h⟩,
    fnStore_toCore_isSome,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_preserves,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_keeps⟩, hostEmbV_none, ?_⟩
  · have hfi : fi = nopFunc := by
      have hm : fi ∈ fnStore.funcs := List.mem_of_getElem? h
      simpa [fnStore] using hm
    subst hfi
    intro a ha
    simp [nopFunc, nopModInst] at ha
    simp [ha, fnPt, fnStore]
  · intro fi hfi
    simp [ptCore, fnPt, fnStore, Store.toCore, nopFunc, FuncInst.toCore, Func.toCore,
      Expr.toCore] at hfi
    subst hfi
    simp [ModuleInst.toCore, nopModInst]

/-- `nopModInst` is typed in `fnStore`, at the context with its one type and one function. -/
theorem moduleInstOk_nop :
    ModuleInstOk fnStore nopModInst
      { types := [nopType], funcs := [nopType], globals := [], tables := [], mems := [],
        elems := [], datas := [], refs := [] } :=
  .mk (refs := []) (fun _ _ => trivial) (.cons (.func (fi := nopFunc) rfl) .nil) .nil .nil .nil .nil
    (fun _ h => by simp [nopModInst] at h) (fun _ h => by simp [nopModInst] at h) .nil
    (fun _ h => by simp [nopModInst] at h) (fun _ h => by simp at h)

theorem funcInstOk_nop : FuncInstOk fnStore nopFunc :=
  .wasm trivial moduleInstOk_nop rfl (.mk rfl .empty)

theorem storeOk_fnStore : StoreOk fnStore := by
  constructor <;> simp [fnStore]
  exact funcInstOk_nop

theorem hostFree_fnStore : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree fnStore := by
  intro fi hfi h
  simp [fnStore] at hfi
  subst hfi
  simp [nopFunc]

/-- **Every typed, host-free point of `v20instHT P`'s domain with the closed host is in
`domInstP P`**: import typing transports everywhere (`importsTransport_all`). -/
theorem domInstP_of_storeOk {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hc : p.2 = closedV) (hs : StoreOk p.1)
    (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) : domInstP P p :=
  domInstP_of_transport hd hc hs hfree (importsTransport_all hd.1.2.1)

/-- **Every typed, host-free point of `v20instHT P`'s domain is in `domInstP P`, whatever its
host relation.** Instantiation calls no host (`instantiate_imports` holds at every host), and
`domInstP` reads behaviours at the closed host, so the point's own host plays no part. -/
theorem domInstP_of_storeOk_any {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hs : StoreOk p.1) (hfree : Silmaril.Proofs.Wasm.Models.V2Sound.HostFree p.1) :
    domInstP P p := by
  refine ⟨hd, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  obtain ⟨ixt, xt, hm⟩ := hval
  have hx : List.Forall₂ (ExternAddrOk p.1) xas ixt :=
    importsTransport_all hd.1.2.1 m cm xas ixt xt xtI xtE hm hcm hok hxas
  obtain ⟨c, hinst, hfree'⟩ := Silmaril.Wasm.Models.V2CoreInstImp.instantiate_imports P hs hfree hm hx
    (Silmaril.Proofs.Wasm.Models.V2CoreInstDom.segBounded_of_core hcm hC.bounded)
  obtain ⟨hok', -⟩ := Instantiate.ok Silmaril.Proofs.Wasm.Models.V2Sound.hostOk_divV hs
    (hinst Silmaril.Proofs.Wasm.Models.V2Sound.divV)
  exact ⟨c, hinst p.2, Silmaril.Proofs.Wasm.Models.V2Sound.behavioursOf_nonempty_of_safe
    fun _ hsteps => (Silmaril.Proofs.Wasm.Models.V2Sound.closed_safe hfree' hok' hsteps).2.2⟩

/-- **`fnPt` is in `domInstP P`**, at every profile. -/
theorem domInstP_fnPt (P : Profile) : domInstP P fnPt :=
  domInstP_of_transport (fnPt_dom P) rfl storeOk_fnStore hostFree_fnStore
    (importsTransport_all fnStore_toCore_isSome)

/-- **`fnPt` is in `domInstDet g`**, at every grow policy. -/
theorem domInstDet_fnPt (g : GrowKind → Nat → Nat → Nat → Bool) :
    V2CoreInstDet.domInstDet g fnPt :=
  domInstP_fnPt _

/-- **`fnPt` has a function to import**: Core types `FUNC 0` at the image of `nopType`, and 2.0
types it at `nopType`. -/
theorem fnPt_importable :
    Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore fnPt).1 (.func 0)
        (ExternType.toCore (.func nopType)) ∧
      ExternAddrOk fnPt.1 (.func 0) (.func nopType) :=
  by
    obtain ⟨cfi, hc, ht⟩ : ∃ cfi : Silmaril.Wasm.Execution.Core.FuncInst Nat,
        (ptCore fnPt).1.funcs[0]? = some cfi ∧ cfi.type = nopType.toDefType :=
      ⟨_, rfl, rfl⟩
    refine ⟨?_, .func (fi := nopFunc) rfl⟩
    have h := Silmaril.Wasm.Execution.Core.ExternAddrOk.func hc
    rw [ht] at h
    exact h

/-! ## A point with a host that is not closed -/

/-- `fnStore` with `divV`, the host whose calls all diverge. -/
def fnDivPt : Pt Nat := (fnStore, Silmaril.Proofs.Wasm.Models.V2Sound.divV)

theorem divV_preserves :
    HostPreserves (Silmaril.Proofs.Wasm.Models.V2Sound.divV (H := Nat)) := by
  intro h s vs s' r hh
  cases hh

theorem divV_keeps : HostKeepsV (Silmaril.Proofs.Wasm.Models.V2Sound.divV (H := Nat)) := by
  intro h s vs s' r hh
  cases hh

theorem divV_blind : GlobalsBlindV (Silmaril.Proofs.Wasm.Models.V2Sound.divV (H := Nat)) :=
  ⟨fun _ _ _ _ _ hh => (by cases hh), fun _ _ _ _ _ _ _ hh => (by cases hh),
    fun _ _ _ _ _ _ => rfl⟩

/-- `fnDivPt` is in `v20instHT`'s domain at every profile. -/
theorem fnDivPt_dom (P : Profile) : (v20instHT P).dom fnDivPt :=
  ⟨⟨(fnPt_dom P).1.1, fnStore_toCore_isSome, divV_preserves, divV_keeps⟩,
    hostEmbV_blind divV_blind, (fnPt_dom P).2.2⟩

/-- **`fnDivPt`, a store with a function and a host that is not the closed host, is in
`domInstP P`** at every profile. -/
theorem domInstP_fnDivPt (P : Profile) : domInstP P fnDivPt :=
  domInstP_of_storeOk_any (fnDivPt_dom P) storeOk_fnStore hostFree_fnStore

end Silmaril.Proofs.Wasm.Models.V2CoreInstFn
