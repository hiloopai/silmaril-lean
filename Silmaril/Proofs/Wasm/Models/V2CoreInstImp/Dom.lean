module

public import Silmaril.Wasm.Models.V2CoreInstImp.Defs
public import Silmaril.Proofs.Wasm.Models.V2CoreInstImp.Transport

/-!
# The instantiation domain with imports, at every profile

* `domInstP_of_transport`: a point of `v20instHT P`'s domain with the closed host, a typed and
  host-free store, at which Core import typing transports back to 2.0 (`ImportsTransport`), is
  in `domInstP P`. The proof is `instantiate_imports` (2.0 progress with imports) and 2.0 type
  soundness with the closed host.
* `importsTransport_noF`: `ImportsTransport` holds at every point whose store has no function,
  through `import_transport_noF`.
* The points: `emptyPt`, `dataPt` and `impPt` are in `domInstP P` at **every** profile `P`.
  At `impPt` a module may import a memory, an immutable `i32` global and a `funcref` table, and
  read the global in its initialisers; Core instantiates such modules there, and so does 2.0.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstImp

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstImp (domInstP ImportsTransport NoFuncs impStore impPt)
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree divV hostOk_divV closed_safe
  behavioursOf_nonempty_of_safe)
open Silmaril.Proofs.Wasm.Models.V2CoreInstDom (imports_of_toCore segBounded_of_core)

/-- `domInstDet g` is `domInstP` at the deterministic profile. -/
theorem domInstDet_iff (g : GrowKind → Nat → Nat → Nat → Bool) (p : Pt Nat) :
    V2CoreInstDet.domInstDet g p ↔ domInstP (Profile.deterministic g) p :=
  Iff.rfl

/-- **A point at which import typing transports is in `domInstP P`**, at every profile. -/
theorem domInstP_of_transport {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hc : p.2 = closedV) (hs : StoreOk p.1) (hfree : HostFree p.1) (ht : ImportsTransport p) :
    domInstP P p := by
  refine ⟨hd, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  obtain ⟨ixt, xt, hm⟩ := hval
  have hx : List.Forall₂ (ExternAddrOk p.1) xas ixt := ht m cm xas ixt xt xtI xtE hm hcm hok hxas
  obtain ⟨c, hinst, hfree'⟩ :=
    instantiate_imports P hs hfree hm hx (segBounded_of_core hcm hC.bounded)
  have hrun : Instantiate P p.2 p.1 m xas c := hinst p.2
  rw [hc] at hrun
  obtain ⟨hok', -⟩ := Instantiate.ok hostOk_divV hs (hinst divV)
  exact ⟨c, hc ▸ hrun, behavioursOf_nonempty_of_safe fun _ hsteps =>
    (closed_safe hfree' hok' hsteps).2.2⟩

/-- **Import typing transports at every point whose store has no function.** -/
theorem importsTransport_noF {p : Pt Nat} (hd : (Store.toCore p.1).isSome)
    (hf : NoFuncs p.1) : ImportsTransport p := by
  intro m cm xas ixt xt xtI xtE hm hcm hcok hxas
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hd
  have hp : (ptCore p).1 = cs := by simp [ptCore, hcs]
  rw [hp] at hxas
  cases hm with
  | mk _ himports =>
    cases hcok with
    | mk _ himportsC =>
      rw [imports_of_toCore hcm] at himportsC
      refine forall₂_combine (f := Import.toCore) (g := ExternAddr.toCore) ?_
        himports himportsC hxas
      intro _ _ _ _ h₂ hc ha
      exact import_transport_noF hcs hf h₂ hc ha

/-! ## The points -/

theorem domInstP_emptyPt (P : Profile) : domInstP P V2CoreInstDom.emptyPt :=
  domInstP_of_transport (V2CoreInstDom.emptyPt_dom P) rfl V2CoreInstDom.storeOk_empty
    (fun _ h => by simp [V2CoreInstDom.emptyPt] at h) (importsTransport_noF rfl rfl)

theorem domInstP_dataPt (P : Profile) : domInstP P V2CoreInstData.dataPt :=
  domInstP_of_transport (V2CoreInstData.dataPt_dom P) rfl V2CoreInstData.storeOk_dataStore
    V2CoreInstData.hostFree_dataStore (importsTransport_noF rfl rfl)

theorem impStore_mem {i : Nat} {mi : MemInst} (h : impStore.mems[i]? = some mi) :
    mi = { type := ⟨⟨0, none⟩⟩, bytes := ByteArray.empty } := by
  have hm : mi ∈ impStore.mems := List.mem_of_getElem? h
  simpa [impStore] using hm

theorem impStore_table {i : Nat} {ti : TableInst} (h : impStore.tables[i]? = some ti) :
    ti = { type := ⟨⟨0, none⟩, .funcref⟩, refs := [] } := by
  have hm : ti ∈ impStore.tables := List.mem_of_getElem? h
  simpa [impStore] using hm

/-- `impPt` is in `v20instHT`'s domain at every profile. -/
theorem impPt_dom (P : Profile) : (v20instHT P).dom impPt := by
  refine ⟨⟨⟨fun _ _ h => by simp [impPt, impStore] at h, fun _ _ h => ?_, fun _ _ h => ?_,
    fun _ _ h => ?_⟩, rfl,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_preserves,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_keeps⟩, hostEmbV_none, ?_⟩
  · rw [impStore_mem h]; decide
  · rw [impStore_mem h]; decide
  · rw [impStore_table h]; decide
  · intro fi hfi
    have e : (ptCore impPt).1.funcs = [] := rfl
    rw [e] at hfi
    simp at hfi

theorem storeOk_impStore : StoreOk impStore := by
  constructor <;> simp [impStore, MemInstOk, GlobalInstOk, TableInstOk]
  · exact ⟨by decide, .num _⟩
  · decide
  · decide

theorem hostFree_impStore : HostFree impStore := fun _ h => by simp [impStore] at h

/-- **`impPt` is in `domInstP P`**, at every profile. -/
theorem domInstP_impPt (P : Profile) : domInstP P impPt :=
  domInstP_of_transport (impPt_dom P) rfl storeOk_impStore hostFree_impStore
    (importsTransport_noF rfl rfl)

end Silmaril.Proofs.Wasm.Models.V2CoreInstImp
