module

public import Silmaril.Wasm.Wac.Bridge.DecodeItemsR.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeItemsR

/-!
# WAC bridge: WIT packages of several items over `EsOkR`

* `decodePkg_itemsPackageR`: for items of `EsOkR` (`okR`), the wrappers succeed,
  and `decodePkg` reads the binary of the package back as `itemsPkgR items`: each
  interface as `.inst (some id) (dks (rdEs [] es))`, each world as
  `.comp (some id) (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es))`;
* `decodePkg_ifacePackageR`: the WIT interface package of one interface.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeRefVal (EsOkR rdEs)
open DecodeItems (PItem itemDef itemsDefs project_itemsPackage)

namespace DecodeItemsR

/-- **The byte level for WIT packages of several items** of `EsOkR`. -/
theorem decodePkg_itemsPackageR {N : NomTable} {items : List (String × PItem)}
    (h : ∀ p ∈ items, okR N p.2) (cs : List Section) (hc : ∀ c ∈ cs, Wit.Project.isCode c = true) :
    ∃ defs, itemsDefs N items = .ok defs ∧
      ∀ b, Component.Binary.encode (Wit.Project.itemsPackage defs cs) = some b →
        ∃ nt, decodePkg b = .ok (itemsPkgR items, nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨defs, hdefs, hres, δ', hdec, hn⟩ :=
    items_decR items 0 {} [] h rfl (fun _ hp => absurd hp (by simp))
  refine ⟨defs, hdefs, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.itemsPackage defs cs) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (project_itemsPackage defs cs hres hc)
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, hw]
  exact pkgOfWorld_itemsR hdec

/-- **A WIT interface package** of the fragment `EsOkR`. -/
theorem decodePkg_ifacePackageR {N : NomTable} {id name : String} {es : Externs} (h : EsOkR N [] es) :
    ∃ t, itemDef N (.iface id es) = .ok t ∧
      ∀ b, Component.Binary.encode (Wit.Project.itemsPackage [(name, t)] []) = some b →
        ∃ nt, decodePkg b =
            .ok ({ defs := [(defName name, .type (.inst (some id) (DecodeNamed.dks (rdEs [] es))))] }, nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨defs, hdefs, hb⟩ := decodePkg_itemsPackageR (N := N) (items := [(name, .iface id es)])
    (fun p hp => by rw [List.mem_singleton.1 hp]; exact h) [] (fun _ hc => absurd hc (by simp))
  cases ht : itemDef N (.iface id es) with
  | error e => simp [itemsDefs, ht] at hdefs
  | ok t =>
    have e : defs = [(name, t)] := by simp [itemsDefs, ht] at hdefs; exact hdefs.symm
    subst e
    exact ⟨t, rfl, hb⟩

end DecodeItemsR

end Silmaril.Wasm.Wac.Bridge
