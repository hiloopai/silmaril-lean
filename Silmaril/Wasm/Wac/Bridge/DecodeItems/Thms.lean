module

public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeItems

/-!
# WAC bridge: `decodePkg` on WIT packages of several items

`Bridge.DecodeNamed.decodePkg_world` proves the byte level of `decodePkg` for the WIT
package of one world. This module proves it for WIT packages in general
(`Wit.Project.itemsPackage`, wit-component's layout): any number of interfaces and
worlds of the named fragment, followed by custom sections.

* `ifaceDef_run`, `worldDef_run`: the wrapper component type of an item (`itemDef`) is
  the one type definition the encoder's `ifaceDef` and `worldDef` write;
* `decodePkg_itemsPackage`: **the byte level**: if `b` is the binary
  (`Component.Binary.encode`) of the package of the items' wrapper component types and
  custom sections `cs`, then `decodePkg b` returns the package whose definitions are the
  items (`itemsPkg`): an interface `iface id es` as `.inst (some id) (dks es)`, a world
  as `.comp (some id) (dks is) (dks es)`, under the name after `/` (`defName`); the
  nominal definitions it records come from `N`;
* `decodePkg_ifacePackage`: the case of one interface (a WIT interface package).

The proofs are in `Silmaril/Proofs/Wasm/Wac/Bridge/DecodeItems.lean`; they go through
`Component.Binary.parse` (`parse_encode`), `Wit.Project.projectI` (`projectI_of_project`,
`replay_itemSecs`) and the item simulations of `Bridge.DecodeNamed` (`inst_type`, a
component type in either sharing mode `comp_type_b`).

**Not covered**: interfaces that `use` types of other interfaces of the package (the
encoder writes every interface closed), and component (implementation) binaries.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

namespace DecodeItems

/-- **The byte level for WIT packages of several items.** -/
theorem decodePkg_itemsPackage {N : NomTable} {items : List (String × PItem)}
    (h : ∀ p ∈ items, p.2.Ok N) (cs : List Section) (hc : ∀ c ∈ cs, Wit.Project.isCode c = true) :
    ∃ defs, itemsDefs N items = .ok defs ∧
      ∀ b, Component.Binary.encode (Wit.Project.itemsPackage defs cs) = some b →
        ∃ nt, decodePkg b = .ok (itemsPkg items, nt) ∧ ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨defs, hdefs, hres, δ', hdec, hn⟩ :=
    items_dec items 0 {} [] h rfl (fun _ hp => absurd hp (by simp))
  refine ⟨defs, hdefs, fun b hb => ⟨δ'.nom, ?_, hn⟩⟩
  have hp : Component.Binary.parse b = .ok (Wit.Project.itemsPackage defs cs) :=
    Component.Binary.parse_encode hb
  have hw := Wit.Project.projectI_of_project (project_itemsPackage defs cs hres hc)
  simp only [decodePkg, hp, DecodeEnc.pure_ok, DecodeEnc.ok_bind, hw]
  exact pkgOfWorld_items hdec

/-- **A WIT interface package**: the binary of the package of one interface of the
fragment is read back as that interface. -/
theorem decodePkg_ifacePackage {N : NomTable} {id name : String} {es : Externs}
    (h : DecodeNamed.EsOk N [] es) :
    ∃ t, itemDef N (.iface id es) = .ok t ∧
      ∀ b, Component.Binary.encode (Wit.Project.itemsPackage [(name, t)] []) = some b →
        ∃ nt, decodePkg b = .ok ({ defs := [(defName name, .type (.inst (some id) (DecodeNamed.dks es)))] }, nt) ∧
          ∀ p ∈ nt, N.lookup p.1 = some p.2 := by
  obtain ⟨defs, hdefs, hb⟩ := decodePkg_itemsPackage (N := N) (items := [(name, .iface id es)])
    (fun p hp => by rw [List.mem_singleton.1 hp]; exact h) [] (fun _ hc => absurd hc (by simp))
  cases ht : itemDef N (.iface id es) with
  | error e => simp [itemsDefs, ht] at hdefs
  | ok t =>
    have e : defs = [(name, t)] := by simp [itemsDefs, ht] at hdefs; exact hdefs.symm
    subst e
    exact ⟨t, rfl, hb⟩

end DecodeItems

end Silmaril.Wasm.Wac.Bridge
