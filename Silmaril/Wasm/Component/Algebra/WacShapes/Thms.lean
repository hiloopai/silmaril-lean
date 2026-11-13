module

public import Silmaril.Wasm.Component.Algebra.WacShapes.Defs
public import Silmaril.Proofs.Wasm.Component.Algebra.WacShapes.Main
public import Silmaril.Wasm.Wac.Nest.Defs

/-!
# WAC statement shapes as algebra operators

Each shape of WAC statement has its operator of the component algebra:

| WAC text | composition graph | algebra | theorem |
|---|---|---|---|
| `let x = new p { a: e, … }` | an instance node `⟨p, args⟩` | the term node `.inst (.var p) args` | `Graph.term`, `eval_term` |
| `new p { … }` with `...` (promotion) | implicit arguments | explicit arguments (`reimport`) | `Wac.toComp_explicate` |
| `new p { ...i }` (spread) | arguments by name | `reimport … (byName …)` | `plug_equiv_seq` |
| `new p` of a composition | `nestPkgs` | substitution of terms | `build_nestPkgs`, `Wac.nest_inline` |
| `wac plug` (by name) | `Graph.seq g₁ g₂` | `seq` after `reimport` | `seq_graph` (any graphs) |
| `export e as n` | `Graph.renameExps` | `renameExports` | `toComp_renameExps` |
| the exports a document names | `Graph.keepExps` | `select` | `keepExps_equiv` |
| `x.f`, `x["f"]` (aliases) | references, no node | wiring `Impl.fwd` | `Bridge.toGraph` |
| types, resources, worlds | no node | none (no functions) | `Bridge.toGraph` |

Values (`import v: u32`, value arguments) and components passed as values have no reading in
the function-level IR; `Bridge.NoValue` excludes them (the tool checks it, `EndToEnd.noValues`).

* `toComp_renameExps`: renaming the exports of a graph is `renameExports` of its component
  (an equality);
* `keepExps_equiv`: keeping the exports of indices `keep` of a graph whose exports are
  instance exports is `select keep` of its component, for every core semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Wac WacShapesProof

variable {M : Type}

theorem iface_renameExps (S : Nat → PkgSig) (f : String → String) (g : Graph) :
    (g.renameExps f).iface S = g.iface S := by
  simp only [Graph.iface, Graph.renameExps, Graph.exportUses, List.filterMap_map]
  rfl

/-- **`export e as n` is renaming of exports.** -/
theorem toComp_renameExps (P : Nat → Comp M) (f : String → String) (g : Graph) :
    (g.renameExps f).toComp P = renameExports f (g.toComp P) := by
  have hI := iface_renameExps (fun k => sigOf (P k)) f g
  have hn : (g.renameExps f).nodes = g.nodes := rfl
  simp only [Graph.toComp, Graph.build, hI, Graph.mkExports]
  rw [mkNodes_congr P hn, resolve_congr hn, tyOf_congr hn]
  simp only [Graph.renameExps, renameExports, List.map_map]
  rfl

theorem iface_keepExps {S : Nat → PkgSig} {g : Graph} (ho : g.ExportsOut) (keep : List Nat) :
    (g.keepExps keep).iface S = g.iface S := by
  have h₁ : (g.keepExps keep).exportUses = [] := by
    refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hp
    obtain ⟨k, q, hk⟩ := ho p (List.mem_of_getElem? hj)
    simp only [hk]
  have h₂ : g.exportUses = [] := by
    refine List.filterMap_eq_nil_iff.2 fun p hp => ?_
    obtain ⟨k, q, hk⟩ := ho p hp
    simp only [hk]
  simp only [Graph.iface, h₁, h₂]
  rfl

theorem mkExports_keepExps (S : Nat → PkgSig) (g : Graph) (I : Iface) (keep : List Nat) :
    ((g.keepExps keep).mkExports S I).map Export.impl =
      keep.filterMap fun j => ((g.mkExports S I).map Export.impl)[j]? := by
  have hn : (g.keepExps keep).nodes = g.nodes := rfl
  simp only [Graph.mkExports]
  rw [resolve_congr hn, tyOf_congr hn]
  simp only [Graph.keepExps, List.map_filterMap, List.map_map, List.getElem?_map, Option.map_map]

variable [CoreModule M]

/-- **Exporting only some of a composition's exports is `select`**, when its exports are
exports of its instances. -/
theorem keepExps_equiv (C : CoreSem M) (P : Nat → Comp M) {g : Graph} (ho : g.ExportsOut)
    (keep : List Nat) :
    CompEquiv C ((g.keepExps keep).toComp P) (select keep (g.toComp P)) := by
  have hI := iface_keepExps (S := fun k => sigOf (P k)) ho keep
  have hn : (g.keepExps keep).nodes = g.nodes := rfl
  have hX := mkExports_keepExps (fun k => sigOf (P k)) g (g.iface fun k => sigOf (P k)) keep
  have hlen : ((g.mkExports (fun k => sigOf (P k)) (g.iface fun k => sigOf (P k))).map
      Export.impl).length = (g.toComp P).exports.length := List.length_map _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ((g.keepExps keep).iface _).length = (g.iface _).length
    rw [hI]
  · show (Graph.mkExports _ _ _).length = (keptExports _ _ _).length
    rw [length_keptExports, ← List.length_map (f := Export.impl), hI, hX, ← hlen,
      length_filterMap_get]
  · rw [denU_select]
    simp only [Graph.toComp, Graph.build, Comp.denU, hI, mkNodes_congr P hn, hn, exportsH, hX,
      implsH_filterMap, Strategy.comp_assoc, Strategy.ofHandler_comp, Comp.exports_mk, List.length_map]
    rfl

end Silmaril.Wasm.Component.Algebra
