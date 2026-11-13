module

public import Silmaril.Wasm.Wac.WitOrder.Defs

/-!
# WIT packages in wit-parser's item order: theorems

* `topo_perm`, `sortPkg_perm`: reordering keeps every item (a permutation), so the sorted
  package declares the same interfaces and worlds;
* `encodeTextO_of_unchanged`: when resolving aliases and sorting change nothing and
  `WitDir.encodeTextX` succeeds, `encodeTextO` gives its bytes (and so, for one file, `Wit.Tool.encodeText`: `WitDir.encodeTextX_of_ok`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WitOrder

open Silmaril.Wasm.Wit

theorem topo_perm (tops : List (Name × Option Name)) (names : List Name) :
    ∀ (f : Nat) (done : List Name) (rest : List PackageItem),
      (topo tops names f done rest).Perm rest
  | 0, _, _ => .refl _
  | f + 1, done, rest => by
    unfold topo
    split
    · exact .refl _
    · rename_i it hit
      have hm : it ∈ rest := List.mem_of_find?_eq_some hit
      exact ((topo_perm tops names f _ (rest.erase it)).cons it).trans (List.perm_cons_erase hm).symm

theorem sortPkg_perm (p : Package) : (sortPkg p).items.Perm p.items := by
  have h1 : (p.items.filter fun it => (itemName it).isNone) ++
      (p.items.filter fun it => (itemName it).isSome) |>.Perm p.items := by
    have h := List.filter_append_perm (fun it => (itemName it).isNone) p.items
    simpa [Option.isSome_iff_ne_none, Option.isNone_iff_eq_none] using h
  exact ((List.Perm.refl _).append (topo_perm _ _ _ _ _)).trans h1

theorem encodeTextO_of_unchanged {main : List (String × String)}
    {deps : List (List (String × String))} {d₀ d : Document} {ds₀ ds : List Document}
    {b : ByteArray}
    (hd₀ : WitDir.parseFiles main = .ok d₀) (hds₀ : deps.mapM WitDir.parseFiles = .ok ds₀)
    (hd : parseFilesR main = .ok d) (hds : deps.mapM parseFilesR = .ok ds)
    (hu : unchanged d₀ d = true) (hus : (ds₀.zip ds).all (fun p => unchanged p.1 p.2) = true)
    (hok : WitDir.encodeTextX main deps = .ok b) : encodeTextO main deps = .ok b := by
  simp [encodeTextO, hd₀, hds₀, hd, hds, hu, hus, hok]

end Silmaril.Wasm.Wac.WitOrder
