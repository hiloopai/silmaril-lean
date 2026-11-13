module

public import Silmaril.Wasi.Versions.WitImport.KErase.Univ.Thms

@[expose] public section

/-!
# Doc comments do not reach the validity check

The resolution leaves of the checker are the same on the erased universe (`funLeaves_erase`),
every structural validity predicate holds of an erased item exactly when it holds of the item
(`ValidWith_erase`), and so `check_erase : check U.erase = check U`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

theorem World.externNames_erase (W : World) : W.erase.externNames = W.externNames := by
  simp only [World.externNames, World.erase_items, List.flatMap_map]
  congr 1
  funext it
  rcases it with ⟨⟨_ | _ | _, _, _⟩⟩ | ⟨⟨_ | _ | _, _, _⟩⟩ | _ | _ | _ <;> rfl

theorem funLeaves_erase (U : Universe) (F G : Nat) : funLeaves U.erase F G = funLeaves U F G := by
  have hr : refB U.erase F G = refB U F G := by
    funext o r
    simp [refB, bind_erase, isRes_erase]
  have hu : useB U.erase F = useB U F := by
    funext p path y
    simp [useB, resolve_erase, denote_erase]
  have hi : inclB U.erase = inclB U := by
    funext p path ns
    simp only [inclB, resolve_erase]
    cases resolve U .world p path with
    | none => rfl
    | some w =>
      simp only [Universe.world?_erase]
      cases U.world? w <;> simp [World.externNames_erase]
  simp only [funLeaves, hr, hu, hi, resolve_erase]

section
variable (L : Leaves)

theorem KindOk_erase (o : Owner) (k : TypeDefKind) : KindOk L o k.erase ↔ KindOk L o k := by
  cases k <;> simp [KindOk, TypeDefKind.erase, Field.erase, Case.erase, Label.erase,
    ResourceFunc.erase, List.map_map, Function.comp_def, List.filter_map, List.filterMap_map,
    ResourceFuncOk]

theorem TypeDefOk_erase (o : Owner) (d : TypeDef) : TypeDefOk L o d.erase ↔ TypeDefOk L o d := by
  simp only [TypeDefOk, TypeDef.erase_name, TypeDef.erase_gates]
  rw [show d.erase.kind = d.kind.erase from rfl, KindOk_erase]

theorem IfaceItemOk_erase (o : Owner) (it : IfaceItem) : IfaceItemOk L o it.erase ↔ IfaceItemOk L o it := by
  cases it with
  | type d => exact TypeDefOk_erase L o d
  | use u => exact Iff.rfl
  | func f => exact Iff.rfl

theorem IfaceItem.names_erase (it : IfaceItem) : it.erase.names = it.names := by
  cases it <;> rfl

theorem ItemsOk_erase (o : Owner) (items : List IfaceItem) :
    ItemsOk L o (items.map IfaceItem.erase) ↔ ItemsOk L o items := by
  simp [ItemsOk, List.flatMap_map, IfaceItem.names_erase, IfaceItemOk_erase]

theorem InterfaceOk_erase (p : PackageName) (I : Interface) : InterfaceOk L p I.erase ↔ InterfaceOk L p I := by
  simp only [InterfaceOk, Interface.erase_name, Interface.erase_gates, Interface.erase_items, ItemsOk_erase]

theorem ExternOk_erase (w : ItemId) (b : Bool) (e : Extern) : ExternOk L w b e.erase ↔ ExternOk L w b e := by
  cases e with
  | iface n items => simp only [Extern.erase, ExternOk, ItemsOk_erase]
  | _ => exact Iff.rfl

theorem WorldItemOk_erase (w : ItemId) (it : WorldItem) : WorldItemOk L w it.erase ↔ WorldItemOk L w it := by
  cases it with
  | «import» e => simp only [WorldItem.erase, WorldItemOk, WorldExtern.erase_gates, WorldExtern.erase_ext, ExternOk_erase]
  | «export» e => simp only [WorldItem.erase, WorldItemOk, WorldExtern.erase_gates, WorldExtern.erase_ext, ExternOk_erase]
  | type d => exact TypeDefOk_erase L _ d
  | _ => exact Iff.rfl

theorem WorldItem.importNames_erase (it : WorldItem) : it.erase.importNames = it.importNames := by
  rcases it with ⟨⟨_ | _ | _, _, _⟩⟩ | ⟨⟨_ | _ | _, _, _⟩⟩ | _ | _ | _ <;> rfl

theorem WorldItem.exportNames_erase (it : WorldItem) : it.erase.exportNames = it.exportNames := by
  rcases it with ⟨⟨_ | _ | _, _, _⟩⟩ | ⟨⟨_ | _ | _, _, _⟩⟩ | _ | _ | _ <;> rfl

theorem WorldOk_erase (p : PackageName) (W : World) : WorldOk L p W.erase ↔ WorldOk L p W := by
  simp [WorldOk, List.flatMap_map, WorldItem.importNames_erase, WorldItem.exportNames_erase,
    WorldItemOk_erase]

theorem PackageItemOk_erase (p : PackageName) (it : PackageItem) :
    PackageItemOk L p it.erase ↔ PackageItemOk L p it := by
  cases it with
  | iface I => exact InterfaceOk_erase L p I
  | world W => exact WorldOk_erase L p W
  | use u => exact Iff.rfl

theorem PackageItem.name_erase (it : PackageItem) : it.erase.name = it.name := by
  cases it <;> rfl

theorem PackageOk_erase (P : Package) : PackageOk L P.erase ↔ PackageOk L P := by
  simp [PackageOk, List.map_map, Function.comp_def, PackageItem.name_erase, PackageItemOk_erase]

theorem ValidWith_erase (U : Universe) : ValidWith L U.erase ↔ ValidWith L U := by
  simp [ValidWith, Universe.erase, List.map_map, Function.comp_def, PackageOk_erase]

end

theorem check_erase (U : Universe) : check U.erase = check U := by
  unfold check
  rw [ifaceDeps_erase, Universe.ifaceIds_erase, typeDeps_erase, Universe.typeIds_erase,
    worldDeps_erase, Universe.worldIds_erase]
  congr 1
  exact decide_eq_decide.mpr (by rw [funLeaves_erase]; exact ValidWith_erase _ U)

end Silmaril.Wasm.Wit
