module

public import Silmaril.Wasi.Versions.WitImport.KErase.Defs

@[expose] public section

/-!
# Doc comments do not reach name resolution or validity

For the erased universe `U.erase` (`Silmaril.Wasi.Versions.WitImport.KErase`): feature gates commute
with erasure (`Universe.gate_erase`); the lookups return the erased items (`pkg?`, `iface?`,
`world?`, `Owner.scope`, `Owner.src?`, `typeDef?`); resolution, denotation, `isRes`, the node
lists and dependency functions of the three graphs are unchanged; and so is the validity check
(`check_erase : check U.erase = check U`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

/-! ## Generic list facts -/

theorem findSome?_map_opt {α β γ : Type} {g : α → Option γ} {h : α → Option β} {e : β → γ}
    (hg : ∀ x, g x = (h x).map e) : ∀ l : List α, l.findSome? g = (l.findSome? h).map e
  | [] => rfl
  | x :: l => by
    rw [List.findSome?_cons, List.findSome?_cons, hg x]
    cases h x with
    | none => exact findSome?_map_opt hg l
    | some b => rfl

/-! ## Projections -/

@[simp] theorem TypeDef.erase_name (d : TypeDef) : d.erase.name = d.name := rfl
@[simp] theorem TypeDef.erase_gates (d : TypeDef) : d.erase.gates = d.gates := rfl
@[simp] theorem FuncDef.erase_name (f : FuncDef) : f.erase.name = f.name := rfl
@[simp] theorem FuncDef.erase_gates (f : FuncDef) : f.erase.gates = f.gates := rfl
@[simp] theorem FuncDef.erase_func (f : FuncDef) : f.erase.func = f.func := rfl
@[simp] theorem Interface.erase_name (I : Interface) : I.erase.name = I.name := rfl
@[simp] theorem Interface.erase_gates (I : Interface) : I.erase.gates = I.gates := rfl
@[simp] theorem Interface.erase_items (I : Interface) : I.erase.items = I.items.map IfaceItem.erase := rfl
@[simp] theorem Interface.erase_docs (I : Interface) : I.erase.docs = {} := rfl
@[simp] theorem World.erase_name (W : World) : W.erase.name = W.name := rfl
@[simp] theorem World.erase_gates (W : World) : W.erase.gates = W.gates := rfl
@[simp] theorem World.erase_items (W : World) : W.erase.items = W.items.map WorldItem.erase := rfl
@[simp] theorem World.erase_docs (W : World) : W.erase.docs = {} := rfl
@[simp] theorem Package.erase_name (P : Package) : P.erase.name = P.name := rfl
@[simp] theorem Package.erase_items (P : Package) : P.erase.items = P.items.map PackageItem.erase := rfl
@[simp] theorem Package.erase_docs (P : Package) : P.erase.docs = {} := rfl
@[simp] theorem WorldExtern.erase_gates (e : WorldExtern) : e.erase.gates = e.gates := rfl
@[simp] theorem WorldExtern.erase_ext (e : WorldExtern) : e.erase.ext = e.ext.erase := rfl
@[simp] theorem WorldExtern.erase_docs (e : WorldExtern) : e.erase.docs = {} := rfl

@[simp] theorem IfaceItem.gates_erase (it : IfaceItem) : it.erase.gates = it.gates := by
  cases it <;> rfl
@[simp] theorem WorldItem.gates_erase (it : WorldItem) : it.erase.gates = it.gates := by
  cases it <;> rfl
@[simp] theorem PackageItem.gates_erase (it : PackageItem) : it.erase.gates = it.gates := by
  cases it <;> rfl

/-! ## Feature gates -/

theorem TypeDef.gate_erase (fs : List Name) (d : TypeDef) :
    TypeDef.gate fs d.erase = (TypeDef.gate fs d).erase := by
  rcases d with ⟨n, k, ds, gs⟩
  cases k <;> simp [TypeDef.gate, TypeDef.erase, TypeDefKind.erase, List.filter_map,
    Function.comp_def, ResourceFunc.erase]

theorem IfaceItem.gate_erase (fs : List Name) (it : IfaceItem) :
    IfaceItem.gate fs it.erase = (IfaceItem.gate fs it).erase := by
  cases it <;> simp [IfaceItem.gate, IfaceItem.erase, TypeDef.gate_erase]

theorem gateItems_erase (fs : List Name) (items : List IfaceItem) :
    gateItems fs (items.map IfaceItem.erase) = (gateItems fs items).map IfaceItem.erase := by
  simp [gateItems, List.filter_map, Function.comp_def, IfaceItem.gate_erase]

theorem WorldExtern.gate_erase (fs : List Name) (e : WorldExtern) :
    WorldExtern.gate fs e.erase = (WorldExtern.gate fs e).erase := by
  rcases e with ⟨x, ds, gs⟩
  cases x <;> simp [WorldExtern.gate, WorldExtern.erase, Extern.erase, gateItems_erase]

theorem WorldItem.gate_erase (fs : List Name) (it : WorldItem) :
    WorldItem.gate fs it.erase = (WorldItem.gate fs it).erase := by
  cases it <;> simp [WorldItem.gate, WorldItem.erase, WorldExtern.gate_erase, TypeDef.gate_erase]

theorem PackageItem.gate_erase (fs : List Name) (it : PackageItem) :
    PackageItem.gate fs it.erase = (PackageItem.gate fs it).erase := by
  cases it <;> simp [PackageItem.gate, PackageItem.erase, Interface.erase, World.erase,
    gateItems_erase, List.filter_map, Function.comp_def, WorldItem.gate_erase]

theorem Package.gate_erase (fs : List Name) (P : Package) :
    Package.gate fs P.erase = (Package.gate fs P).erase := by
  simp [Package.gate, Package.erase, List.filter_map, Function.comp_def, PackageItem.gate_erase]

theorem Universe.gate_erase (fs : List Name) (U : Universe) :
    Universe.gate fs U.erase = (Universe.gate fs U).erase := by
  simp [Universe.gate, Universe.erase, Package.gate_erase]

/-! ## Lookups -/

theorem Package.iface?_erase (P : Package) (n : Name) :
    P.erase.iface? n = (P.iface? n).map Interface.erase := by
  unfold Package.iface?
  rw [Package.erase_items, List.findSome?_map]
  refine findSome?_map_opt (fun it => ?_) P.items
  cases it with
  | iface I => by_cases h : I.name = n <;> simp [PackageItem.erase, h]
  | _ => rfl

theorem Package.world?_erase (P : Package) (n : Name) :
    P.erase.world? n = (P.world? n).map World.erase := by
  unfold Package.world?
  rw [Package.erase_items, List.findSome?_map]
  refine findSome?_map_opt (fun it => ?_) P.items
  cases it with
  | world W => by_cases h : W.name = n <;> simp [PackageItem.erase, h]
  | _ => rfl

theorem Package.topUse?_erase (P : Package) (n : Name) : P.erase.topUse? n = P.topUse? n := by
  unfold Package.topUse?
  rw [Package.erase_items, List.findSome?_map]
  congr 1
  funext it
  cases it <;> rfl

theorem Universe.pkg?_erase (U : Universe) (p : PackageName) :
    U.erase.pkg? p = (U.pkg? p).map Package.erase := by
  unfold Universe.pkg? Universe.erase
  rw [List.find?_map]
  rfl

theorem Universe.iface?_erase (U : Universe) (i : ItemId) :
    U.erase.iface? i = (U.iface? i).map Interface.erase := by
  unfold Universe.iface?
  rw [Universe.pkg?_erase]
  cases U.pkg? i.pkg <;> simp [Package.iface?_erase]

theorem Universe.world?_erase (U : Universe) (i : ItemId) :
    U.erase.world? i = (U.world? i).map World.erase := by
  unfold Universe.world?
  rw [Universe.pkg?_erase]
  cases U.pkg? i.pkg <;> simp [Package.world?_erase]

theorem Universe.has_erase (U : Universe) : U.erase.has = U.has := by
  funext k i
  cases k <;> simp [Universe.has, Universe.iface?_erase, Universe.world?_erase]

theorem Universe.topUse?_erase (U : Universe) : U.erase.topUse? = U.topUse? := by
  funext p n
  unfold Universe.topUse?
  rw [Universe.pkg?_erase]
  cases U.pkg? p <;> simp [Package.topUse?_erase]

theorem resolve_erase (U : Universe) : resolve U.erase = resolve U := by
  funext k p path
  cases path <;> simp [resolve, Universe.has_erase, Universe.topUse?_erase]

/-! ## Scopes -/

theorem World.inline?_erase (W : World) (e : Bool) (n : Name) :
    W.erase.inline? e n = (W.inline? e n).map (·.map IfaceItem.erase) := by
  unfold World.inline?
  rw [World.erase_items, List.findSome?_map]
  refine findSome?_map_opt (fun it => ?_) W.items
  rcases it with ⟨⟨_ | _ | _, _, _⟩⟩ | ⟨⟨_ | _ | _, _, _⟩⟩ | _ | _ | _ <;>
    simp [WorldItem.erase, WorldExtern.erase, Extern.erase, apply_ite]

theorem IfaceItem.scope_erase (it : IfaceItem) : it.erase.scope = it.scope.map ScopeItem.erase := by
  cases it <;> rfl

theorem WorldItem.scope_erase (it : WorldItem) : it.erase.scope = it.scope.map ScopeItem.erase := by
  cases it <;> rfl

theorem filterMap_scope_erase (items : List IfaceItem) :
    (items.map IfaceItem.erase).filterMap IfaceItem.scope =
      (items.filterMap IfaceItem.scope).map ScopeItem.erase := by
  simp [List.filterMap_map, List.map_filterMap, IfaceItem.scope_erase]

theorem filterMap_wscope_erase (items : List WorldItem) :
    (items.map WorldItem.erase).filterMap WorldItem.scope =
      (items.filterMap WorldItem.scope).map ScopeItem.erase := by
  simp [List.filterMap_map, List.map_filterMap, WorldItem.scope_erase]

theorem Owner.scope_inline_erase (U : Universe) (w : ItemId) (e : Bool) (n : Name) :
    (Owner.inline w e n).scope U.erase = ((Owner.inline w e n).scope U).map (·.map ScopeItem.erase) := by
  simp only [Owner.scope, Universe.world?_erase]
  cases U.world? w with
  | none => rfl
  | some W =>
    simp only [Option.map_some, Option.bind_some, World.inline?_erase]
    cases W.inline? e n with
    | none => rfl
    | some items => exact congrArg some (filterMap_scope_erase items)

theorem Owner.scope_erase (U : Universe) (o : Owner) :
    o.scope U.erase = (o.scope U).map (·.map ScopeItem.erase) := by
  cases o with
  | iface i =>
    simp only [Owner.scope, Universe.iface?_erase]
    cases U.iface? i with
    | none => rfl
    | some I => exact congrArg some (filterMap_scope_erase I.items)
  | world w =>
    simp only [Owner.scope, Universe.world?_erase]
    cases U.world? w with
    | none => rfl
    | some W => exact congrArg some (filterMap_wscope_erase W.items)
  | inline w e n => exact Owner.scope_inline_erase U w e n

theorem ScopeItem.src?_erase (x : Name) (s : ScopeItem) :
    s.erase.src? x = (s.src? x).map Src.erase := by
  cases s with
  | type d => by_cases h : d.name = x <;> simp [ScopeItem.erase, ScopeItem.src?, h, Src.erase]
  | use u => cases h : u.names.find? (fun un => un.bound = x) <;> simp [ScopeItem.erase, ScopeItem.src?, h, Src.erase]

theorem Owner.src?_erase (U : Universe) (o : Owner) (x : Name) :
    o.src? U.erase x = (o.src? U x).map Src.erase := by
  unfold Owner.src?
  rw [Owner.scope_erase]
  cases o.scope U with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.bind_some, List.findSome?_map]
    exact findSome?_map_opt (fun s => ScopeItem.src?_erase x s) l

theorem Universe.typeDef?_erase (U : Universe) (t : TypeId) :
    U.erase.typeDef? t = (U.typeDef? t).map TypeDef.erase := by
  unfold Universe.typeDef?
  rw [Owner.src?_erase]
  rcases t.owner.src? U t.name with _ | ⟨_ | _⟩ <;> rfl

theorem denote_erase (U : Universe) : ∀ f, denote U.erase f = denote U f
  | 0 => rfl
  | f + 1 => by
    funext i x
    simp only [denote, Owner.src?_erase, resolve_erase, denote_erase U f]
    rcases (Owner.iface i).src? U x with _ | ⟨_ | _⟩ <;> rfl

theorem bind_erase (U : Universe) : bind U.erase = bind U := by
  funext f o x
  simp only [bind, Owner.src?_erase, resolve_erase, denote_erase]
  rcases o.src? U x with _ | ⟨_ | _⟩ <;> rfl

theorem isRes_erase (U : Universe) (f : Nat) : ∀ g, isRes U.erase f g = isRes U f g
  | 0 => rfl
  | g + 1 => by
    funext t
    simp only [isRes, Universe.typeDef?_erase, bind_erase, isRes_erase U f g]
    rcases U.typeDef? t with _ | ⟨n, k, ds, gs⟩
    · rfl
    · cases k with
      | «alias» ty => cases ty <;> rfl
      | _ => rfl

/-! ## Graphs -/

theorem Universe.ifaceIds_erase (U : Universe) : U.erase.ifaceIds = U.ifaceIds := by
  simp only [Universe.ifaceIds, Universe.erase, List.flatMap_map, Package.erase_items,
    List.filterMap_map]
  congr 1
  funext P
  congr 1
  funext it
  cases it <;> rfl

theorem Universe.worldIds_erase (U : Universe) : U.erase.worldIds = U.worldIds := by
  simp only [Universe.worldIds, Universe.erase, List.flatMap_map, Package.erase_items,
    List.filterMap_map]
  congr 1
  funext P
  congr 1
  funext it
  cases it <;> rfl

theorem World.inlineOwners_erase (w : ItemId) (W : World) : W.erase.inlineOwners w = W.inlineOwners w := by
  simp only [World.inlineOwners, World.erase_items, List.filterMap_map]
  congr 1
  funext it
  rcases it with ⟨⟨_ | _ | _, _, _⟩⟩ | ⟨⟨_ | _ | _, _, _⟩⟩ | _ | _ | _ <;> rfl

theorem Universe.owners_erase (U : Universe) : U.erase.owners = U.owners := by
  simp only [Universe.owners, Universe.ifaceIds_erase, Universe.worldIds_erase, Universe.world?_erase]
  congr 2
  funext w
  cases U.world? w <;> simp [World.inlineOwners_erase]

theorem Universe.typeIds_erase (U : Universe) : U.erase.typeIds = U.typeIds := by
  simp only [Universe.typeIds, Universe.owners_erase, Owner.scope_erase]
  congr 1
  funext o
  cases o.scope U with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.getD_some, List.filterMap_map]
    congr 1
    funext s
    cases s <;> rfl

theorem TypeDef.refs_erase (d : TypeDef) : d.erase.refs = d.refs := by
  rcases d with ⟨n, k, ds, gs⟩
  cases k <;> simp [TypeDef.refs, TypeDef.erase, TypeDefKind.erase, Field.erase, Case.erase,
    List.flatMap_map]

theorem ifaceDeps_erase (U : Universe) : ifaceDeps U.erase = ifaceDeps U := by
  funext i
  simp only [ifaceDeps, Universe.iface?_erase, resolve_erase]
  cases U.iface? i with
  | none => rfl
  | some I =>
    simp only [Option.map_some, Interface.erase_items, List.filterMap_map]
    congr 1
    funext it
    cases it <;> rfl

theorem typeDeps_erase (U : Universe) : typeDeps U.erase = typeDeps U := by
  funext f t
  simp only [typeDeps, Universe.typeDef?_erase, bind_erase]
  cases U.typeDef? t <;> simp [TypeDef.refs_erase]

theorem worldDeps_erase (U : Universe) : worldDeps U.erase = worldDeps U := by
  funext w
  simp only [worldDeps, Universe.world?_erase, resolve_erase]
  cases U.world? w with
  | none => rfl
  | some W =>
    simp only [Option.map_some, World.erase_items, List.filterMap_map]
    congr 1
    funext it
    cases it <;> rfl

end Silmaril.Wasm.Wit
