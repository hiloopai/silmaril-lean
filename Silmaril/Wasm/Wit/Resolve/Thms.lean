module

public import Silmaril.Wasm.Wit.Resolve.Defs
public import Silmaril.Wasm.Wit.Graph.Thms

/-!
# WIT: name resolution is computed by the resolution functions

* `resolve_iff`: `resolve U k p path = some i ↔ ResolvesTo U k p path i`.
* `denote_sound`, `bind_sound`, `isRes_sound`: the fuelled functions only return
  what the relations derive, at every fuel.
* `denote_complete`, `bind_complete`, `isRes_complete`: when the interface graph
  (resp. type graph) is ranked, fuel above the rank suffices.
* `ifaceEdge_iff`, `typeEdge_iff`, `worldEdge_iff`: the edge relations are the
  `deps` edges between the nodes, so `Graph.kahn` decides their acyclicity.
* `bind_iff_of_kahn`, `denote_iff_of_kahn`, `isRes_iff_of_kahn`: once `kahn`
  accepts the interface graph (resp. both graphs), the functions with fuel the number
  of interfaces (resp. types) are exactly the relations; `kahn_iface_iff`,
  `kahn_type_iff`, `kahn_world_iff`: `kahn` decides the acyclicity of the three graphs.
* `ResolvesTo.det`, `Denotes.det`, `Binds.det`: resolution is deterministic.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

open Graph

variable {U : Universe}

/-! ## Paths -/

theorem resolve_foreign_sound {k : Kind} {p q : PackageName} {n : Name} {i : ItemId}
    (h : resolve U k p (.foreign q n) = some i) : ResolvesTo U k p (.foreign q n) i := by
  by_cases hq : U.has k ⟨q, n⟩ = true
  · have hi : i = ⟨q, n⟩ := by simpa [resolve, hq, eq_comm] using h
    exact hi ▸ .foreign hq
  · simp [resolve, hq] at h

theorem resolve_alias_sound {k : Kind} {p : PackageName} {n : Name} {i : ItemId}
    (hp : U.has k ⟨p, n⟩ = false) (h : resolve U k p (.local n) = some i) :
    ResolvesTo U k p (.local n) i := by
  simp only [resolve, hp, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · rename_i q m ht
    by_cases hq : U.has k ⟨q, m⟩ = true
    · have hi : i = ⟨q, m⟩ := by simpa [hq, eq_comm] using h
      exact hi ▸ .alias hp ht hq
    · simp [hq] at h
  · cases h

theorem resolve_sound {k : Kind} {p : PackageName} {path : UsePath} {i : ItemId}
    (h : resolve U k p path = some i) : ResolvesTo U k p path i := by
  cases path with
  | foreign q n => exact resolve_foreign_sound h
  | «local» n =>
    by_cases hp : U.has k ⟨p, n⟩ = true
    · have hi : i = ⟨p, n⟩ := by simpa [resolve, hp, eq_comm] using h
      exact hi ▸ .local hp
    · exact resolve_alias_sound (by simpa using hp) h

theorem resolve_complete {k : Kind} {p : PackageName} {path : UsePath} {i : ItemId}
    (h : ResolvesTo U k p path i) : resolve U k p path = some i := by
  cases h with
  | foreign hq => simp [resolve, hq]
  | «local» hp => simp [resolve, hp]
  | alias hp ht hq => simp [resolve, hp, ht, hq]

theorem resolve_iff {k : Kind} {p : PackageName} {path : UsePath} {i : ItemId} :
    resolve U k p path = some i ↔ ResolvesTo U k p path i :=
  ⟨resolve_sound, resolve_complete⟩

theorem ResolvesTo.has {k : Kind} {p : PackageName} {path : UsePath} {i : ItemId}
    (h : ResolvesTo U k p path i) : U.has k i = true := by
  cases h <;> assumption

/-! ## Soundness of the fuelled functions -/

theorem denote_sound : ∀ (f : Nat) (i : ItemId) (x : Name) (t : TypeId),
    denote U f i x = some t → Denotes U i x t
  | 0, _, _, _, h => by simp [denote] at h
  | f + 1, i, x, t, h => by
    cases hs : (Owner.iface i).src? U x with
    | none => simp [denote, hs] at h
    | some s =>
      cases s with
      | type d =>
        have ht : t = ⟨.iface i, x⟩ := by simpa [denote, hs] using h.symm
        exact ht ▸ .type hs
      | use path y =>
        have h' : ((resolve U .iface i.pkg path).bind fun j => denote U f j y) = some t := by
          simpa [denote, hs] using h
        obtain ⟨j, hj, hd⟩ := Option.bind_eq_some_iff.mp h'
        exact .use hs (resolve_iff.mp hj) (denote_sound f j y t hd)

theorem bind_sound {f : Nat} {o : Owner} {x : Name} {t : TypeId}
    (h : bind U f o x = some t) : Binds U o x t := by
  cases hs : o.src? U x with
  | none => simp [bind, hs] at h
  | some s =>
    cases s with
    | type d =>
      have ht : t = ⟨o, x⟩ := by simpa [bind, hs] using h.symm
      exact ht ▸ .type hs
    | use path y =>
      have h' : ((resolve U .iface o.pkg path).bind fun j => denote U f j y) = some t := by
        simpa [bind, hs] using h
      obtain ⟨j, hj, hd⟩ := Option.bind_eq_some_iff.mp h'
      exact .use hs (resolve_iff.mp hj) (denote_sound f j y t hd)

/-! ## Membership -/

theorem pkg?_mem {p : PackageName} {P : Package} (h : U.pkg? p = some P) :
    P ∈ U ∧ P.name = p :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem Package.iface?_mem {P : Package} {n : Name} {I : Interface}
    (h : P.iface? n = some I) : PackageItem.iface I ∈ P.items ∧ I.name = n := by
  obtain ⟨a, ha, he⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | iface J =>
    by_cases hJ : J.name = n
    · have hJI : J = I := by simpa [hJ] using he
      exact hJI ▸ ⟨ha, hJ⟩
    · simp [hJ] at he
  | world _ | use _ => simp at he

theorem Package.world?_mem {P : Package} {n : Name} {W : World}
    (h : P.world? n = some W) : PackageItem.world W ∈ P.items ∧ W.name = n := by
  obtain ⟨a, ha, he⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | world J =>
    by_cases hJ : J.name = n
    · have hJW : J = W := by simpa [hJ] using he
      exact hJW ▸ ⟨ha, hJ⟩
    · simp [hJ] at he
  | iface _ | use _ => simp at he

theorem iface?_mem_ids {i : ItemId} {I : Interface} (h : U.iface? i = some I) :
    i ∈ U.ifaceIds := by
  obtain ⟨P, hP, hI⟩ := Option.bind_eq_some_iff.mp h
  have hP' := pkg?_mem hP
  have hI' := Package.iface?_mem hI
  refine List.mem_flatMap.mpr ⟨P, hP'.1, List.mem_filterMap.mpr ⟨.iface I, hI'.1, ?_⟩⟩
  simp [hP'.2, hI'.2]

theorem world?_mem_ids {w : ItemId} {W : World} (h : U.world? w = some W) :
    w ∈ U.worldIds := by
  obtain ⟨P, hP, hW⟩ := Option.bind_eq_some_iff.mp h
  have hP' := pkg?_mem hP
  have hW' := Package.world?_mem hW
  refine List.mem_flatMap.mpr ⟨P, hP'.1, List.mem_filterMap.mpr ⟨.world W, hW'.1, ?_⟩⟩
  simp [hP'.2, hW'.2]

theorem has_iface_mem {i : ItemId} (h : U.has .iface i = true) : i ∈ U.ifaceIds := by
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.mp h
  exact iface?_mem_ids hI

theorem has_world_mem {w : ItemId} (h : U.has .world w = true) : w ∈ U.worldIds := by
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp h
  exact world?_mem_ids hW

theorem ScopeItem.src?_use {x : Name} {si : ScopeItem} {path : UsePath} {y : Name}
    (h : si.src? x = some (.use path y)) : ∃ u, si = .use u ∧ u.path = path := by
  cases si with
  | type d => by_cases hd : d.name = x <;> simp [ScopeItem.src?, hd] at h
  | use u =>
    simp only [ScopeItem.src?, Option.map_eq_some_iff, Src.use.injEq] at h
    obtain ⟨_, _, hp, _⟩ := h
    exact ⟨u, rfl, hp⟩

theorem src?_use_mem {i : ItemId} {x : Name} {path : UsePath} {y : Name}
    (h : (Owner.iface i).src? U x = some (.use path y)) :
    ∃ I u, U.iface? i = some I ∧ IfaceItem.use u ∈ I.items ∧ u.path = path := by
  obtain ⟨l, hl, hf⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨I, hI, hlI⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨si, hsi, hs⟩ := List.exists_of_findSome?_eq_some hf
  obtain ⟨u, rfl, hp⟩ := ScopeItem.src?_use hs
  have hmem : ScopeItem.use u ∈ I.items.filterMap IfaceItem.scope := hlI ▸ hsi
  obtain ⟨it, hit, hsc⟩ := List.mem_filterMap.mp hmem
  cases it with
  | use u' =>
    have hu : u' = u := by simpa [IfaceItem.scope] using hsc
    exact ⟨I, u, hI, hu ▸ hit, hp⟩
  | type _ | func _ => simp [IfaceItem.scope] at hsc

/-! ## The interface graph -/

theorem ifaceEdge_iff (i j : ItemId) :
    IfaceEdge U i j ↔ i ∈ U.ifaceIds ∧ j ∈ ifaceDeps U i ∧ j ∈ U.ifaceIds := by
  constructor
  · rintro ⟨I, u, hI, hu, hr⟩
    have hd : j ∈ ifaceDeps U i := by
      simp only [ifaceDeps, hI]
      exact List.mem_filterMap.mpr ⟨.use u, hu, resolve_complete hr⟩
    exact ⟨iface?_mem_ids hI, hd, has_iface_mem hr.has⟩
  · rintro ⟨_, hd, _⟩
    cases hI : U.iface? i with
    | none => simp [ifaceDeps, hI] at hd
    | some I =>
      simp only [ifaceDeps, hI] at hd
      obtain ⟨it, hit, he⟩ := List.mem_filterMap.mp hd
      cases it with
      | use u => exact ⟨I, u, hI, hit, resolve_sound he⟩
      | type _ | func _ => simp at he

/-! ## Completeness of the fuelled functions -/

theorem denote_complete {r : ItemId → Nat} (hr : ∀ i j, IfaceEdge U i j → r j < r i)
    {i : ItemId} {x : Name} {t : TypeId} (h : Denotes U i x t) :
    ∀ f, r i < f → denote U f i x = some t := by
  induction h with
  | type hs =>
    intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp [denote, hs]
  | use hs hres _ ih =>
    intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨I, u, hI, hu, hp⟩ := src?_use_mem hs
    have hedge := hr _ _ ⟨I, u, hI, hu, hp ▸ hres⟩
    have hd := ih f' (by omega)
    simp [denote, hs, resolve_complete hres, hd]

theorem bind_complete {r : ItemId → Nat} (hr : ∀ i j, IfaceEdge U i j → r j < r i)
    {f : Nat} (hf : ∀ j ∈ U.ifaceIds, r j < f) {o : Owner} {x : Name} {t : TypeId}
    (h : Binds U o x t) : bind U f o x = some t := by
  cases h with
  | type hs => simp [bind, hs]
  | use hs hres hd =>
    have hd' := denote_complete hr hd f (hf _ (has_iface_mem hres.has))
    simp [bind, hs, resolve_complete hres, hd']

theorem Denotes.mem {i : ItemId} {x : Name} {t : TypeId} (h : Denotes U i x t) :
    i ∈ U.ifaceIds := by
  have hs : ∃ s, (Owner.iface i).src? U x = some s := by
    cases h with
    | type hs => exact ⟨_, hs⟩
    | use hs _ _ => exact ⟨_, hs⟩
  obtain ⟨s, hs⟩ := hs
  obtain ⟨l, hl, _⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨I, hI, _⟩ := Option.map_eq_some_iff.mp hl
  exact iface?_mem_ids hI

/-- Once the interface graph is acyclic, `bind` with fuel the number of interfaces is
`Binds`. -/
theorem bind_iff_of_kahn (hk : kahn (ifaceDeps U) U.ifaceIds = true) {o : Owner}
    {x : Name} {t : TypeId} : bind U U.ifaceIds.length o x = some t ↔ Binds U o x t := by
  obtain ⟨r, hr, hb⟩ := kahn_bounded_edges (ifaceDeps U) (fun a b => ifaceEdge_iff a b) hk
  exact ⟨bind_sound, bind_complete hr hb⟩

/-- Once the interface graph is acyclic, `denote` with fuel the number of interfaces is
`Denotes`. -/
theorem denote_iff_of_kahn (hk : kahn (ifaceDeps U) U.ifaceIds = true) {i : ItemId}
    {x : Name} {t : TypeId} : denote U U.ifaceIds.length i x = some t ↔ Denotes U i x t := by
  obtain ⟨r, hr, hb⟩ := kahn_bounded_edges (ifaceDeps U) (fun a b => ifaceEdge_iff a b) hk
  exact ⟨denote_sound _ _ _ _, fun h => denote_complete hr h _ (hb _ h.mem)⟩

/-- Acyclicity of the interface graph is decided by `kahn`. -/
theorem kahn_iface_iff :
    kahn (ifaceDeps U) U.ifaceIds = true ↔ ∃ r : ItemId → Nat, ∀ i j, IfaceEdge U i j → r j < r i :=
  (kahn_iff _ _).trans (acyclic_iff_edges _ fun a b => ifaceEdge_iff a b)

/-! ## The world graph -/

theorem worldEdge_iff (w w' : ItemId) :
    WorldEdge U w w' ↔ w ∈ U.worldIds ∧ w' ∈ worldDeps U w ∧ w' ∈ U.worldIds := by
  constructor
  · rintro ⟨W, i, hW, hi, hr⟩
    have hd : w' ∈ worldDeps U w := by
      simp only [worldDeps, hW]
      exact List.mem_filterMap.mpr ⟨.include i, hi, resolve_complete hr⟩
    exact ⟨world?_mem_ids hW, hd, has_world_mem hr.has⟩
  · rintro ⟨_, hd, _⟩
    cases hW : U.world? w with
    | none => simp [worldDeps, hW] at hd
    | some W =>
      simp only [worldDeps, hW] at hd
      obtain ⟨it, hit, he⟩ := List.mem_filterMap.mp hd
      cases it with
      | «include» i => exact ⟨W, i, hW, hit, resolve_sound he⟩
      | «import» _ | «export» _ | use _ | type _ => simp at he

/-- Acyclicity of the world graph is decided by `kahn`. -/
theorem kahn_world_iff :
    kahn (worldDeps U) U.worldIds = true ↔ ∃ r : ItemId → Nat, ∀ w w', WorldEdge U w w' → r w' < r w :=
  (kahn_iff _ _).trans (acyclic_iff_edges _ fun a b => worldEdge_iff a b)

/-! ## Types -/

theorem typeDef?_eq {t : TypeId} {d : TypeDef} :
    U.typeDef? t = some d ↔ t.owner.src? U t.name = some (.type d) := by
  unfold Universe.typeDef?
  cases hs : t.owner.src? U t.name with
  | none => simp
  | some s => cases s <;> simp

theorem src?_type {o : Owner} {x : Name} {d : TypeDef} (h : o.src? U x = some (.type d)) :
    ∃ l, o.scope U = some l ∧ ScopeItem.type d ∈ l ∧ d.name = x := by
  obtain ⟨l, hl, hf⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨si, hsi, hs⟩ := List.exists_of_findSome?_eq_some hf
  cases si with
  | type d' =>
    by_cases hd : d'.name = x
    · have hdd : d' = d := by simpa [ScopeItem.src?, hd] using hs
      exact ⟨l, hl, hdd ▸ hsi, hdd ▸ hd⟩
    · simp [ScopeItem.src?, hd] at hs
  | use u => simp [ScopeItem.src?] at hs

theorem World.inline?_mem {W : World} {e : Bool} {n : Name} {items : List IfaceItem}
    (h : W.inline? e n = some items) (w : ItemId) : Owner.inline w e n ∈ W.inlineOwners w := by
  obtain ⟨a, ha, he⟩ := List.exists_of_findSome?_eq_some h
  refine List.mem_filterMap.mpr ⟨a, ha, ?_⟩
  rcases a with ⟨⟨_, _⟩ | ⟨m, its⟩ | _, _, _⟩ | ⟨⟨_, _⟩ | ⟨m, its⟩ | _, _, _⟩ | _ | _ | _ <;>
    simp_all

theorem Owner.scope_mem {o : Owner} {l : List ScopeItem} (h : o.scope U = some l) :
    o ∈ U.owners := by
  cases o with
  | iface i =>
    obtain ⟨I, hI, _⟩ := Option.map_eq_some_iff.mp h
    exact List.mem_append_left _ (List.mem_map_of_mem (iface?_mem_ids hI))
  | world w =>
    obtain ⟨W, hW, _⟩ := Option.map_eq_some_iff.mp h
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, world?_mem_ids hW, List.mem_cons_self⟩)
  | inline w e n =>
    obtain ⟨its, hits, _⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨W, hW, hin⟩ := Option.bind_eq_some_iff.mp hits
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨w, world?_mem_ids hW, ?_⟩)
    simp only [hW]
    exact List.mem_cons_of_mem _ (World.inline?_mem hin w)

theorem typeDef?_mem {t : TypeId} {d : TypeDef} (h : U.typeDef? t = some d) :
    t ∈ U.typeIds := by
  obtain ⟨l, hl, hmem, hn⟩ := src?_type (typeDef?_eq.mp h)
  refine List.mem_flatMap.mpr ⟨t.owner, Owner.scope_mem hl, ?_⟩
  simp only [hl, Option.getD_some]
  exact List.mem_filterMap.mpr ⟨.type d, hmem, by simp [hn]⟩

theorem Denotes.typeDef {i : ItemId} {x : Name} {t : TypeId} (h : Denotes U i x t) :
    ∃ d, U.typeDef? t = some d := by
  induction h with
  | type hs => exact ⟨_, typeDef?_eq.mpr hs⟩
  | use _ _ _ ih => exact ih

theorem Binds.typeDef {o : Owner} {x : Name} {t : TypeId} (h : Binds U o x t) :
    ∃ d, U.typeDef? t = some d := by
  cases h with
  | type hs => exact ⟨_, typeDef?_eq.mpr hs⟩
  | use _ _ hd => exact hd.typeDef

theorem IsResource.typeDef {t : TypeId} (h : IsResource U t) : ∃ d, U.typeDef? t = some d := by
  cases h with
  | resource hd _ => exact ⟨_, hd⟩
  | alias hd _ _ _ => exact ⟨_, hd⟩

theorem typeEdge_iff {f : Nat} (hB : ∀ o x t, bind U f o x = some t ↔ Binds U o x t)
    (t t' : TypeId) :
    TypeEdge U t t' ↔ t ∈ U.typeIds ∧ t' ∈ typeDeps U f t ∧ t' ∈ U.typeIds := by
  constructor
  · rintro ⟨d, hd, r, hr, hb⟩
    have hdep : t' ∈ typeDeps U f t := by
      simp only [typeDeps, hd]
      exact List.mem_filterMap.mpr ⟨r, hr, (hB _ _ _).mpr hb⟩
    obtain ⟨d', hd'⟩ := hb.typeDef
    exact ⟨typeDef?_mem hd, hdep, typeDef?_mem hd'⟩
  · rintro ⟨_, hdep, _⟩
    cases hd : U.typeDef? t with
    | none => simp [typeDeps, hd] at hdep
    | some d =>
      simp only [typeDeps, hd] at hdep
      obtain ⟨r, hr, hb⟩ := List.mem_filterMap.mp hdep
      exact ⟨d, hd, r, hr, (hB _ _ _).mp hb⟩

/-- Once the interface graph is acyclic, acyclicity of the type graph is decided by
`kahn` with fuel the number of interfaces. -/
theorem kahn_type_iff (hi : kahn (ifaceDeps U) U.ifaceIds = true) :
    kahn (typeDeps U U.ifaceIds.length) U.typeIds = true ↔
      ∃ s : TypeId → Nat, ∀ t t', TypeEdge U t t' → s t' < s t :=
  (kahn_iff _ _).trans (acyclic_iff_edges _ fun a b =>
    typeEdge_iff (fun _ _ _ => bind_iff_of_kahn hi) a b)

theorem isRes_alias_sound {f g : Nat} {t : TypeId} {d : TypeDef} {n : Name}
    (hd : U.typeDef? t = some d) (hk : d.kind = .alias (.named n))
    (ih : ∀ t', isRes U f g t' = true → IsResource U t')
    (h : isRes U f (g + 1) t = true) : IsResource U t := by
  obtain ⟨nm, kind, docs, gates⟩ := d
  cases hk
  cases hb : bind U f t.owner n with
  | none => simp [isRes, hd, hb] at h
  | some t' =>
    have h' : isRes U f g t' = true := by simpa [isRes, hd, hb] using h
    exact .alias hd rfl (bind_sound hb) (ih t' h')

theorem isRes_sound {f : Nat} : ∀ (g : Nat) (t : TypeId), isRes U f g t = true → IsResource U t
  | 0, _, h => by simp [isRes] at h
  | g + 1, t, h => by
    cases hd : U.typeDef? t with
    | none => simp [isRes, hd] at h
    | some d =>
      obtain ⟨nm, kind, docs, gates⟩ := d
      cases kind with
      | resource fs => exact .resource hd rfl
      | alias ty =>
        cases ty with
        | named n => exact isRes_alias_sound hd rfl (isRes_sound g) h
        | _ => simp [isRes, hd] at h
      | _ => simp [isRes, hd] at h

theorem isRes_complete {s : TypeId → Nat} (hs : ∀ t t', TypeEdge U t t' → s t' < s t)
    {f : Nat} (hB : ∀ {o x t}, Binds U o x t → bind U f o x = some t)
    {t : TypeId} (h : IsResource U t) : ∀ g, s t < g → isRes U f g t = true := by
  induction h with
  | @resource t d fs hd hk =>
    intro g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    obtain ⟨nm, kind, docs, gates⟩ := d
    cases hk
    simp [isRes, hd]
  | @alias t d n t' hd hk hb _ ih =>
    intro g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hedge : s t' < s t := hs _ _ ⟨d, hd, (.plain, n), by simp [TypeDef.refs, hk, Ty.refs], hb⟩
    have hr := ih g' (by omega)
    obtain ⟨nm, kind, docs, gates⟩ := d
    cases hk
    simp [isRes, hd, hB hb, hr]

/-- Once both graphs are acyclic, `isRes` with fuel the numbers of interfaces and of
types is `IsResource`. -/
theorem isRes_iff_of_kahn (hi : kahn (ifaceDeps U) U.ifaceIds = true)
    (ht : kahn (typeDeps U U.ifaceIds.length) U.typeIds = true) {t : TypeId} :
    isRes U U.ifaceIds.length U.typeIds.length t = true ↔ IsResource U t := by
  have hB : ∀ o x t, bind U U.ifaceIds.length o x = some t ↔ Binds U o x t :=
    fun _ _ _ => bind_iff_of_kahn hi
  obtain ⟨s, hs, hb⟩ := kahn_bounded_edges (typeDeps U _) (fun a b => typeEdge_iff hB a b) ht
  refine ⟨isRes_sound _ _, fun h => isRes_complete hs (fun hb' => (hB _ _ _).mpr hb') h _ ?_⟩
  obtain ⟨d, hd⟩ := h.typeDef
  exact hb _ (typeDef?_mem hd)

/-! ## Determinism -/

theorem ResolvesTo.det {k : Kind} {p : PackageName} {path : UsePath} {i i' : ItemId}
    (h : ResolvesTo U k p path i) (h' : ResolvesTo U k p path i') : i = i' := by
  have e : some i = some i' := (resolve_complete h).symm.trans (resolve_complete h')
  simpa using e

/-- A name of an interface denotes at most one type. -/
theorem Denotes.det {i : ItemId} {x : Name} {t t' : TypeId} (h : Denotes U i x t)
    (h' : Denotes U i x t') : t = t' := by
  induction h generalizing t' with
  | type hs =>
    cases h' with
    | type _ => rfl
    | use hs' _ _ => exact absurd (hs.symm.trans hs') (by simp)
  | use hs hr _ ih =>
    cases h' with
    | type hs' => exact absurd (hs.symm.trans hs') (by simp)
    | use hs' hr' hd' =>
      have e : Src.use _ _ = Src.use _ _ := Option.some.inj (hs.symm.trans hs')
      obtain ⟨rfl, rfl⟩ := Src.use.inj e
      exact ih (hr.det hr' ▸ hd')

/-- A name binds at most one type in a scope. -/
theorem Binds.det {o : Owner} {x : Name} {t t' : TypeId} (h : Binds U o x t)
    (h' : Binds U o x t') : t = t' := by
  cases h with
  | type hs =>
    cases h' with
    | type _ => rfl
    | use hs' _ _ => exact absurd (hs.symm.trans hs') (by simp)
  | use hs hr hd =>
    cases h' with
    | type hs' => exact absurd (hs.symm.trans hs') (by simp)
    | use hs' hr' hd' =>
      have e : Src.use _ _ = Src.use _ _ := Option.some.inj (hs.symm.trans hs')
      obtain ⟨rfl, rfl⟩ := Src.use.inj e
      exact hd.det (hr.det hr' ▸ hd')

end Silmaril.Wasm.Wit
