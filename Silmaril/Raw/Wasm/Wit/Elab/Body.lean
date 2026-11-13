module

public import Silmaril.Proofs.Wasm.Wit.Elab.Names
public import Silmaril.Proofs.Wasm.Wit.Elab.Scope

/-!
# Elaboration: bodies of a valid universe pass the binary checks

`elabBody_good`: the body an interface (or inline interface) of a valid universe
elaborates to passes `Interface.validB` and `Interface.namesUniqueB`, and the
interfaces its `use`s name pass `IfaceName.validB` (`BodyGood`).

* the type names of a scope are a permutation of the names it binds
  (`elabTypes_names_perm`), so they are distinct;
* every elaborated type is a `use`d name or the elaboration of a definition of the
  scope (`elabTypes_mem`), so its labels are distinct (`TypeGood`);
* functions are told apart by kind and name (`fkey`), and a valid function's mangled
  name determines both (`demangleChars_mangled`), so mangled names are distinct.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

/-! ## Good types, functions and bodies -/

/-- A type whose labels are distinct and whose `use`d interface has a valid name. -/
def TypeGood (td : Binary.TypeDef) : Prop :=
  labelsUniqueB td.kind = true ∧ ∀ j, typeDep td = some j → IfaceName.validB j = true

/-- A function whose names are plain identifiers; a constructor is named after its
resource and synchronous. -/
def FuncGood (f : Binary.Func) : Prop :=
  Plain f.name ∧ (∀ r, f.kind.resource? = some r → Plain r) ∧
    ∀ r, f.kind = .constructor r → f.name = r ∧ f.async = false

/-- A body that passes the binary checks, whose dependencies have valid names. -/
def BodyGood (b : Binary.Interface) : Prop :=
  Interface.validB b = true ∧ Interface.namesUniqueB b = true ∧
    ∀ j ∈ Binary.directDeps b, IfaceName.validB j = true

theorem FuncGood.validB {f : Binary.Func} (h : FuncGood f) : Func.validB f = true := by
  obtain ⟨hn, hr, hc⟩ := h
  unfold Func.validB
  cases hk : f.kind with
  | freestanding =>
    have := h_head hn
    simp [this]
  | method r =>
    have := not_mem_of_plain (hr r (by simp [hk, Binary.FuncKind.resource?])) plainChar_dot
    simpa using this
  | static r =>
    have := not_mem_of_plain (hr r (by simp [hk, Binary.FuncKind.resource?])) plainChar_dot
    simpa using this
  | constructor r =>
    obtain ⟨h1, h2⟩ := hc r hk
    simp [h1, h2]
where
  h_head {s : String} (h : Plain s) : (s.toList.head? != some '[') = true := by
    simpa using Plain.head_ne h

theorem FuncGood.valid {f : Binary.Func} (h : FuncGood f) : f.Valid := Func.validB_sound h.validB

theorem mem_directDeps {b : Binary.Interface} {j : Binary.IfaceName} (h : j ∈ Binary.directDeps b) :
    ∃ td ∈ b.types, typeDep td = some j := by
  unfold Binary.directDeps at h
  obtain ⟨td, htd, hj⟩ := List.mem_filterMap.mp h
  refine ⟨td, htd, ?_⟩
  obtain ⟨n, k, d, s⟩ := td
  simp only at hj
  split at hj
  · cases hj; rfl
  · cases hj

/-! ## Types of a scope -/

/-- The types a scope's `use`s define. -/
def useTypes (c : Ctx) (o : Owner) (items : List ScopeItem) : List Binary.TypeDef :=
  items.flatMap fun | .use u => elabUse c o u | .type _ => []

def useNames : List ScopeItem → List Name
  | [] => []
  | .use u :: rest => u.names.map UseName.bound ++ useNames rest
  | .type _ :: rest => useNames rest

def defNames : List ScopeItem → List Name
  | [] => []
  | .use _ :: rest => defNames rest
  | .type d :: rest => d.name :: defNames rest

theorem useTypes_names (c : Ctx) (o : Owner) : ∀ items : List ScopeItem,
    (useTypes c o items).map (·.name) = useNames items
  | [] => rfl
  | .use u :: rest => by
    have ih := useTypes_names c o rest
    simp only [useTypes, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp [useNames, elabUse]
  | .type d :: rest => by
    have ih := useTypes_names c o rest
    simp only [useTypes, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp [useNames]

theorem scopeEntries_defs (c : Ctx) (o : Owner) : ∀ items : List ScopeItem,
    ((scopeEntries c o items).filterMap (·.2.2)).map (·.name) = defNames items
  | [] => rfl
  | .use u :: rest => by
    have ih := scopeEntries_defs c o rest
    simp [scopeEntries, defNames, ← ih, List.filterMap_append]
  | .type d :: rest => by
    have ih := scopeEntries_defs c o rest
    simp [scopeEntries, defNames, ← ih, elabTypeDef]

theorem names_perm : ∀ items : List ScopeItem,
    (items.flatMap ScopeItem.names).Perm (useNames items ++ defNames items)
  | [] => .nil
  | .use u :: rest => by
    have ih := names_perm rest
    simp only [List.flatMap_cons, ScopeItem.names, useNames, defNames, List.append_assoc]
    exact ih.append_left _
  | .type d :: rest => by
    have ih := names_perm rest
    simp only [List.flatMap_cons, ScopeItem.names, useNames, defNames, List.singleton_append]
    exact (ih.cons d.name).trans List.perm_middle.symm

theorem elabTypes_some {c : Ctx} {o : Owner} {items : List ScopeItem} {ts : List Binary.TypeDef}
    (h : elabTypes c o items = some ts) : ∃ order,
      toposort (scopeEntries c o items).length [] (scopeEntries c o items) = some order ∧
        ts = useTypes c o items ++ order.filterMap (·.2.2) := by
  unfold elabTypes at h
  cases ho : toposort (scopeEntries c o items).length [] (scopeEntries c o items) with
  | none => simp [ho] at h
  | some order =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    exact ⟨order, rfl, h.symm⟩

/-- The type names of a scope are a permutation of the names it binds. -/
theorem elabTypes_names_perm {c : Ctx} {o : Owner} {items : List ScopeItem} {ts : List Binary.TypeDef}
    (h : elabTypes c o items = some ts) : (ts.map (·.name)).Perm (items.flatMap ScopeItem.names) := by
  obtain ⟨order, ho, rfl⟩ := elabTypes_some h
  have hp := toposort_perm _ _ _ _ ho
  have h1 : ((order.filterMap (·.2.2)).map (·.name)).Perm (defNames items) := by
    rw [← scopeEntries_defs c o items]
    exact (hp.filterMap _).map _
  rw [List.map_append, useTypes_names]
  exact (h1.append_left _).trans (names_perm items).symm

theorem scopeEntries_some {c : Ctx} {o : Owner} {td : Binary.TypeDef} : ∀ {items : List ScopeItem}
    {e : Entry}, e ∈ scopeEntries c o items → e.2.2 = some td →
      ∃ d, ScopeItem.type d ∈ items ∧ td = elabTypeDef c o d
  | [], _, h, _ => absurd h List.not_mem_nil
  | .type d :: rest, e, h, he => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨d, List.mem_cons_self, (Option.some.inj he).symm⟩
    · obtain ⟨d', hd', h'⟩ := scopeEntries_some h he
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩
  | .use u :: rest, e, h, he => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨un, _, rfl⟩ := List.mem_map.mp h
      cases he
    · obtain ⟨d', hd', h'⟩ := scopeEntries_some h he
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩

/-- An elaborated type is a `use`d name or a definition of the scope. -/
theorem elabTypes_mem {c : Ctx} {o : Owner} {items : List ScopeItem} {ts : List Binary.TypeDef}
    (h : elabTypes c o items = some ts) {td : Binary.TypeDef} (htd : td ∈ ts) :
    (∃ u, ScopeItem.use u ∈ items ∧ td ∈ elabUse c o u) ∨
      ∃ d, ScopeItem.type d ∈ items ∧ td = elabTypeDef c o d := by
  obtain ⟨order, ho, rfl⟩ := elabTypes_some h
  rcases List.mem_append.mp htd with h | h
  · obtain ⟨it, hit, hm⟩ := List.mem_flatMap.mp h
    cases it with
    | use u => exact .inl ⟨u, hit, hm⟩
    | type _ => exact absurd hm List.not_mem_nil
  · obtain ⟨e, he, hs⟩ := List.mem_filterMap.mp h
    exact .inr (scopeEntries_some ((toposort_perm _ _ _ _ ho).subset he) hs)

/-- Elaborated type expressions refer to local names only at the top. -/
theorem elabTy_ref {c : Ctx} {o : Owner} {t : Ty} {r : Binary.TyRef} (h : elabTy c o t = .ref r) :
    r.owner = .local := by
  cases t <;> simp only [elabTy, reduceCtorEq] at h
  case named n =>
    split at h
    · cases h
    · cases h; rfl

theorem typeDep_elabTypeDef (c : Ctx) (o : Owner) (d : TypeDef) : typeDep (elabTypeDef c o d) = none := by
  unfold elabTypeDef
  cases hk : d.kind with
  | «alias» t =>
    cases t with
    | named n => rfl
    | _ =>
      simp only [elabKind]
      cases he : elabTy c o _ with
      | ref r =>
        have := elabTy_ref he
        obtain ⟨ow, n⟩ := r
        simp only at this
        subst this
        rfl
      | _ => rfl
  | _ => rfl

theorem labelsUniqueB_elabKind {L : Leaves} {c : Ctx} {o : Owner} {k : TypeDefKind} (h : KindOk L o k) :
    labelsUniqueB (elabKind c o k) = true := by
  cases k with
  | «alias» t => cases t <;> rfl
  | record fs => simpa [elabKind, labelsUniqueB, List.map_map, Function.comp_def] using h.1.2.1
  | variant cs => simpa [elabKind, labelsUniqueB, List.map_map, Function.comp_def] using h.1.2.1
  | enum ls => simpa [elabKind, labelsUniqueB, List.map_map, Function.comp_def] using h.2.1
  | flags ls => simpa [elabKind, labelsUniqueB, List.map_map, Function.comp_def] using h.1.2.1
  | resource _ => rfl

/-- What the scope items of a valid owner give: `use` paths resolve to valid
interfaces, definitions have well-formed bodies. -/
def ScopeOk (U : Universe) (o : Owner) (si : ScopeItem) : Prop :=
  match si with
  | .use u => ∃ j, ResolvesTo U .iface o.pkg u.path j
  | .type d => ∃ L : Leaves, KindOk L o d.kind

theorem elabUse_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U)
    {o : Owner} {u : Use} (h : ∃ j, ResolvesTo U .iface o.pkg u.path j) {td : Binary.TypeDef}
    (htd : td ∈ elabUse c o u) : TypeGood td := by
  obtain ⟨j, hj⟩ := h
  unfold elabUse at htd
  obtain ⟨un, _, rfl⟩ := List.mem_map.mp htd
  refine ⟨rfl, fun j' hj' => ?_⟩
  simp only [typeDep, Option.some.injEq] at hj'
  subst hj'
  rw [hc, resolve_getD hj]
  have hv' := resolve_valid hv (resolve_complete hj)
  exact ifaceName_validB hv'.1 hv'.2

/-- **The types of a valid scope are good.** -/
theorem elabTypes_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U)
    {o : Owner} {items : List ScopeItem} (hok : ∀ si ∈ items, ScopeOk U o si) {ts : List Binary.TypeDef}
    (h : elabTypes c o items = some ts) : ∀ td ∈ ts, TypeGood td := by
  intro td htd
  rcases elabTypes_mem h htd with ⟨u, hu, hm⟩ | ⟨d, hd, rfl⟩
  · exact elabUse_good hv hc (hok _ hu) hm
  · obtain ⟨L, hk⟩ := hok _ hd
    exact ⟨labelsUniqueB_elabKind hk, fun j hj => by rw [typeDep_elabTypeDef] at hj; cases hj⟩

/-! ## Functions -/

/-- Kind and name: what tells functions of a body apart. -/
def fkey (f : Binary.Func) : Binary.FuncKind × String := (f.kind, f.name)

theorem nodup_map_of_nodup_map {α β γ : Type} {f : α → β} {k : α → γ} :
    ∀ {l : List α}, (l.map k).Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → k x = k y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, hk, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hk ⊢
    refine ⟨fun ⟨y, hy, he⟩ => hk.1 ⟨y, hy, (hf _ (List.mem_cons_of_mem _ hy) _ List.mem_cons_self he)⟩,
      nodup_map_of_nodup_map hk.2 fun a ha b hb => hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩

/-- Distinct kinds and names give distinct mangled names. -/
theorem mangled_nodup {fs : List Binary.Func} (hg : ∀ f ∈ fs, FuncGood f) (hn : (fs.map fkey).Nodup) :
    (fs.map Binary.Func.mangled).Nodup := by
  refine nodup_map_of_nodup_map hn fun f hf g hg' he => ?_
  have hc : f.mangledChars = g.mangledChars := by
    have := congrArg String.toList he
    simpa [Binary.Func.mangled] using this
  have h1 := Binary.demangleChars_mangled (hg f hf).valid
  have h2 := Binary.demangleChars_mangled (hg g hg').valid
  rw [hc, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  simp only [fkey, h1.1, String.toList_inj.mp h1.2.1.symm]

theorem elabResFunc_kind (c : Ctx) (o : Owner) (r : Name) (rf : ResourceFunc) :
    (elabResFunc c o r rf).kind.resource? = some r := by
  unfold elabResFunc
  cases rf.kind <;> rfl

/-- The key of a resource function. -/
theorem fkey_elabResFunc (c : Ctx) (o : Owner) (r : Name) (rf : ResourceFunc) :
    fkey (elabResFunc c o r rf) = match rf.kind with
      | .ctor => (.constructor r, r)
      | .method n => (.method r, n)
      | .static n => (.static r, n) := by
  unfold elabResFunc fkey
  cases rf.kind <;> rfl

theorem resFuncs_keys_nodup (c : Ctx) (o : Owner) (r : Name) : ∀ {fns : List ResourceFunc},
    (fns.filter fun rf => rf.kind == .ctor).length ≤ 1 → (fns.filterMap (·.kind.name?)).Nodup →
      ((fns.map (elabResFunc c o r)).map fkey).Nodup
  | [], _, _ => List.nodup_nil
  | rf :: fns, hc, hn => by
    have hc' : (fns.filter fun rf => rf.kind == .ctor).length ≤ 1 := by
      have := List.Sublist.length_le (List.Sublist.filter (fun rf : ResourceFunc => rf.kind == .ctor)
        (List.sublist_cons_self rf fns))
      omega
    have hn' : (fns.filterMap (·.kind.name?)).Nodup :=
      List.Nodup.sublist (List.Sublist.filterMap _ (List.sublist_cons_self rf fns)) hn
    have ih := resFuncs_keys_nodup c o r hc' hn'
    simp only [List.map_map, List.map_cons, List.nodup_cons] at ih ⊢
    refine ⟨?_, ih⟩
    intro hm
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hm
    simp only [Function.comp_apply, fkey_elabResFunc] at he
    cases hk : rf.kind with
    | ctor =>
      cases hgk : g.kind with
      | ctor =>
        have h2 : 2 ≤ ((rf :: fns).filter fun rf => rf.kind == .ctor).length := by
          simp only [List.filter_cons, hk, beq_self_eq_true, ite_true, List.length_cons]
          have : 0 < (fns.filter fun rf => rf.kind == .ctor).length :=
            List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by simp [hgk]⟩)
          omega
        omega
      | method n => rw [hk, hgk] at he; cases he
      | static n => rw [hk, hgk] at he; cases he
    | method n =>
      cases hgk : g.kind with
      | ctor => rw [hk, hgk] at he; cases he
      | static n' => rw [hk, hgk] at he; cases he
      | method n' =>
        rw [hk, hgk] at he
        simp only [Prod.mk.injEq] at he
        have hmem : n ∈ fns.filterMap (·.kind.name?) :=
          List.mem_filterMap.mpr ⟨g, hg, by simp [hgk, ResourceFuncKind.name?, he.2]⟩
        simp only [List.filterMap_cons, hk, ResourceFuncKind.name?, List.nodup_cons] at hn
        exact hn.1 hmem
    | static n =>
      cases hgk : g.kind with
      | ctor => rw [hk, hgk] at he; cases he
      | method n' => rw [hk, hgk] at he; cases he
      | static n' =>
        rw [hk, hgk] at he
        simp only [Prod.mk.injEq] at he
        have hmem : n ∈ fns.filterMap (·.kind.name?) :=
          List.mem_filterMap.mpr ⟨g, hg, by simp [hgk, ResourceFuncKind.name?, he.2]⟩
        simp only [List.filterMap_cons, hk, ResourceFuncKind.name?, List.nodup_cons] at hn
        exact hn.1 hmem

/-- The resource functions of a well-formed type definition are good and have
distinct keys. -/
theorem resFuncs_good {L : Leaves} {c : Ctx} {o : Owner} {d : TypeDef} (h : TypeDefOk L o d) :
    (∀ f ∈ resFuncs c o d, FuncGood f) ∧ ((resFuncs c o d).map fkey).Nodup := by
  unfold resFuncs
  obtain ⟨hn, _, hk⟩ := h
  cases hd : d.kind with
  | resource fns =>
    rw [hd] at hk
    refine ⟨fun f hf => ?_, resFuncs_keys_nodup c o d.name hk.1 hk.2.1⟩
    obtain ⟨rf, hrf, rfl⟩ := List.mem_map.mp hf
    have hrok := hk.2.2 rf hrf
    have hpn := plain_of_validId hn
    refine ⟨?_, fun r hr => ?_, fun r hr => ?_⟩
    · unfold elabResFunc
      cases hrk : rf.kind with
      | ctor => exact hpn
      | method m => exact plain_of_validId (hrok.2.1 m (by simp [hrk, ResourceFuncKind.name?]))
      | static m => exact plain_of_validId (hrok.2.1 m (by simp [hrk, ResourceFuncKind.name?]))
    · rw [elabResFunc_kind] at hr
      cases hr; exact hpn
    · unfold elabResFunc at hr ⊢
      cases hrk : rf.kind with
      | ctor =>
        simp only [hrk, Binary.FuncKind.constructor.injEq] at hr ⊢
        exact ⟨hr, trivial⟩
      | method m => simp [hrk] at hr
      | static m => simp [hrk] at hr
  | _ => exact ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

theorem itemFuncs_shape {c : Ctx} {o : Owner} {it : IfaceItem} {f : Binary.Func} (h : f ∈ itemFuncs c o it) :
    (∃ g, it = .func g ∧ f.kind = .freestanding ∧ f.name = g.name) ∨
      (∃ d, it = .type d ∧ f.kind.resource? = some d.name) := by
  cases it with
  | func g =>
    simp only [itemFuncs, List.mem_singleton] at h
    exact .inl ⟨g, rfl, by rw [h]; rfl, by rw [h]; rfl⟩
  | type d =>
    refine .inr ⟨d, rfl, ?_⟩
    simp only [itemFuncs, resFuncs] at h
    split at h
    · obtain ⟨rf, _, rfl⟩ := List.mem_map.mp h
      exact elabResFunc_kind c o d.name rf
    · exact absurd h List.not_mem_nil
  | use u => exact absurd h List.not_mem_nil

theorem itemFuncs_good {L : Leaves} {c : Ctx} {o : Owner} {it : IfaceItem} (h : IfaceItemOk L o it) :
    (∀ f ∈ itemFuncs c o it, FuncGood f) ∧ ((itemFuncs c o it).map fkey).Nodup := by
  cases it with
  | func g =>
    refine ⟨fun f hf => ?_, by simp [itemFuncs]⟩
    simp only [itemFuncs, List.mem_singleton] at hf
    subst hf
    refine ⟨plain_of_validId h.1, fun r hr => ?_, fun r hr => ?_⟩
    · simp [elabFunc, Binary.FuncKind.resource?] at hr
    · simp [elabFunc] at hr
  | type d => exact resFuncs_good h
  | use u => exact ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

/-- The functions of well-formed items are good and have distinct keys. -/
theorem funcs_good {L : Leaves} {c : Ctx} {o : Owner} {items : List IfaceItem} (h : ItemsOk L o items) :
    (∀ f ∈ items.flatMap (itemFuncs c o), FuncGood f) ∧ ((items.flatMap (itemFuncs c o)).map fkey).Nodup := by
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨it, hit, hf⟩ := List.mem_flatMap.mp hf
    exact (itemFuncs_good (h.2 it hit)).1 f hf
  · rw [List.map_flatMap]
    refine List.nodup_flatMap.mpr ⟨fun it hit => (itemFuncs_good (h.2 it hit)).2, ?_⟩
    have hp := (List.nodup_flatMap.mp h.1).2
    refine List.Pairwise.imp_of_mem ?_ hp
    intro a b ha hb hab x hxa hxb
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hxa
    obtain ⟨g, hg, hfg⟩ := List.mem_map.mp hxb
    simp only [fkey, Prod.mk.injEq] at hfg
    rcases itemFuncs_shape hf with ⟨fa, rfl, hk1, hn1⟩ | ⟨da, rfl, hr1⟩ <;>
      rcases itemFuncs_shape hg with ⟨fb, rfl, hk2, hn2⟩ | ⟨db, rfl, hr2⟩
    · have he : fa.name = fb.name := by rw [← hn1, ← hn2, hfg.2]
      exact (show List.Disjoint _ _ from hab) (a := fa.name) (by simp [IfaceItem.names])
        (by simp [IfaceItem.names, he])
    · rw [hfg.1, hk1] at hr2; cases hr2
    · rw [← hfg.1, hk2] at hr1; cases hr1
    · rw [hfg.1, hr1] at hr2
      exact (show List.Disjoint _ _ from hab) (a := da.name) (by simp [IfaceItem.names])
        (by simp [IfaceItem.names, Option.some.inj hr2])

/-! ## Bodies -/

/-- What the items of a valid owner give for its scope. -/
theorem itemsOk_scopeOk {U : Universe} {o : Owner} {items : List IfaceItem}
    (h : ItemsOk (specLeaves U) o items) : ∀ si ∈ items.filterMap IfaceItem.scope, ScopeOk U o si := by
  intro si hsi
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hsi
  cases it with
  | type d =>
    simp only [IfaceItem.scope, Option.some.injEq] at hs
    subst hs
    exact ⟨_, (h.2 _ hit).2.2⟩
  | use u =>
    simp only [IfaceItem.scope, Option.some.injEq] at hs
    subst hs
    exact (h.2 _ hit).2.1
  | func _ => cases hs

/-- **The body of well-formed items of a valid universe is good.** -/
theorem elabBody_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U)
    {o : Owner} {items : List IfaceItem} (h : ItemsOk (specLeaves U) o items) {d : Docs} {gs : List Gate}
    {b : Binary.Interface} (hb : elabBody c o items d gs = some b) : BodyGood b := by
  unfold elabBody at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
  obtain ⟨ts, hts, rfl⟩ := hb
  have htg := elabTypes_good hv hc (itemsOk_scopeOk h) hts
  have hfg := funcs_good (c := c) h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Interface.validB, List.all_eq_true]
    exact fun f hf => (hfg.1 f hf).validB
  · simp only [Interface.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨(elabTypes_names_perm hts).nodup_iff.mpr (itemsOk_scope h).1, mangled_nodup hfg.1 hfg.2⟩,
      fun td htd => (htg td htd).1⟩
  · intro j hj
    obtain ⟨td, htd, hj⟩ := mem_directDeps hj
    exact (htg td htd).2 j hj

end Silmaril.Wasm.Wit.Elab
