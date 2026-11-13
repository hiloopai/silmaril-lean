module

public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Wit.Elab.Thms

/-!
# WIT text: every valid document is printable

`printable_of_valid : Valid (d.packages ++ deps) → printable d = true`: the
identifiers of a valid document are `ValidId`, hence `idOk` (`idOk_of_validId`),
and its versions are valid, hence `verOk` (`verOk_of_valid`). References in types
and paths are covered through name resolution: a name bound in a scope is bound
by a valid definition or `use` (`binds_validId`), a resolved path names a valid
package and item (`pathOk_of_resolves`). So `parse_print` applies to every valid
document (`parse_print_of_valid`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Silmaril.Wasm.Wit.Elab (Universe.iface?_mem Universe.world?_mem has_valid)

/-! ## Types -/

mutual
theorem tyOk_of_refs : ∀ t : Ty, (∀ r ∈ t.refs, ValidId r.2) → tyOk t = true
  | .named n, h => by simpa [tyOk] using idOk_of_validId (h (.plain, n) (by simp [Ty.refs]))
  | .own n, h => by simpa [tyOk] using idOk_of_validId (h (.handle, n) (by simp [Ty.refs]))
  | .borrow n, h => by simpa [tyOk] using idOk_of_validId (h (.handle, n) (by simp [Ty.refs]))
  | .list t, h => by simp only [tyOk]; exact tyOk_of_refs t (by simpa [Ty.refs] using h)
  | .fixedList t _, h => by simp only [tyOk]; exact tyOk_of_refs t (by simpa [Ty.refs] using h)
  | .option t, h => by simp only [tyOk]; exact tyOk_of_refs t (by simpa [Ty.refs] using h)
  | .map a b, h => by
    simp only [tyOk, Bool.and_eq_true]
    exact ⟨tyOk_of_refs a fun r hr => h r (by simp [Ty.refs, hr]),
      tyOk_of_refs b fun r hr => h r (by simp [Ty.refs, hr])⟩
  | .tuple ts, h => by simp only [tyOk]; exact tysOk_of_refs ts (by simpa [Ty.refs] using h)
  | .result a b, h => by
    simp only [tyOk, Bool.and_eq_true]
    exact ⟨optOk_of_refs a fun r hr => h r (by simp [Ty.refs, hr]),
      optOk_of_refs b fun r hr => h r (by simp [Ty.refs, hr])⟩
  | .future t, h => by simp only [tyOk]; exact optOk_of_refs t (by simpa [Ty.refs] using h)
  | .stream t, h => by simp only [tyOk]; exact optOk_of_refs t (by simpa [Ty.refs] using h)
  | .bool, _ | .s8, _ | .s16, _ | .s32, _ | .s64, _ | .u8, _ | .u16, _ | .u32, _ | .u64, _
  | .f32, _ | .f64, _ | .char, _ | .string, _ | .errorContext, _ => rfl
theorem optOk_of_refs : ∀ t : Option Ty, (∀ r ∈ Ty.refsOpt t, ValidId r.2) → optOk t = true
  | none, _ => rfl
  | some t, h => by simp only [optOk]; exact tyOk_of_refs t h
theorem tysOk_of_refs : ∀ ts : List Ty, (∀ r ∈ Ty.refsList ts, ValidId r.2) → tysOk ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [tysOk, Bool.and_eq_true]
    exact ⟨tyOk_of_refs t fun r hr => h r (by simp [Ty.refsList, hr]),
      tysOk_of_refs ts fun r hr => h r (by simp [Ty.refsList, hr])⟩
end

/-! ## Names bound in scopes -/

theorem useName_bound_valid {un : UseName} (h1 : ValidId un.name) (h2 : ∀ a ∈ un.as, ValidId a) :
    ValidId un.bound := by
  unfold UseName.bound
  cases ha : un.as with
  | none => exact h1
  | some a => exact h2 a ha

/-- The names an interface item of a valid owner binds in its scope are valid. -/
theorem ifaceItem_scope_valid {L : Leaves} {o : Owner} {it : IfaceItem} (h : IfaceItemOk L o it)
    {si : ScopeItem} (hs : it.scope = some si) : ∀ x ∈ Elab.ScopeItem.names si, ValidId x := by
  cases it with
  | type d =>
    simp only [IfaceItem.scope, Option.some.injEq] at hs
    subst hs
    intro x hx
    simp only [Elab.ScopeItem.names, List.mem_singleton] at hx
    exact hx ▸ h.1
  | use u =>
    simp only [IfaceItem.scope, Option.some.injEq] at hs
    subst hs
    intro x hx
    obtain ⟨un, hun, rfl⟩ := List.mem_map.mp hx
    exact useName_bound_valid (h.2.2 un hun).1 (h.2.2 un hun).2.1
  | func _ => cases hs

theorem worldItem_scope_valid {L : Leaves} {w : ItemId} {it : WorldItem} (h : WorldItemOk L w it)
    {si : ScopeItem} (hs : it.scope = some si) : ∀ x ∈ Elab.ScopeItem.names si, ValidId x := by
  cases it with
  | type d =>
    simp only [WorldItem.scope, Option.some.injEq] at hs
    subst hs
    intro x hx
    simp only [Elab.ScopeItem.names, List.mem_singleton] at hx
    exact hx ▸ h.1
  | use u =>
    simp only [WorldItem.scope, Option.some.injEq] at hs
    subst hs
    intro x hx
    obtain ⟨un, hun, rfl⟩ := List.mem_map.mp hx
    exact useName_bound_valid (h.2.2 un hun).1 (h.2.2 un hun).2.1
  | «import» _ => cases hs
  | «export» _ => cases hs
  | «include» _ => cases hs

theorem inline?_mem {W : World} {e : Bool} {n : Name} {items : List IfaceItem} (h : W.inline? e n = some items) :
    ∃ docs gs, (if e then WorldItem.export ⟨.iface n items, docs, gs⟩
      else WorldItem.import ⟨.iface n items, docs, gs⟩) ∈ W.items := by
  unfold World.inline? at h
  obtain ⟨it, hit, hs⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | «import» x =>
    obtain ⟨ext, docs, gs⟩ := x
    cases ext with
    | iface m is =>
      by_cases hc : (!e) = true ∧ m = n
      · obtain ⟨he, rfl⟩ := hc
        have he' : e = false := by simpa using he
        subst he'
        have : is = items := by simpa using hs
        subst this
        exact ⟨docs, gs, by simpa using hit⟩
      · simp only [hc, ite_false] at hs; cases hs
    | func _ _ => simp at hs
    | path _ => simp at hs
  | «export» x =>
    obtain ⟨ext, docs, gs⟩ := x
    cases ext with
    | iface m is =>
      by_cases hc : e = true ∧ m = n
      · obtain ⟨he, rfl⟩ := hc
        subst he
        have : is = items := by simpa using hs
        subst this
        exact ⟨docs, gs, by simpa using hit⟩
      · simp only [hc, ite_false] at hs; cases hs
    | func _ _ => simp at hs
    | path _ => simp at hs
  | use _ => simp at hs
  | type _ => simp at hs
  | «include» _ => simp at hs

/-- The names bound in the scope of an owner of a valid universe are valid. -/
theorem scope_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {o : Owner} {sc : List ScopeItem}
    (h : o.scope U = some sc) : ∀ si ∈ sc, ∀ x ∈ Elab.ScopeItem.names si, ValidId x := by
  intro si hsi
  cases o with
  | iface i =>
    simp only [Owner.scope, Option.map_eq_some_iff] at h
    obtain ⟨I, hI, rfl⟩ := h
    obtain ⟨P, hP, _, hIm, _⟩ := Universe.iface?_mem hI
    have hok : InterfaceOk L P.name I := (hv.2 P hP).2.2 _ hIm
    obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hsi
    exact ifaceItem_scope_valid (hok.2.2.2 it hit) hs
  | world w =>
    simp only [Owner.scope, Option.map_eq_some_iff] at h
    obtain ⟨W, hW, rfl⟩ := h
    obtain ⟨P, hP, _, hWm, _⟩ := Universe.world?_mem hW
    have hok : WorldOk L P.name W := (hv.2 P hP).2.2 _ hWm
    obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hsi
    exact worldItem_scope_valid (hok.2.2.2.2 it hit) hs
  | inline w e n =>
    simp only [Owner.scope, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨items, ⟨W, hW, hin⟩, rfl⟩ := h
    obtain ⟨P, hP, _, hWm, _⟩ := Universe.world?_mem hW
    have hok : WorldOk L P.name W := (hv.2 P hP).2.2 _ hWm
    obtain ⟨docs, gs, hm⟩ := inline?_mem hin
    obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hsi
    have hitems : ItemsOk L (.inline ⟨P.name, W.name⟩ e n) items := by
      cases e with
      | false => exact (hok.2.2.2.2 (WorldItem.import ⟨.iface n items, docs, gs⟩) (by simpa using hm)).2.2
      | true => exact (hok.2.2.2.2 (WorldItem.export ⟨.iface n items, docs, gs⟩) (by simpa using hm)).2.2
    exact ifaceItem_scope_valid (hitems.2 it hit) hs

theorem src_names {sc : List ScopeItem} {x : Name} {s : Src} (h : sc.findSome? (·.src? x) = some s) :
    ∃ si ∈ sc, x ∈ Elab.ScopeItem.names si := by
  obtain ⟨si, hsi, hs⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨si, hsi, ?_⟩
  cases si with
  | type d =>
    by_cases hd : d.name = x
    · simp [Elab.ScopeItem.names, hd]
    · simp [ScopeItem.src?, hd] at hs
  | use u =>
    simp only [ScopeItem.src?, Option.map_eq_some_iff] at hs
    obtain ⟨un, hf, _⟩ := hs
    have hb : un.bound = x := by simpa using List.find?_some hf
    exact List.mem_map.mpr ⟨un, List.mem_of_find?_eq_some hf, hb⟩

/-- **A name bound in a scope of a valid universe is a valid identifier.** -/
theorem binds_validId {L : Leaves} {U : Universe} (hv : ValidWith L U) {o : Owner} {x : Name} {t : TypeId}
    (h : Binds U o x t) : ValidId x := by
  have hs : ∃ s, o.src? U x = some s := by
    cases h with
    | type hs => exact ⟨_, hs⟩
    | use hs _ _ => exact ⟨_, hs⟩
  obtain ⟨s, hs⟩ := hs
  unfold Owner.src? at hs
  obtain ⟨sc, hsc, hf⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨si, hsi, hx⟩ := src_names hf
  exact scope_valid hv hsc si hsi x hx

theorem tyOk_of_TyOk {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {t : Ty}
    (h : TyOk (specLeaves U) o t) : tyOk t = true :=
  tyOk_of_refs t fun r hr => (h.2 r hr).elim fun _ ⟨hb, _⟩ => binds_validId hv hb

theorem optOk_of_TyOk {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {t : Option Ty}
    (h : ∀ x ∈ t, TyOk (specLeaves U) o x) : optOk t = true := by
  cases t with
  | none => rfl
  | some t => exact tyOk_of_TyOk hv (h t rfl)

theorem funcOk_of_FuncOk {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {f : Func}
    (h : FuncOk (specLeaves U) o f) : funcOk f = true := by
  simp only [funcOk, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun p hp => ⟨idOk_of_validId (h.2.1 p hp).1, tyOk_of_TyOk hv (h.2.1 p hp).2⟩,
    optOk_of_TyOk hv fun x hx => (h.2.2 x hx).1⟩

/-! ## Gates and paths -/

theorem gatesOk_all {gs : List Gate} (h : GatesOk gs) : gs.all gateOk = true := by
  simp only [List.all_eq_true]
  intro g hg
  have := h.2 g hg
  cases g with
  | since v => exact verOk_of_valid this
  | deprecated v => exact verOk_of_valid this
  | unstable f => exact idOk_of_validId this

theorem pkgNameOk_of_valid {p : PackageName} (h : p.Valid) : pkgNameOk p = true := by
  simp only [pkgNameOk, Bool.and_eq_true]
  refine ⟨⟨idOk_of_validId h.1, idOk_of_validId h.2.1⟩, ?_⟩
  cases hv : p.version with
  | none => rfl
  | some v => exact verOk_of_valid (h.2.2 v hv)

theorem topUse?_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {p : PackageName} {n : Name}
    {path : UsePath} (h : U.topUse? p n = some path) : ValidId n := by
  unfold Universe.topUse? at h
  obtain ⟨P, hP, hu⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hPm, _⟩ := Elab.pkg?_mem hP
  unfold Package.topUse? at hu
  obtain ⟨it, hit, hs⟩ := List.exists_of_findSome?_eq_some hu
  cases it with
  | use u =>
    by_cases hb : u.bound = n
    · have hok := (hv.2 P hPm).2.2 _ hit
      exact hb ▸ hok.2.1
    · simp [hb] at hs
  | iface _ => simp at hs
  | world _ => simp at hs

/-- **A resolved path of a valid universe is printable.** -/
theorem pathOk_of_resolves {L : Leaves} {U : Universe} (hv : ValidWith L U) {k : Kind} {p : PackageName}
    {path : UsePath} {j : ItemId} (h : ResolvesTo U k p path j) : pathOk path = true := by
  cases h with
  | foreign hq =>
    have := has_valid hv hq
    simp only [pathOk, Bool.and_eq_true]
    exact ⟨pkgNameOk_of_valid this.1, idOk_of_validId this.2⟩
  | «local» hp =>
    simp only [pathOk]
    exact idOk_of_validId (has_valid hv hp).2
  | «alias» _ ht _ =>
    simp only [pathOk]
    exact idOk_of_validId (topUse?_valid hv ht)

/-! ## Items -/

theorem useOk_of_UseOk {U : Universe} (hv : ValidWith (specLeaves U) U) {p : PackageName} {u : Use}
    (h : UseOk (specLeaves U) p u) : useOk u = true := by
  simp only [useOk, Bool.and_eq_true, List.all_eq_true]
  obtain ⟨j, hj⟩ := h.2.1
  refine ⟨⟨List.all_eq_true.mp (gatesOk_all h.1), pathOk_of_resolves hv hj⟩, fun un hun => ⟨idOk_of_validId (h.2.2 un hun).1, ?_⟩⟩
  cases ha : un.as with
  | none => rfl
  | some a => exact idOk_of_validId ((h.2.2 un hun).2.1 a ha)

theorem typeDefOk_of_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {d : TypeDef}
    (h : TypeDefOk (specLeaves U) o d) : typeDefOk d = true := by
  simp only [typeDefOk, Bool.and_eq_true]
  refine ⟨⟨idOk_of_validId h.1, gatesOk_all h.2.1⟩, ?_⟩
  have hk := h.2.2
  cases hd : d.kind with
  | «alias» t => rw [hd] at hk; exact tyOk_of_TyOk hv hk
  | record fs =>
    rw [hd] at hk
    simp only [typeDefKindOk, List.all_eq_true, Bool.and_eq_true]
    exact fun f hf => ⟨idOk_of_validId (hk.1.2.2 _ (List.mem_map_of_mem hf)), tyOk_of_TyOk hv (hk.2 f hf)⟩
  | variant cs =>
    rw [hd] at hk
    simp only [typeDefKindOk, List.all_eq_true, Bool.and_eq_true]
    exact fun c hc => ⟨idOk_of_validId (hk.1.2.2 _ (List.mem_map_of_mem hc)), optOk_of_TyOk hv (hk.2 c hc)⟩
  | enum ls =>
    rw [hd] at hk
    simp only [typeDefKindOk, List.all_eq_true]
    exact fun l hl => idOk_of_validId (hk.2.2 _ (List.mem_map_of_mem hl))
  | flags ls =>
    rw [hd] at hk
    simp only [typeDefKindOk, List.all_eq_true]
    exact fun l hl => idOk_of_validId (hk.1.2.2 _ (List.mem_map_of_mem hl))
  | resource fns =>
    rw [hd] at hk
    simp only [typeDefKindOk, List.all_eq_true]
    intro rf hrf
    have hr := hk.2.2 rf hrf
    simp only [resFuncOk, Bool.and_eq_true]
    refine ⟨⟨gatesOk_all hr.1, funcOk_of_FuncOk hv hr.2.2.1⟩, ?_⟩
    cases hrk : rf.kind with
    | ctor => rfl
    | method n => exact idOk_of_validId (hr.2.1 n (by simp [hrk, ResourceFuncKind.name?]))
    | static n => exact idOk_of_validId (hr.2.1 n (by simp [hrk, ResourceFuncKind.name?]))

theorem ifaceItemOk_of_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {it : IfaceItem}
    (h : IfaceItemOk (specLeaves U) o it) : ifaceItemOk it = true := by
  cases it with
  | type d => exact typeDefOk_of_ok hv h
  | use u => exact useOk_of_UseOk hv h
  | func f =>
    simp only [ifaceItemOk, Bool.and_eq_true]
    exact ⟨⟨idOk_of_validId h.1, gatesOk_all h.2.1⟩, funcOk_of_FuncOk hv h.2.2⟩

theorem itemsOk_all {U : Universe} (hv : ValidWith (specLeaves U) U) {o : Owner} {items : List IfaceItem}
    (h : ItemsOk (specLeaves U) o items) : items.all ifaceItemOk = true :=
  List.all_eq_true.mpr fun it hit => ifaceItemOk_of_ok hv (h.2 it hit)

theorem externNames_valid {L : Leaves} {p : PackageName} {W : World} (h : WorldOk L p W) :
    ∀ n ∈ W.externNames, ValidId n := by
  intro n hn
  obtain ⟨it, hit, hm⟩ := List.mem_flatMap.mp hn
  have hok := h.2.2.2.2 it hit
  cases it with
  | «import» e =>
    obtain ⟨ext, _, _⟩ := e
    cases ext with
    | func m f => simp only [List.mem_singleton] at hm; exact hm ▸ hok.2.1
    | iface m is => simp only [List.mem_singleton] at hm; exact hm ▸ hok.2.1
    | path _ => simp at hm
  | «export» e =>
    obtain ⟨ext, _, _⟩ := e
    cases ext with
    | func m f => simp only [List.mem_singleton] at hm; exact hm ▸ hok.2.1
    | iface m is => simp only [List.mem_singleton] at hm; exact hm ▸ hok.2.1
    | path _ => simp at hm
  | use _ => simp at hm
  | type _ => simp at hm
  | «include» _ => simp at hm

theorem worldItemOk_of_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {w : ItemId} {it : WorldItem}
    (h : WorldItemOk (specLeaves U) w it) : worldItemOk it = true := by
  have hext : ∀ {b : Bool} {e : Extern}, ExternOk (specLeaves U) w b e → externOk e = true := by
    intro b e he
    cases e with
    | func n f =>
      simp only [externOk, Bool.and_eq_true]
      exact ⟨idOk_of_validId he.1, funcOk_of_FuncOk hv he.2⟩
    | iface n is =>
      simp only [externOk, Bool.and_eq_true]
      exact ⟨idOk_of_validId he.1, itemsOk_all hv he.2⟩
    | path p =>
      obtain ⟨j, hj⟩ := he
      exact pathOk_of_resolves hv hj
  cases it with
  | «import» e =>
    simp only [worldItemOk, Bool.and_eq_true]
    exact ⟨gatesOk_all h.1, hext h.2⟩
  | «export» e =>
    simp only [worldItemOk, Bool.and_eq_true]
    exact ⟨gatesOk_all h.1, hext h.2⟩
  | use u => exact useOk_of_UseOk hv h
  | type d => exact typeDefOk_of_ok hv h
  | «include» i =>
    simp only [worldItemOk, includeOk, Bool.and_eq_true, List.all_eq_true]
    obtain ⟨hg, _, has, w', W', hr, hW', hn⟩ := h
    obtain ⟨P, hP, _, hWm, _⟩ := Universe.world?_mem hW'
    have hwok : WorldOk (specLeaves U) P.name W' := (hv.2 P hP).2.2 _ hWm
    exact ⟨⟨List.all_eq_true.mp (gatesOk_all hg), pathOk_of_resolves hv hr⟩, fun m hm =>
      ⟨idOk_of_validId (externNames_valid hwok _ (hn _ (List.mem_map_of_mem hm))), idOk_of_validId (has m hm)⟩⟩

theorem packageOk_of_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {P : Package}
    (h : PackageOk (specLeaves U) P) : packageOk P = true := by
  simp only [packageOk, Bool.and_eq_true, List.all_eq_true]
  refine ⟨pkgNameOk_of_valid h.1, fun it hit => ?_⟩
  have hok := h.2.2 it hit
  cases it with
  | iface I =>
    simp only [packageItemOk, Bool.and_eq_true]
    exact ⟨⟨idOk_of_validId hok.1, gatesOk_all hok.2.1⟩, itemsOk_all hv hok.2.2⟩
  | world W =>
    simp only [packageItemOk, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨idOk_of_validId hok.1, List.all_eq_true.mp (gatesOk_all hok.2.1)⟩, fun x hx => worldItemOk_of_ok hv (hok.2.2.2.2 x hx)⟩
  | use u =>
    simp only [packageItemOk, Bool.and_eq_true]
    obtain ⟨hg, hb, _, hp⟩ := hok
    refine ⟨⟨gatesOk_all hg, ?_⟩, ?_⟩
    · rcases hp with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact pathOk_of_resolves hv hj
      · exact pathOk_of_resolves hv hj
    · cases ha : u.as with
      | none => rfl
      | some a =>
        have : u.bound = a := by simp [TopUse.bound, ha]
        exact idOk_of_validId (this ▸ hb)

/-- **Every valid document is printable**: in a valid universe with its
dependencies `deps`, the document's identifiers and versions are spelled by the
printer. -/
theorem printable_of_valid {d : Document} {deps : Universe} (h : Valid (d.packages ++ deps)) :
    printable d = true := by
  have hv := h.pkgs
  simp only [printable, Bool.and_eq_true, List.all_eq_true]
  refine ⟨packageOk_of_ok hv (hv.2 _ (by simp [Document.packages])), fun P hP =>
    packageOk_of_ok hv (hv.2 _ (by simp [Document.packages, hP]))⟩

/-- A document that passes `Document.check` is printable. -/
theorem printable_of_check {d : Document} {deps : Universe} (h : d.check deps = true) : printable d = true :=
  printable_of_valid (check_sound h)

/-- **The text round trip holds for every valid document.** -/
theorem parse_print_of_valid {d : Document} {deps : Universe} (h : Valid (d.packages ++ deps)) :
    parse (print d) = some (Document.norm d) :=
  parse_print d (printable_of_valid h)

/-! ## Valid documents are in normal form -/

theorem map_eq_self {α : Type} {f : α → α} {l : List α} (h : ∀ x ∈ l, f x = x) : l.map f = l :=
  (List.map_congr_left h).trans (List.map_id l)

theorem resFunc_norm_eq {L : Leaves} {o : Owner} {rf : ResourceFunc} (h : ResourceFuncOk L o rf) :
    ResourceFunc.norm rf = rf := by
  obtain ⟨k, ⟨ps, r, a⟩, d, g⟩ := rf
  cases k with
  | ctor =>
    have ha : a = false := (h.2.2.2 rfl).2
    subst ha
    rfl
  | method _ => rfl
  | static _ => rfl

theorem typeDef_norm_eq {L : Leaves} {o : Owner} {d : TypeDef} (h : TypeDefOk L o d) : TypeDef.norm d = d := by
  obtain ⟨n, k, docs, gs⟩ := d
  have hk := h.2.2
  cases k with
  | resource fns =>
    simp only [TypeDef.norm, TypeDefKind.norm]
    rw [map_eq_self fun rf hrf => resFunc_norm_eq (hk.2.2 rf hrf)]
  | «alias» _ => rfl
  | record _ => rfl
  | variant _ => rfl
  | enum _ => rfl
  | flags _ => rfl

theorem ifaceItem_norm_eq {L : Leaves} {o : Owner} {it : IfaceItem} (h : IfaceItemOk L o it) :
    IfaceItem.norm it = it := by
  cases it with
  | type d => simp only [IfaceItem.norm]; rw [typeDef_norm_eq h]
  | use _ => rfl
  | func _ => rfl

theorem worldItem_norm_eq {L : Leaves} {w : ItemId} {it : WorldItem} (h : WorldItemOk L w it) :
    WorldItem.norm it = it := by
  have hext : ∀ {b : Bool} {e : Extern}, ExternOk L w b e → Extern.norm e = e := by
    intro b e he
    cases e with
    | iface n is =>
      simp only [Extern.norm]
      rw [map_eq_self fun x hx => ifaceItem_norm_eq (he.2.2 x hx)]
    | func _ _ => rfl
    | path _ => rfl
  cases it with
  | «import» e => simp only [WorldItem.norm]; rw [hext h.2]
  | «export» e => simp only [WorldItem.norm]; rw [hext h.2]
  | type d => simp only [WorldItem.norm]; rw [typeDef_norm_eq h]
  | use _ => rfl
  | «include» _ => rfl

theorem package_norm_eq {L : Leaves} {P : Package} (h : PackageOk L P) : Package.norm P = P := by
  obtain ⟨name, docs, items⟩ := P
  simp only [Package.norm]
  rw [map_eq_self fun it hit => ?_]
  have hok := h.2.2 it hit
  cases it with
  | iface I =>
    simp only [PackageItem.norm]
    rw [map_eq_self fun x hx => ifaceItem_norm_eq (hok.2.2.2 x hx)]
  | world W =>
    simp only [PackageItem.norm]
    rw [map_eq_self fun x hx => worldItem_norm_eq (hok.2.2.2.2 x hx)]
  | use _ => rfl

/-- **A valid document is in the text normal form** (its constructors are not
`async`). -/
theorem norm_eq_of_valid {d : Document} {deps : Universe} (h : Valid (d.packages ++ deps)) :
    Document.norm d = d := by
  obtain ⟨main, nested⟩ := d
  have hv := h.pkgs
  simp only [Document.norm]
  rw [package_norm_eq (hv.2 main (by simp [Document.packages])),
    map_eq_self fun P hP => package_norm_eq (hv.2 P (by simp [Document.packages, hP]))]

/-- **The text round trip is exact on valid documents.** -/
theorem parse_print_valid {d : Document} {deps : Universe} (h : Valid (d.packages ++ deps)) :
    parse (print d) = some d := by
  rw [parse_print_of_valid h, norm_eq_of_valid h]

/-- Printing is injective on valid documents. -/
theorem print_injective_of_valid {d e : Document} {deps deps' : Universe} (hd : Valid (d.packages ++ deps))
    (he : Valid (e.packages ++ deps')) (h : print d = print e) : d = e := by
  have h1 := parse_print_valid hd
  rw [h, parse_print_valid he] at h1
  exact (Option.some.inj h1).symm

end Silmaril.Wasm.Wit.Text
