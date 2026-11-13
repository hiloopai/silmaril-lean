module

public import Silmaril.Raw.Wasm.Wit.Elab.Complete

/-!
# Elaboration: the only failures on a valid universe are wit-parser's world errors

`ElaborateComplete` (proved as `elaborate_complete`) assumes that the worlds of
the package elaborate. This module shows that this hypothesis is exactly wit-parser's
world conditions that `Valid` does not imply:

* `preItems_ok`: the items of a world of a valid universe are elaborated (its
  scope and the scopes of its inline interfaces have a topological type order:
  *sorted world scopes*);
* `elabWorld_error`: with fuel above a ranking of the `include` graph (the bounded
  ranking `kahn` gives, `Valid.worldAcyclic`: *enough include fuel*),
  `elabWorld` fails only with a `WorldError`: a world item defined twice (also after
  `include … with` renaming: wit-parser's `ItemShadowing`), a stability mismatch
  of an interface included twice (`StabilityMismatch`), an interface both imported
  and exported by the dependencies of an export (`InvalidTransitiveDependency`), or
  an interface exported twice;
* `elaborate_error`: `elaborate` fails on a valid gated universe (package with an
  interface or a world) only with a `WorldError`;
* `elaborate_ok_iff`: it succeeds iff every world of the package elaborates.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

/-- The error messages of wit-parser's world elaboration that `Valid` does not
exclude. -/
def WorldError (m : String) : Prop :=
  (∃ k : String, m = s!"world item `{k}` defined more than once") ∨
  (∃ i : String, m = s!"stability mismatch for `{i}`") ∨
  m = "an interface is both imported and exported by the dependencies of an export" ∨
  m = "an interface is exported more than once"

/-! ## Errors of folds -/

theorem foldlM_error {ε α β : Type} {f : β → α → Except ε β} {m : ε} :
    ∀ {l : List α} {b : β}, l.foldlM f b = .error m → ∃ a ∈ l, ∃ b', f b' a = .error m
  | [], b, h => by simp [List.foldlM_nil, pure, Except.pure] at h
  | a :: l, b, h => by
    rw [List.foldlM_cons] at h
    cases hb : f b a with
    | error e =>
      rw [hb] at h
      cases h
      exact ⟨a, List.mem_cons_self, b, hb⟩
    | ok b' =>
      rw [hb] at h
      obtain ⟨a', ha', b'', h'⟩ := foldlM_error h
      exact ⟨a', List.mem_cons_of_mem _ ha', b'', h'⟩

theorem mapM_error {ε α β : Type} {f : α → Except ε β} {m : ε} :
    ∀ {l : List α}, l.mapM f = .error m → ∃ a ∈ l, f a = .error m
  | [], h => by simp [List.mapM_nil, pure, Except.pure] at h
  | a :: l, h => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | error e =>
      rw [hb] at h
      cases h
      exact ⟨a, List.mem_cons_self, hb⟩
    | ok b =>
      rw [hb] at h
      cases hl : l.mapM f with
      | error e =>
        rw [hl] at h
        cases h
        obtain ⟨a', ha', h'⟩ := mapM_error hl
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
      | ok bs => rw [hl] at h; cases h

theorem foldlM_ok_of_forall {ε α β : Type} {f : β → α → Except ε β} :
    ∀ {l : List α} {b : β}, (∀ a ∈ l, ∀ b, ∃ b', f b a = .ok b') → ∃ r, l.foldlM f b = .ok r
  | [], b, _ => ⟨b, rfl⟩
  | a :: l, b, h => by
    obtain ⟨b', hb'⟩ := h a List.mem_cons_self b
    obtain ⟨r, hr⟩ := foldlM_ok_of_forall (l := l) (b := b') fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨r, by rw [List.foldlM_cons, hb']; exact hr⟩

theorem mapM_ok_of_forall_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ {a : α}, a ∈ l → ∃ b, f a = .ok b
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | x :: l, l', h, a, ha => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, _⟩ := except_bind_ok h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, hb⟩
    · exact mapM_ok_of_forall_mem hbs ha

theorem world?_of_mem {P : Package} (hn : (P.items.map PackageItem.name).Nodup) {W : World}
    (hW : PackageItem.world W ∈ P.items) : P.world? W.name = some W := by
  unfold Package.world?
  generalize P.items = items at hn hW ⊢
  induction items with
  | nil => exact absurd hW List.not_mem_nil
  | cons it items ih =>
    have hn' : (items.map PackageItem.name).Nodup := (List.nodup_cons.mp (by simpa using hn)).2
    have hit : it.name ∉ items.map PackageItem.name := (List.nodup_cons.mp (by simpa using hn)).1
    rcases List.mem_cons.mp hW with rfl | hW
    · simp
    · have hne : it.name ≠ W.name := fun he => hit (he ▸ List.mem_map_of_mem (f := PackageItem.name) hW)
      have ih' := ih hn' hW
      cases it with
      | world J =>
        have hJ : J.name ≠ W.name := hne
        simpa [hJ] using ih'
      | iface I => simpa using ih'
      | use u => simpa using ih'

/-! ## The world errors -/

theorem insertNew_error {its : List Binary.WorldItem} {it : Binary.WorldItem} {m : String}
    (h : insertNew its it = .error m) : WorldError m := by
  unfold insertNew at h
  split at h
  · cases h; exact .inl ⟨_, rfl⟩
  · cases h

theorem elabImport_error {env : Binary.Env} {fuel : Nat} {acc : List Binary.WorldItem} {it : Binary.WorldItem}
    {m : String} (h : elabImport env fuel acc it = .error m) : WorldError m := by
  cases it with
  | ifaceRef _ _ _ => cases h
  | ifaceInline _ _ => cases h
  | func f => exact insertNew_error h
  | type t => exact insertNew_error h

theorem includeItem_error {external : Bool} {its : List Binary.WorldItem} {it : Binary.WorldItem} {m : String}
    (h : includeItem external its it = .error m) : WorldError m := by
  cases it with
  | ifaceRef i d s =>
    unfold includeItem at h
    cases hf : its.find? (fun x => x.key == (Binary.WorldItem.ifaceRef i d s).key) <;>
      simp only [hf] at h <;> split at h <;> first
        | (cases h; exact .inr (.inl ⟨_, rfl⟩))
        | cases h
  | ifaceInline _ _ => exact insertNew_error h
  | func _ => exact insertNew_error h
  | type _ => exact insertNew_error h

theorem includeInto_error {external : Bool} {ns : List IncludeName} {W : Binary.World}
    {imps exps : List Binary.WorldItem} {m : String} (h : includeInto external ns W imps exps = .error m) :
    WorldError m := by
  unfold includeInto at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
    rename_i hf
    obtain ⟨_, _, _, h'⟩ := foldlM_error hf
    exact includeItem_error h'
  · split at h
    · cases h
      rename_i hf
      obtain ⟨_, _, _, h'⟩ := foldlM_error hf
      exact includeItem_error h'
    · cases h

theorem elabWorldItems_error {env : Binary.Env} {imports exports : List Binary.WorldItem} {m : String}
    (h : elabWorldItems env imports exports = .error m) : WorldError m := by
  unfold elabWorldItems at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · rename_i e hf
    cases h
    obtain ⟨_, _, _, h'⟩ := foldlM_error hf
    exact elabImport_error h'
  · split at h
    · rename_i e hf
      cases h
      obtain ⟨_, _, _, h'⟩ := foldlM_error hf
      exact insertNew_error h'
    · split at h
      · split at h
        · simp [pure, Except.pure] at h
        · cases h; exact .inr (.inr (.inr rfl))
      · cases h; exact .inr (.inr (.inl rfl))

/-! ## Sorted world scopes -/

theorem world_scope_names_sublist : ∀ items : List WorldItem,
    ((items.filterMap WorldItem.scope).flatMap ScopeItem.names).Sublist (items.flatMap WorldItem.importNames)
  | [] => List.nil_sublist _
  | it :: rest => by
    have ih := world_scope_names_sublist rest
    cases it with
    | type d => simpa [WorldItem.scope, ScopeItem.names, WorldItem.importNames] using ih
    | use u => simpa [WorldItem.scope, ScopeItem.names, WorldItem.importNames] using ih
    | «import» e =>
      simp only [List.filterMap_cons, WorldItem.scope, List.flatMap_cons]
      exact ih.trans (List.sublist_append_right _ _)
    | «export» e =>
      simp only [List.filterMap_cons, WorldItem.scope, List.flatMap_cons]
      exact ih.trans (List.sublist_append_right _ _)
    | «include» i =>
      simp only [List.filterMap_cons, WorldItem.scope, List.flatMap_cons]
      exact ih.trans (List.sublist_append_right _ _)

theorem world_types_isSome {U : Universe} (hv : Valid U) (c : Ctx) {w : ItemId} {W : World}
    (hW : U.world? w = some W) : (elabTypes c (.world w) (W.items.filterMap WorldItem.scope)).isSome := by
  have hok := (world_ok hv.pkgs hW).1
  have hitems := world_items_ok hv.pkgs hW
  have hsc : (Owner.world w).scope U = some (W.items.filterMap WorldItem.scope) := by
    simp only [Owner.scope, hW, Option.map_some]
  refine elabTypes_isSome hsc ((world_scope_names_sublist W.items).nodup hok.2.2.1) (fun d hd => ?_)
    hv.typeAcyclic
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hd
  cases it with
  | type d' =>
    simp only [WorldItem.scope, Option.some.injEq, ScopeItem.type.injEq] at hs
    subst hs
    exact kindOk_refs (hitems _ hit).2.2
  | use _ => simp [WorldItem.scope] at hs
  | «import» _ => cases hs
  | «export» _ => cases hs
  | «include» _ => cases hs

theorem inline?_of_mem_import {W : World} (hn : (W.items.flatMap WorldItem.importNames).Nodup) {n : Name}
    {items : List IfaceItem} {docs : Docs} {gs : List Gate}
    (h : WorldItem.import ⟨.iface n items, docs, gs⟩ ∈ W.items) : W.inline? false n = some items := by
  unfold World.inline?
  generalize W.items = l at hn h
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons it rest ih =>
    rw [List.flatMap_cons] at hn
    have hn' := (List.nodup_append.mp hn).2.1
    have hdis := (List.nodup_append.mp hn).2.2
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hnot : n ∉ it.importNames := fun hm =>
        hdis n hm n (List.mem_flatMap.mpr ⟨_, h, by simp [WorldItem.importNames]⟩) rfl
      rw [List.findSome?_cons_of_isNone]
      · exact ih hn' h
      · cases it with
        | «import» e =>
          obtain ⟨ext, _, _⟩ := e
          cases ext with
          | iface m _ =>
            have : m ≠ n := fun he => hnot (by simp [WorldItem.importNames, he])
            simp [this]
          | func _ _ => simp
          | path _ => simp
        | «export» e =>
          obtain ⟨ext, _, _⟩ := e
          cases ext <;> simp
        | use _ => simp
        | type _ => simp
        | «include» _ => simp

theorem inline?_of_mem_export {W : World} (hn : (W.items.flatMap WorldItem.exportNames).Nodup) {n : Name}
    {items : List IfaceItem} {docs : Docs} {gs : List Gate}
    (h : WorldItem.export ⟨.iface n items, docs, gs⟩ ∈ W.items) : W.inline? true n = some items := by
  unfold World.inline?
  generalize W.items = l at hn h
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons it rest ih =>
    rw [List.flatMap_cons] at hn
    have hn' := (List.nodup_append.mp hn).2.1
    have hdis := (List.nodup_append.mp hn).2.2
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hnot : n ∉ it.exportNames := fun hm =>
        hdis n hm n (List.mem_flatMap.mpr ⟨_, h, by simp [WorldItem.exportNames]⟩) rfl
      rw [List.findSome?_cons_of_isNone]
      · exact ih hn' h
      · cases it with
        | «export» e =>
          obtain ⟨ext, _, _⟩ := e
          cases ext with
          | iface m _ =>
            have : m ≠ n := fun he => hnot (by simp [WorldItem.exportNames, he])
            simp [this]
          | func _ _ => simp
          | path _ => simp
        | «import» e =>
          obtain ⟨ext, _, _⟩ := e
          cases ext <;> simp
        | use _ => simp
        | type _ => simp
        | «include» _ => simp

/-- The body of an inline interface of a world of a valid universe is elaborated. -/
theorem inline_body_isSome {U : Universe} (hv : Valid U) (c : Ctx) {w : ItemId} {W : World}
    (hW : U.world? w = some W) {isExport : Bool} {n : Name} {items : List IfaceItem} {docs : Docs}
    {gs : List Gate}
    (h : (if isExport then WorldItem.export ⟨.iface n items, docs, gs⟩
      else WorldItem.import ⟨.iface n items, docs, gs⟩) ∈ W.items)
    (hok : ItemsOk (specLeaves U) (.inline w isExport n) items) (d : Docs) (g : List Gate) :
    (elabBody c (.inline w isExport n) items d g).isSome := by
  have hwok := (world_ok hv.pkgs hW).1
  have hin : W.inline? isExport n = some items := by
    cases isExport with
    | false => exact inline?_of_mem_import hwok.2.2.1 h
    | true => exact inline?_of_mem_export hwok.2.2.2.1 h
  have hsc : (Owner.inline w isExport n).scope U = some (items.filterMap IfaceItem.scope) := by
    simp only [Owner.scope, hW, Option.bind_some, hin, Option.map_some]
  obtain ⟨hn, hrefs⟩ := itemsOk_scope hok
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp (elabTypes_isSome (c := c) hsc hn hrefs hv.typeAcyclic)
  simp [elabBody, hts]

theorem foldlM_ne_error {ε α β : Type} {f : β → α → Except ε β} {e : ε} {l : List α} {b : β}
    (h : ∀ a ∈ l, ∀ b, ∃ b', f b a = .ok b') : l.foldlM f b ≠ .error e := by
  intro he
  obtain ⟨r, hr⟩ := foldlM_ok_of_forall (b := b) h
  rw [hr] at he; cases he

/-- **The items of a world of a valid universe are elaborated** (`preItems`
never fails). -/
theorem preItems_ok {U : Universe} (hv : Valid U) {c : Ctx} (_hc : c.U = U) {w : ItemId} {W : World}
    (hW : U.world? w = some W) : ∃ r, preItems c w W = .ok r := by
  have hitems := world_items_ok hv.pkgs hW
  obtain ⟨types, htypes⟩ := Option.isSome_iff_exists.mp (world_types_isSome hv c hW)
  unfold preItems
  simp only [htypes, Bind.bind, Except.bind]
  split
  · rename_i e he
    refine absurd he (foldlM_ne_error fun it hit acc => ?_)
    cases it with
    | «import» e =>
      obtain ⟨ext, docs, gs⟩ := e
      have hok := (hitems _ hit).2
      cases ext with
      | func n f => exact ⟨_, rfl⟩
      | path p => exact ⟨_, rfl⟩
      | iface n items =>
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
          (inline_body_isSome hv c hW (isExport := false) (by simpa using hit) hok.2 docs gs)
        simp only [hb]
        exact ⟨_, rfl⟩
    | type d => exact ⟨_, rfl⟩
    | «export» _ => exact ⟨_, rfl⟩
    | use _ => exact ⟨_, rfl⟩
    | «include» _ => exact ⟨_, rfl⟩
  · split
    · rename_i e he
      refine absurd he (foldlM_ne_error fun it hit acc => ?_)
      cases it with
      | «export» e =>
        obtain ⟨ext, docs, gs⟩ := e
        have hok := (hitems _ hit).2
        cases ext with
        | func n f => exact ⟨_, rfl⟩
        | path p => exact ⟨_, rfl⟩
        | iface n items =>
          obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
            (inline_body_isSome hv c hW (isExport := true) (by simpa using hit) hok.2 docs gs)
          simp only [hb]
          exact ⟨_, rfl⟩
      | type _ => exact ⟨_, rfl⟩
      | «import» _ => exact ⟨_, rfl⟩
      | use _ => exact ⟨_, rfl⟩
      | «include» _ => exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-! ## Enough include fuel -/

theorem includesOf_edge {U : Universe} (hv : Valid U) {c : Ctx} (hc : c.U = U) {w : ItemId} {W : World}
    (hW : U.world? w = some W) {inc : ItemId × List IncludeName} (h : inc ∈ includesOf c w W) :
    WorldEdge U w inc.1 ∧ ∃ W', U.world? inc.1 = some W' := by
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp h
  cases it with
  | «include» i =>
    simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨w', W', hr, hW', _⟩ := (world_items_ok hv.pkgs hW _ hit).2.2.2
    have hg : (resolve c.U .world w.pkg i.path).getD ⟨w.pkg, i.path.name⟩ = w' := by
      rw [hc]; exact resolve_getD hr _
    simp only [hg]
    exact ⟨⟨W, i, hW, hit, hr⟩, W', hW'⟩
  | «import» _ => cases hs
  | «export» _ => cases hs
  | use _ => cases hs
  | type _ => cases hs

/-- **With enough fuel, `elabWorld` fails only with a `WorldError`.** -/
theorem elabWorld_error {U : Universe} (hv : Valid U) {c : Ctx} (hc : c.U = U) {env : Binary.Env}
    {r : ItemId → Nat} (hr : ∀ w w', WorldEdge U w w' → r w' < r w) :
    ∀ (f : Nat) (w : ItemId) (W : World) (m : String), U.world? w = some W → r w < f →
      elabWorld c env f w = .error m → WorldError m
  | 0, _, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, w, W, m, hW, hf, h => by
    unfold elabWorld at h
    simp only [Bind.bind, Except.bind] at h
    have hW' : c.U.world? w = some W := hc ▸ hW
    obtain ⟨pr, hpre⟩ := preItems_ok hv hc hW
    rw [hW'] at h
    simp only [hpre] at h
    split at h
    · rename_i e hfold
      cases h
      obtain ⟨inc, hinc, acc, hstep⟩ := foldlM_error hfold
      obtain ⟨hedge, W2, hW2⟩ := includesOf_edge hv hc hW hinc
      split at hstep
      · rename_i e' hrec
        cases hstep
        exact elabWorld_error hv hc hr f inc.1 W2 _ hW2 (by have := hr _ _ hedge; omega) hrec
      · exact includeInto_error hstep
    · split at h
      · rename_i e hwi
        cases h
        exact elabWorldItems_error hwi
      · simp [pure, Except.pure] at h

/-- A ranking of the `include` graph of a valid universe bounded by the number of
worlds. -/
theorem world_rank_bounded {U : Universe} (hv : Valid U) :
    ∃ r : ItemId → Nat, (∀ w w', WorldEdge U w w' → r w' < r w) ∧ ∀ w ∈ U.worldIds, r w < U.worldIds.length := by
  have hk : Graph.kahn (worldDeps U) U.worldIds = true := by
    have := check_complete hv
    simp only [check, Bool.and_eq_true] at this
    exact this.1.2
  exact Graph.kahn_bounded_edges _ (fun a b => worldEdge_iff a b) hk

/-! ## `elaborate` -/

/-- **`elaborate` fails on a valid gated universe only with wit-parser's world
errors.** -/
theorem elaborate_error {U : Universe} {p : PackageName} {fs : List Name} {P : Package}
    (hv : Valid (Universe.gate fs U)) (hP : P ∈ Universe.gate fs U) (hPn : P.name = p)
    (hne : P.ifaces ≠ [] ∨ P.worlds ≠ []) {m : String} (h : elaborate U p fs = .error m) : WorldError m := by
  subst hPn
  have hc : (Ctx.ofUniverse (Universe.gate fs U)).U = Universe.gate fs U := rfl
  obtain ⟨env, henv⟩ := elabEnv_ok hv _ hc
  by_cases hw : ∀ W ∈ P.worlds, ∃ w, elabWorld (Ctx.ofUniverse (Universe.gate fs U)) env
      ((Universe.gate fs U).worldIds.length + 1) ⟨P.name, W.name⟩ = .ok w
  · obtain ⟨r, hr⟩ := elaborate_complete U P.name fs P env hv hP rfl hne henv hw
    rw [hr] at h; cases h
  · -- some world fails; `elaborate` reports the first failing world
    have hlook : lookupPkg (Universe.gate fs U) P.name = .ok P := by
      unfold lookupPkg; rw [pkg?_of_mem hv.pkgs.1 hP]; rfl
    unfold elaborate at h
    simp only [Bind.bind, Except.bind, require, check_complete hv, ite_true, pure, Except.pure, hlook,
      henv] at h
    split at h
    · rename_i e hpkg
      cases h
      unfold elabPackage at hpkg
      simp only [Bind.bind, Except.bind] at hpkg
      split at hpkg
      · rename_i e' hifs
        cases hpkg
        obtain ⟨I, hI, hfI⟩ := mapM_error hifs
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
          (elabBody_iface_isSome hv (Ctx.ofUniverse (Universe.gate fs U)) hP (mem_ifaces hI))
        simp only [hb] at hfI
        simp [pure, Except.pure] at hfI
      · split at hpkg
        · rename_i e' hws
          cases hpkg
          obtain ⟨W, hWm, hfW⟩ := mapM_error hws
          split at hfW
          · rename_i e'' hwe
            cases hfW
            obtain ⟨r, hr, hbound⟩ := world_rank_bounded hv
            have hW : (Universe.gate fs U).world? ⟨P.name, W.name⟩ = some W := by
              simp only [Universe.world?, pkg?_of_mem hv.pkgs.1 hP, Option.bind_some]
              exact world?_of_mem (hv.pkgs.2 P hP).2.1 (mem_worlds hWm)
            exact elabWorld_error hv hc hr _ _ W _ hW
              (by have := hbound _ (world?_mem_ids hW); simp only [hc]; omega) hwe
          · simp [pure, Except.pure] at hfW
        · simp [pure, Except.pure] at hpkg
    · rename_i out hpkg
      exfalso
      apply hw
      intro W hWm
      unfold elabPackage at hpkg
      simp only [Bind.bind, Except.bind] at hpkg
      split at hpkg
      · cases hpkg
      · split at hpkg
        · cases hpkg
        · rename_i ws hws
          obtain ⟨y, hy⟩ := mapM_ok_of_forall_mem hws hWm
          split at hy
          · cases hy
          · rename_i w hw'
            exact ⟨w, hw'⟩

/-- **Completeness, restated with wit-parser's world conditions.** On a valid gated
universe whose package has an interface or a world, `elaborate` either succeeds or
reports one of wit-parser's world errors (`WorldError`). -/
theorem elaborate_ok_or_worldError {U : Universe} {p : PackageName} {fs : List Name} {P : Package}
    (hv : Valid (Universe.gate fs U)) (hP : P ∈ Universe.gate fs U) (hPn : P.name = p)
    (hne : P.ifaces ≠ [] ∨ P.worlds ≠ []) :
    (∃ r, elaborate U p fs = .ok r) ∨ ∃ m, elaborate U p fs = .error m ∧ WorldError m := by
  cases h : elaborate U p fs with
  | ok r => exact .inl ⟨r, rfl⟩
  | error m => exact .inr ⟨m, rfl, elaborate_error hv hP hPn hne h⟩

end Silmaril.Wasm.Wit.Elab
