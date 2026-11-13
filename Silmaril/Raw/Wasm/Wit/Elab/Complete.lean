module

public import Silmaril.Raw.Wasm.Wit.Elab.World

/-!
# Elaboration: completeness

`elaborate_complete : ElaborateComplete`: on a valid (gated) universe whose
package has an interface or a world, `elaborate` succeeds as soon as the worlds of
the package elaborate. The binary checks `elaborate` makes on its output
(`Package.validB`, `Package.namesUniqueB`) always pass on such a universe:

* the environment is good and ranked (`elabEnv_good`, `elabEnv_ranked`): its
  bodies pass the checks (`elabBody_good`), and the `use` graph of a valid universe
  is acyclic, which ranks the interface ids (`ifaceName_id_inj`);
* world items are good before `elaborate_world` (`preItems_good`), `include`
  renames them into good items (`renameItem_good`, `includeInto_good`), and
  `elaborate_world` keeps them good with distinct keys (`elabWorldItems_good`), so
  every elaborated world passes the checks (`elabWorld_good`);
* interface and world names are distinct and valid in a valid package.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

/-! ## `include` renaming -/

/-- A renaming that keeps plain names plain. -/
def SigmaPlain (σ : String → String) : Prop := ∀ s, Plain s → Plain (σ s)

theorem renameBy_plain {ns : List IncludeName} (h : ∀ x ∈ ns, Plain x.as) : SigmaPlain (renameBy ns) := by
  intro s hs
  unfold renameBy
  cases hf : ns.find? (·.name = s) with
  | none => exact hs
  | some x => exact h x (List.mem_of_find?_eq_some hf)

theorem labelsUniqueB_renameKind (σ : String → String) (k : Binary.TyDefKind) :
    labelsUniqueB (renameKind σ k) = labelsUniqueB k := by
  cases k <;> simp [renameKind, labelsUniqueB, List.map_map, Function.comp_def]

theorem typeDep_rename (σ : String → String) (t : Binary.TypeDef) :
    typeDep { t with name := σ t.name, kind := renameKind σ t.kind } = typeDep t := by
  obtain ⟨n, k, d, s⟩ := t
  cases k with
  | type ty =>
    cases ty with
    | ref r =>
      obtain ⟨o, m⟩ := r
      cases o <;> rfl
    | _ => rfl
  | _ => rfl

theorem renameItem_good {σ : String → String} (hσ : SigmaPlain σ) {it : Binary.WorldItem} (h : ItemGood it) :
    ItemGood (renameItem σ it) := by
  cases it with
  | ifaceRef i d s => exact h
  | ifaceInline n b => exact ⟨hσ n h.1, h.2⟩
  | type t =>
    refine ⟨?_, fun j hj => h.2 j ?_⟩
    · simp only [labelsUniqueB_renameKind]; exact h.1
    · simpa only [renameItem, typeDep_rename] using hj
  | func f =>
    obtain ⟨hn, hr, hc⟩ := h
    simp only [renameItem]
    refine ⟨?_, fun r hr' => ?_, fun r hr' => ?_⟩
    · simp only [renameFunc]
      cases hk : f.kind with
      | freestanding => exact hσ _ hn
      | constructor r => exact hσ _ (hr r (by simp [hk, Binary.FuncKind.resource?]))
      | method r => exact hn
      | static r => exact hn
    · simp only [renameFunc] at hr'
      cases hk : f.kind with
      | freestanding => simp [hk, Binary.FuncKind.resource?] at hr'
      | constructor q =>
        simp only [hk, Binary.FuncKind.resource?, Option.some.injEq] at hr'
        exact hr' ▸ hσ _ (hr q (by simp [hk, Binary.FuncKind.resource?]))
      | method q =>
        simp only [hk, Binary.FuncKind.resource?, Option.some.injEq] at hr'
        exact hr' ▸ hσ _ (hr q (by simp [hk, Binary.FuncKind.resource?]))
      | static q =>
        simp only [hk, Binary.FuncKind.resource?, Option.some.injEq] at hr'
        exact hr' ▸ hσ _ (hr q (by simp [hk, Binary.FuncKind.resource?]))
    · simp only [renameFunc] at hr' ⊢
      cases hk : f.kind with
      | constructor q =>
        simp only [hk, Binary.FuncKind.constructor.injEq] at hr' ⊢
        exact ⟨hr', (hc q hk).2⟩
      | freestanding => simp [hk] at hr'
      | method q => simp [hk] at hr'
      | static q => simp [hk] at hr'

theorem map_good {g : Binary.WorldItem → Binary.WorldItem} (hg : ∀ y, ItemGood y → ItemGood (g y))
    {its : List Binary.WorldItem} (h : ∀ x ∈ its, ItemGood x) : ∀ x ∈ its.map g, ItemGood x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact hg y (h y hy)

theorem includeItem_good {external : Bool} {its its' : List Binary.WorldItem} {it : Binary.WorldItem}
    (h : ∀ x ∈ its, ItemGood x) (hg : ItemGood it) (hi : includeItem external its it = .ok its') :
    ∀ x ∈ its', ItemGood x := by
  cases it with
  | ifaceRef i d s =>
    have happ : ∀ x ∈ its ++ [Binary.WorldItem.ifaceRef i d s], ItemGood x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · rw [List.mem_singleton.mp hx]; exact hg
    unfold includeItem at hi
    cases hf : its.find? (fun x => x.key == (Binary.WorldItem.ifaceRef i d s).key) with
    | none =>
      simp only [hf] at hi
      split at hi
      · cases hi
      · simp only [pure, Except.pure, Except.ok.injEq] at hi
        subst hi
        refine map_good (fun y hy => ?_) happ
        cases y with
        | ifaceRef j d' _ => simp only; split <;> exact hy
        | _ => exact hy
    | some old =>
      simp only [hf] at hi
      split at hi
      · cases hi
      · simp only [pure, Except.pure, Except.ok.injEq] at hi
        subst hi
        refine map_good (fun y hy => ?_) h
        cases y with
        | ifaceRef j d' _ => simp only; split <;> exact hy
        | _ => exact hy
  | ifaceInline n b =>
    intro x hx
    rcases insertNew_mem hi x hx with hx | rfl
    · exact h x hx
    · exact hg
  | func f =>
    intro x hx
    rcases insertNew_mem hi x hx with hx | rfl
    · exact h x hx
    · exact hg
  | type t =>
    intro x hx
    rcases insertNew_mem hi x hx with hx | rfl
    · exact h x hx
    · exact hg

theorem includeInto_good {external : Bool} {ns : List IncludeName} {W : Binary.World}
    {imps exps imps' exps' : List Binary.WorldItem} (hns : ∀ x ∈ ns, Plain x.as)
    (hW : (∀ x ∈ W.imports, ItemGood x) ∧ ∀ x ∈ W.exports, ItemGood x)
    (hi : ∀ x ∈ imps, ItemGood x) (he : ∀ x ∈ exps, ItemGood x)
    (h : includeInto external ns W imps exps = .ok (imps', exps')) :
    (∀ x ∈ imps', ItemGood x) ∧ ∀ x ∈ exps', ItemGood x := by
  unfold includeInto at h
  obtain ⟨imps1, h1, h⟩ := except_bind_ok h
  obtain ⟨exps1, h2, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hσ := renameBy_plain hns
  refine ⟨foldlM_except_inv (fun b a b' ha hb hs => includeItem_good hb ?_ hs) hi h1,
    foldlM_except_inv (fun b a b' ha hb hs => includeItem_good hb ?_ hs) he h2⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact renameItem_good hσ (hW.1 x hx)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact renameItem_good hσ (hW.2 x hx)

/-! ## World items before `elaborate_world` -/

theorem world_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {w : ItemId} {W : World}
    (hW : U.world? w = some W) : WorldOk (specLeaves U) w.pkg W ∧ W.name = w.name := by
  obtain ⟨P, hP, hn, hWm, hWn⟩ := Universe.world?_mem hW
  have hok : WorldOk (specLeaves U) P.name W := (hv.2 P hP).2.2 _ hWm
  exact ⟨hn ▸ hok, hWn⟩

theorem world_items_ok {U : Universe} (hv : ValidWith (specLeaves U) U) {w : ItemId} {W : World}
    (hW : U.world? w = some W) : ∀ it ∈ W.items, WorldItemOk (specLeaves U) w it := by
  obtain ⟨hok, hn⟩ := world_ok hv hW
  have he : (⟨w.pkg, W.name⟩ : ItemId) = w := by rw [hn]
  exact he ▸ hok.2.2.2.2

theorem worldItems_scopeOk {U : Universe} {w : ItemId} {W : World}
    (hok : ∀ it ∈ W.items, WorldItemOk (specLeaves U) w it) :
    ∀ si ∈ W.items.filterMap WorldItem.scope, ScopeOk U (.world w) si := by
  intro si hsi
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hsi
  cases it with
  | type d =>
    simp only [WorldItem.scope, Option.some.injEq] at hs
    subst hs
    exact ⟨_, (hok _ hit).2.2⟩
  | use u =>
    simp only [WorldItem.scope, Option.some.injEq] at hs
    subst hs
    exact (hok _ hit).2.1
  | «import» _ => cases hs
  | «export» _ => cases hs
  | «include» _ => cases hs

/-- An import or export of a well-formed world elaborates to a good item. -/
theorem extern_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U) {w : ItemId}
    {isExport : Bool} {ext : Extern} (hok : ExternOk (specLeaves U) w isExport ext) {docs : Docs}
    {gates : List Gate} {x : Binary.WorldItem}
    (h : (match ext with
      | .func n f => (pure (.func (elabFunc c (.world w) n f docs gates)) : Except String Binary.WorldItem)
      | .iface n items =>
        match elabBody c (.inline w isExport n) items docs gates with
        | some b => pure (.ifaceInline n b)
        | none => throw s!"world `{w.name}`, `{n}`: cyclic or undefined types"
      | .path p => pure (.ifaceRef (ifaceName ((resolve c.U .iface w.pkg p).getD ⟨w.pkg, p.name⟩))
          docs.contents (stab gates))) = .ok x) : ItemGood x := by
  cases ext with
  | func n f =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨plain_of_validId hok.1, fun r hr => ?_, fun r hr => ?_⟩
    · simp [elabFunc, Binary.FuncKind.resource?] at hr
    · simp [elabFunc] at hr
  | iface n items =>
    simp only at h
    split at h
    · rename_i b hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨plain_of_validId hok.1, elabBody_good hv hc hok.2 hb⟩
    · cases h
  | path p =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨j, hj⟩ := hok
    show IfaceName.validB _ = true
    rw [hc, resolve_getD hj]
    have hv' := resolve_valid hv (resolve_complete hj)
    exact ifaceName_validB hv'.1 hv'.2

/-- **The items of a world of a valid universe are good before `elaborate_world`.** -/
theorem preItems_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U) {w : ItemId}
    {W : World} (hW : U.world? w = some W) {imps exps : List Binary.WorldItem}
    (h : preItems c w W = .ok (imps, exps)) : (∀ x ∈ imps, ItemGood x) ∧ ∀ x ∈ exps, ItemGood x := by
  have hitems := world_items_ok hv hW
  unfold preItems at h
  dsimp only at h
  split at h
  · rename_i types htypes
    have htg := elabTypes_good hv hc (worldItems_scopeOk hitems) htypes
    obtain ⟨imps0, h1, h⟩ := except_bind_ok h
    obtain ⟨exps0, h2, h⟩ := except_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨foldlM_except_inv (P := fun t => ∀ x ∈ t, ItemGood x) (fun b a b' ha hb hs => ?_) ?_ h1,
      foldlM_except_inv (P := fun t => ∀ x ∈ t, ItemGood x) (fun b a b' ha hb hs => ?_)
        (fun _ h => absurd h List.not_mem_nil) h2⟩
    · have hia := hitems a ha
      cases a with
      | «import» e =>
        simp only at hs
        obtain ⟨x, hx, hs⟩ := except_bind_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at hs
        subst hs
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hb y hy
        · rw [List.mem_singleton.mp hy]; exact extern_good hv hc hia.2 hx
      | type d =>
        simp only [pure, Except.pure, Except.ok.injEq] at hs
        subst hs
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hb y hy
        · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
          exact (resFuncs_good hia).1 f hf
      | «export» _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
      | use _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
      | «include» _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
    · intro x hx
      obtain ⟨td, htd, rfl⟩ := List.mem_map.mp hx
      exact htg td htd
    · have hia := hitems a ha
      cases a with
      | «export» e =>
        simp only at hs
        obtain ⟨x, hx, hs⟩ := except_bind_ok hs
        simp only [pure, Except.pure, Except.ok.injEq] at hs
        subst hs
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hb y hy
        · rw [List.mem_singleton.mp hy]; exact extern_good hv hc hia.2 hx
      | «import» _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
      | type _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
      | use _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
      | «include» _ => simp only [pure, Except.pure, Except.ok.injEq] at hs; exact hs ▸ hb
  · cases h

theorem includesOf_plain {U : Universe} {c : Ctx} {w : ItemId} {W : World}
    (hok : ∀ it ∈ W.items, WorldItemOk (specLeaves U) w it) {inc : ItemId × List IncludeName}
    (h : inc ∈ includesOf c w W) : ∀ x ∈ inc.2, Plain x.as := by
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp h
  cases it with
  | «include» i =>
    simp only [Option.some.injEq] at hs
    subst hs
    intro x hx
    exact plain_of_validId ((hok _ hit).2.2.1 x hx)
  | «import» _ => cases hs
  | «export» _ => cases hs
  | use _ => cases hs
  | type _ => cases hs

/-- **Every elaborated world of a valid universe passes the binary checks.** -/
theorem elabWorld_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U)
    {env : Binary.Env} {R : String → Nat} (hE : EnvGood env) (hR : EnvRanked env R) :
    ∀ (f : Nat) (w : ItemId) (W' : Binary.World), elabWorld c env f w = .ok W' →
      LInv W'.imports ∧ LInv W'.exports ∧ ∀ x ∈ W'.exports, x.isType = false
  | 0, _, _, h => by cases h
  | f + 1, w, W', h => by
    unfold elabWorld at h
    split at h
    · rename_i W hW
      have hW' : U.world? w = some W := hc ▸ hW
      obtain ⟨⟨imps, exps⟩, hpre, h⟩ := except_bind_ok h
      obtain ⟨⟨imps1, exps1⟩, hinc, h⟩ := except_bind_ok h
      obtain ⟨⟨imps2, exps2⟩, hwi, h⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hg1 : (∀ x ∈ imps1, ItemGood x) ∧ ∀ x ∈ exps1, ItemGood x := by
        refine foldlM_except_inv (P := fun p => (∀ x ∈ p.1, ItemGood x) ∧ ∀ x ∈ p.2, ItemGood x)
          (fun b a b' ha hb hs => ?_) (preItems_good hv hc hW' hpre) hinc
        obtain ⟨W2, hW2, hs⟩ := except_bind_ok hs
        have ih := elabWorld_good hv hc hE hR f a.1 W2 hW2
        exact includeInto_good (includesOf_plain (world_items_ok hv hW') ha)
          ⟨ih.1.1, ih.2.1.1⟩ hb.1 hb.2 hs
      exact elabWorldItems_good hE hR hg1.1 hg1.2 hwi
    · cases h

/-! ## The environment -/

theorem mapM_ok_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ b ∈ l', ∃ a ∈ l, f a = .ok b
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact fun _ hb => absurd hb List.not_mem_nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, hfx⟩ := mapM_ok_mem hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem mapM_ok_map {ε α β γ : Type} {f : α → Except ε β} {g : α → γ} {k : β → γ}
    (hk : ∀ a b, f a = .ok b → k b = g a) :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.map k = l.map g
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [List.map_cons, hk a b hb, mapM_ok_map hk hbs]

/-- An entry of the environment of a valid universe. -/
theorem elabEnv_entry {U : Universe} {c : Ctx} (hc : c.U = U) {env : Binary.Env} (h : elabEnv c = .ok env)
    {e : Binary.IfaceName × Binary.Interface} (he : e ∈ env) :
    ∃ P ∈ U, ∃ I, PackageItem.iface I ∈ P.items ∧ e.1 = ifaceName ⟨P.name, I.name⟩ ∧
      elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates = some e.2 := by
  unfold elabEnv at h
  obtain ⟨⟨p, I⟩, hpI, hf⟩ := mapM_ok_mem h e he
  obtain ⟨P, hP, hpI'⟩ := List.mem_flatMap.mp (hc ▸ hpI)
  obtain ⟨it, hit, hsome⟩ := List.mem_filterMap.mp hpI'
  cases it with
  | iface J =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨rfl, rfl⟩ := hsome
    simp only at hf
    split at hf
    · rename_i b hb
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      exact ⟨P, hP, J, hit, rfl, hb⟩
    · cases hf
  | world _ => cases hsome
  | use _ => cases hsome

theorem elabEnv_good {U : Universe} (hv : ValidWith (specLeaves U) U) {c : Ctx} (hc : c.U = U)
    {env : Binary.Env} (h : elabEnv c = .ok env) : EnvGood env := by
  intro e he
  obtain ⟨P, hP, I, hI, h1, h2⟩ := elabEnv_entry hc h he
  have hok : InterfaceOk (specLeaves U) P.name I := (hv.2 P hP).2.2 _ hI
  rw [h1]
  exact ⟨ifaceName_validB (hv.2 P hP).1 hok.1, elabBody_good hv hc hok.2.2 h2⟩

theorem mem_ifaceIds {U : Universe} {P : Package} (hP : P ∈ U) {I : Interface}
    (hI : PackageItem.iface I ∈ P.items) : (⟨P.name, I.name⟩ : ItemId) ∈ U.ifaceIds :=
  List.mem_flatMap.mpr ⟨P, hP, List.mem_filterMap.mpr ⟨_, hI, rfl⟩⟩

theorem ifaceIds_valid {L : Leaves} {U : Universe} (hv : ValidWith L U) {i : ItemId} (hi : i ∈ U.ifaceIds) :
    i.pkg.Valid ∧ ValidId i.name := by
  obtain ⟨P, hP, hm⟩ := List.mem_flatMap.mp hi
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp hm
  cases it with
  | iface I =>
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨(hv.2 P hP).1, ((hv.2 P hP).2.2 _ hit).1⟩
  | world _ => cases hs
  | use _ => cases hs

theorem has_iface_mem {U : Universe} {j : ItemId} (h : U.has .iface j = true) : j ∈ U.ifaceIds := by
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨P, hP, hn, hIm, hIn⟩ := Universe.iface?_mem hI
  have : j = ⟨P.name, I.name⟩ := by cases j; simp_all
  exact this ▸ mem_ifaceIds hP hIm

open Classical in
/-- The rank of an interface id: the rank of the interface of the universe it
names. -/
noncomputable def idRank (U : Universe) (r : ItemId → Nat) (s : String) : Nat :=
  if h : ∃ i ∈ U.ifaceIds, (ifaceName i).id = s then r (Classical.choose h) else 0

theorem idRank_eq {L : Leaves} {U : Universe} (hv : ValidWith L U) (r : ItemId → Nat) {i : ItemId}
    (hi : i ∈ U.ifaceIds) : idRank U r (ifaceName i).id = r i := by
  have hex : ∃ i' ∈ U.ifaceIds, (ifaceName i').id = (ifaceName i).id := ⟨i, hi, rfl⟩
  unfold idRank
  split
  · rename_i hex'
    obtain ⟨hm, he⟩ := Classical.choose_spec hex'
    have h1 := ifaceIds_valid hv hm
    have h2 := ifaceIds_valid hv hi
    rw [ifaceName_id_inj h1.1 h1.2 h2.1 h2.2 he]
  · exact absurd hex ‹_›

/-- **The environment of a valid universe is ranked by its acyclic `use` graph.** -/
theorem elabEnv_ranked {U : Universe} (hv : Valid U) {c : Ctx} (hc : c.U = U) {env : Binary.Env}
    (h : elabEnv c = .ok env) : ∃ R, EnvRanked env R := by
  obtain ⟨r, hr⟩ := hv.ifaceAcyclic
  refine ⟨idRank U r, fun e he j hj => ?_⟩
  obtain ⟨P, hP, I, hI, h1, h2⟩ := elabEnv_entry hc h he
  have hpk := hv.pkgs.2 P hP
  have hok : InterfaceOk (specLeaves U) P.name I := hpk.2.2 _ hI
  obtain ⟨td, htd, hdep⟩ := mem_directDeps hj
  unfold elabBody at h2
  obtain ⟨ts, hts, h2⟩ := Option.bind_eq_some_iff.mp h2
  simp only [Option.pure_def, Option.some.injEq] at h2
  rw [← h2] at htd
  rcases elabTypes_mem hts htd with ⟨u, hu, hm⟩ | ⟨d, _, rfl⟩
  · obtain ⟨it, hit, hsc⟩ := List.mem_filterMap.mp hu
    have hitu : it = .use u := by
      cases it with
      | use u' => simp only [IfaceItem.scope, Option.some.injEq, ScopeItem.use.injEq] at hsc; rw [hsc]
      | type _ => simp [IfaceItem.scope] at hsc
      | func _ => simp [IfaceItem.scope] at hsc
    subst hitu
    obtain ⟨j0, hj0⟩ := ((hok.2.2.2 _ hit).2.1)
    unfold elabUse at hm
    obtain ⟨un, _, rfl⟩ := List.mem_map.mp hm
    simp only [typeDep, Option.some.injEq] at hdep
    subst hdep
    have hU : U.iface? ⟨P.name, I.name⟩ = some I := by
      simp only [Universe.iface?, pkg?_of_mem hv.pkgs.1 hP, Option.bind_some]
      exact iface?_of_mem hpk.2.1 hI
    have hedge : IfaceEdge U ⟨P.name, I.name⟩ j0 := ⟨I, u, hU, hit, hj0⟩
    rw [h1, hc, resolve_getD hj0, idRank_eq hv.pkgs r (has_iface_mem (resolve_has (resolve_complete hj0))),
      idRank_eq hv.pkgs r (mem_ifaceIds hP hI)]
    exact hr _ _ hedge
  · rw [typeDep_elabTypeDef] at hdep; cases hdep

/-! ## Packages -/

theorem ifaces_names_sublist : ∀ items : List PackageItem,
    ((items.filterMap fun | .iface I => some I | _ => none).map (·.name)).Sublist (items.map PackageItem.name)
  | [] => List.nil_sublist _
  | it :: rest => by
    have ih := ifaces_names_sublist rest
    cases it with
    | iface I => simpa [PackageItem.name] using ih
    | world W => simpa using ih.cons _
    | use u => simpa using ih.cons _

theorem worlds_names_sublist : ∀ items : List PackageItem,
    ((items.filterMap fun | .world W => some W | _ => none).map (·.name)).Sublist (items.map PackageItem.name)
  | [] => List.nil_sublist _
  | it :: rest => by
    have ih := worlds_names_sublist rest
    cases it with
    | world W => simpa [PackageItem.name] using ih
    | iface I => simpa using ih.cons _
    | use u => simpa using ih.cons _

theorem mem_ifaces {P : Package} {I : Interface} (h : I ∈ P.ifaces) : PackageItem.iface I ∈ P.items := by
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp h
  cases it with
  | iface J => simp only [Option.some.injEq] at hs; exact hs ▸ hit
  | world _ => cases hs
  | use _ => cases hs

theorem mem_worlds {P : Package} {W : World} (h : W ∈ P.worlds) : PackageItem.world W ∈ P.items := by
  obtain ⟨it, hit, hs⟩ := List.mem_filterMap.mp h
  cases it with
  | world J => simp only [Option.some.injEq] at hs; exact hs ▸ hit
  | iface _ => cases hs
  | use _ => cases hs

theorem mapM_ne_error {ε α β : Type} {f : α → Except ε β} {e : ε} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → l.mapM f ≠ .error e := by
  intro l h he
  obtain ⟨l', hl'⟩ := mapM_ok_of_forall h
  rw [hl'] at he; cases he

/-- `elabPackage` succeeds when the interfaces and worlds do, and its output lists
them with their names. -/
theorem elabPackage_ok {c : Ctx} {env : Binary.Env} {P : Package}
    (hI : ∀ I ∈ P.ifaces, (elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates).isSome)
    (hW : ∀ W ∈ P.worlds, ∃ w, elabWorld c env (c.U.worldIds.length + 1) ⟨P.name, W.name⟩ = .ok w) :
    ∃ ifs ws, elabPackage c env P =
        .ok ({ name := pkgName P.name, docs := P.docs.contents, interfaces := ifs, worlds := ws } : Binary.Package) ∧
      (∀ nb ∈ ifs, ∃ I, PackageItem.iface I ∈ P.items ∧ nb.1 = I.name ∧
        elabBody c (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates = some nb.2) ∧
      (∀ nw ∈ ws, ∃ W, PackageItem.world W ∈ P.items ∧ nw.1 = W.name ∧
        elabWorld c env (c.U.worldIds.length + 1) ⟨P.name, W.name⟩ = .ok nw.2) ∧
      ifs.map (·.1) = P.ifaces.map (·.name) ∧ ws.map (·.1) = P.worlds.map (·.name) := by
  unfold elabPackage
  simp only [Bind.bind, Except.bind]
  split
  · rename_i e he
    refine absurd he (mapM_ne_error fun I hI' => ?_)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hI I hI')
    exact ⟨_, by simp only [hb]; rfl⟩
  · rename_i ifs hifs
    split
    · rename_i e he
      refine absurd he (mapM_ne_error fun W hW' => ?_)
      obtain ⟨w, hw⟩ := hW W hW'
      exact ⟨_, by simp only [hw]; rfl⟩
    · rename_i ws hws
      refine ⟨ifs, ws, rfl, fun nb hnb => ?_, fun nw hnw => ?_, ?_, ?_⟩
      · obtain ⟨I, hI', hf⟩ := mapM_ok_mem hifs nb hnb
        split at hf
        · rename_i b hb
          simp only [pure, Except.pure, Except.ok.injEq] at hf
          subst hf
          exact ⟨I, mem_ifaces hI', rfl, hb⟩
        · cases hf
      · obtain ⟨W, hW', hf⟩ := mapM_ok_mem hws nw hnw
        obtain ⟨w, hw, hf⟩ := except_bind_ok hf
        simp only [pure, Except.pure, Except.ok.injEq] at hf
        subst hf
        exact ⟨W, mem_worlds hW', rfl, hw⟩
      · refine mapM_ok_map (fun I b hf => ?_) hifs
        split at hf
        · simp only [pure, Except.pure, Except.ok.injEq] at hf; rw [← hf]
        · cases hf
      · refine mapM_ok_map (fun W b hf => ?_) hws
        obtain ⟨w, _, hf⟩ := except_bind_ok hf
        simp only [pure, Except.pure, Except.ok.injEq] at hf; rw [← hf]

/-- **Completeness of elaboration.** On a valid gated universe, the package `p`
with an interface or a world elaborates as soon as its worlds do: the binary
checks of `elaborate` never fail on a valid universe. -/
theorem elaborate_complete : ElaborateComplete := by
  intro U p fs P env hv hP hPn hne henv hworlds
  subst hPn
  have hvp := hv.pkgs
  have hc : (Ctx.ofUniverse (Universe.gate fs U)).U = Universe.gate fs U := rfl
  have hE := elabEnv_good hvp hc henv
  obtain ⟨R, hR⟩ := elabEnv_ranked hv hc henv
  have hpk := hvp.2 P hP
  obtain ⟨ifs, ws, hout, hifs_mem, hws_mem, hifs_names, hws_names⟩ :=
    elabPackage_ok (c := Ctx.ofUniverse (Universe.gate fs U)) (env := env) (P := P)
      (fun I hI => elabBody_iface_isSome hv _ hP (mem_ifaces hI)) hworlds
  have hifs_body : ∀ nb ∈ ifs, BodyGood nb.2 ∧ ValidId nb.1 := by
    intro nb hnb
    obtain ⟨I, hI, h1, h2⟩ := hifs_mem nb hnb
    have hok : InterfaceOk (specLeaves _) P.name I := hpk.2.2 _ hI
    exact ⟨elabBody_good hvp hc hok.2.2 h2, h1 ▸ hok.1⟩
  have hws_good : ∀ nw ∈ ws, (LInv nw.2.imports ∧ LInv nw.2.exports ∧ ∀ x ∈ nw.2.exports, x.isType = false) ∧
      ValidId nw.1 := by
    intro nw hnw
    obtain ⟨W, hW, h1, h2⟩ := hws_mem nw hnw
    have hok : WorldOk (specLeaves _) P.name W := hpk.2.2 _ hW
    exact ⟨elabWorld_good hvp hc hE hR _ _ _ h2, h1 ▸ hok.1⟩
  have hvalid : Package.validB { name := pkgName P.name, docs := P.docs.contents, interfaces := ifs, worlds := ws }
      (env.filter (·.1.pkg != pkgName P.name)) = true := by
    simp only [Package.validB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, List.all_eq_true]
    refine ⟨⟨⟨⟨?_, fun nb hnb => ?_⟩, fun nw hnw => ?_⟩, fun ib hib => ?_⟩, fun nw hnw => ?_⟩
    · rcases hne with h | h
      · exact .inl fun he => h (List.map_eq_nil_iff.mp (by rw [← hifs_names, he]; rfl))
      · exact .inr fun he => h (List.map_eq_nil_iff.mp (by rw [← hws_names, he]; rfl))
    · exact ifaceName_validB (i := ⟨P.name, nb.1⟩) hpk.1 (hifs_body nb hnb).2
    · exact ifaceName_validB (i := ⟨P.name, nw.1⟩) hpk.1 (hws_good nw hnw).2
    · simp only [Binary.Package.env, List.mem_append, List.mem_map, List.mem_filter] at hib
      rcases hib with ⟨nb, hnb, rfl⟩ | ⟨hib, _⟩
      · exact ⟨ifaceName_validB (i := ⟨P.name, nb.1⟩) hpk.1 (hifs_body nb hnb).2, (hifs_body nb hnb).1.1⟩
      · exact ⟨(hE ib hib).1, (hE ib hib).2.1⟩
    · obtain ⟨⟨hi, he, _⟩, _⟩ := hws_good nw hnw
      exact ⟨fun x hx => (hi.1 x hx).validB, fun x hx => (he.1 x hx).validB⟩
  have huniq : Package.namesUniqueB
      { name := pkgName P.name, docs := P.docs.contents, interfaces := ifs, worlds := ws } = true := by
    simp only [Package.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, fun nb hnb => (hifs_body nb hnb).1.2.1⟩, fun nw hnw => ?_⟩
    · rw [hifs_names]; exact (ifaces_names_sublist P.items).nodup hpk.2.1
    · rw [hws_names]; exact (worlds_names_sublist P.items).nodup hpk.2.1
    · obtain ⟨⟨hi, he, ht⟩, _⟩ := hws_good nw hnw
      exact world_namesUniqueB hi he ht
  have hlook : lookupPkg (Universe.gate fs U) P.name = .ok P := by
    unfold lookupPkg; rw [pkg?_of_mem hvp.1 hP]; rfl
  refine ⟨({ name := pkgName P.name, docs := P.docs.contents, interfaces := ifs, worlds := ws },
    env.filter (·.1.pkg != pkgName P.name)), ?_⟩
  unfold elaborate
  simp only [Bind.bind, Except.bind, require, check_complete hv, ite_true, pure, Except.pure, hlook, henv, hout,
    hvalid, huniq]

end Silmaril.Wasm.Wit.Elab
