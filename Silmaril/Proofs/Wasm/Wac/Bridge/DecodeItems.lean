module

public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeNamed.Thms

/-!
# WAC bridge: WIT packages of several items, proofs

* `comp_type_b`: `DecodeNamed.comp_type` in either sharing mode (worlds are encoded
  without sharing, `worldDef`);
* `iface_dec`, `world_dec`: the decoder reads an item's wrapper component type
  (`itemDef`) back as a component type exporting the interface or world;
* `items_dec`: the declarations a package of items projects to (`Wit.Project.itemDecls`)
  are read back by `decCDecls` as type exports, one per item;
* `project_itemsPackage`: the projection of the package (no type inference needed).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeEnc (ok_bind pure_ok)
open DecodeNamed

namespace DecodeItems

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

/-- A nominal table whose entries come from `N`. -/
def FromN (N : NomTable) (nt : NomTable) : Prop := ∀ p ∈ nt, N.lookup p.1 = some p.2

theorem nested_run' {b : Bool} {m : TM Unit} {σ s : Scope}
    (h : m.run { nom := σ.nom, share := b } = .ok ((), s)) : (nested b m).run' σ = .ok s.decls := by
  simp only [nested, StateT.run'_eq, StateT.run_bind, StateT.run_get, pure_bind, h]
  rfl

/-- **A component type of the fragment**, in either sharing mode. -/
theorem comp_type_b {N : NomTable} {is fs : Externs} (b : Bool) (h1 : EsOk N [] is)
    (h2 : EsOk N (extend [] is) fs) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ (C : List ComponentDecl) (δi : DScope),
      (nested b (do importDecls is; exportDecls fs)).run' { nom := N } = .ok C ∧
      (decDefType (.component C)).run δ =
        .ok (.comp (dks is) (dks fs), { δ with nom := δi.nom }) ∧ FromN N δi.nom := by
  obtain ⟨σa, Ea, δa, hra, hda, hma, hreadsa⟩ := (esOk_sim h1 _ _ (m_empty b δ hn)).1
  obtain ⟨σb, Eb, δb, hrb, hdb, hmb, hreadsb, -⟩ := (esOk_sim h2 _ _ hma).2
  have hdecls : σb.decls = Ea ++ Eb := by rw [hdb, hda]; simp
  have hb : (decCDecls (Eb ++ []) ([] ++ dks is) []).run δa =
      (decCDecls [] ([] ++ dks is) ([] ++ dks fs)).run δb := hreadsb [] _ []
  have hdec : (decCDecls (Ea ++ Eb) [] []).run { outer := δ.types :: δ.outer, nom := δ.nom } =
      .ok ((dks is, dks fs), δb) := by
    rw [hreadsa, ← List.append_nil Eb, hb]
    simp [decCDecls]
  refine ⟨Ea ++ Eb, δb, ?_, ?_, hmb.dnom⟩
  · rw [← hdecls]
    exact nested_run' (σ := { nom := N }) (by simp only [StateT.run_bind, hra]; exact hrb)
  · simp [decDefType, inNested, hdec]

/-- What the decoder reads an item's wrapper component type back as. -/
def infoP : PItem → TInfo
  | .iface id es => .comp [] [(id, .inst (ifaceId id) (dks es))]
  | .world id is es => .comp [] [(id, .comp (ifaceId id) (dks is) (dks es))]

/-- **An interface item** is read back as a component type exporting the interface. -/
theorem iface_dec {N : NomTable} {id : String} {es : Externs} (h : EsOk N [] es) {δ : DScope}
    (hn : FromN N δ.nom) :
    ∃ t, itemDef N (.iface id es) = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoP (.iface id es), { δ with nom := nom' }) ∧
      FromN N nom' := by
  obtain ⟨D, δi, hr, hd, hni⟩ := inst_type (esOk_sim h) (m_empty false δ hn)
  refine ⟨_, by simp only [itemDef, StateT.run'_eq, hr]; rfl, δi.nom, ?_, hni⟩
  rw [decDefType_norm, decDefType.eq_4]
  simp [inNested, decCDecls, decIDecl, hd, pushTy, decExtern, typeAt, infoP]

/-- **A world item** is read back as a component type exporting the world. -/
theorem world_dec {N : NomTable} {id : String} {is es : Externs} (h1 : EsOk N [] is)
    (h2 : EsOk N (extend [] is) es) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ t, itemDef N (.world id is es) = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoP (.world id is es), { δ with nom := nom' }) ∧
      FromN N nom' := by
  obtain ⟨C, δi, hr, hd, hni⟩ := comp_type_b false h1 h2
    (δ := { outer := δ.types :: δ.outer, nom := δ.nom }) hn
  refine ⟨_, by simp only [itemDef, hr]; rfl, δi.nom, ?_, hni⟩
  rw [decDefType_norm, decDefType.eq_4]
  simp [inNested, decCDecls, decIDecl, hd, pushTy, decExtern, typeAt, infoP]

theorem item_dec {N : NomTable} {it : PItem} (h : it.Ok N) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ t, itemDef N it = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoP it, { δ with nom := nom' }) ∧
      FromN N nom' := by
  cases it with
  | iface id es => exact iface_dec h hn
  | world id is es => exact world_dec h.1 h.2 hn

theorem itemDef_isResource {N : NomTable} {it : PItem} {t : DefType} (h : itemDef N it = .ok t) :
    Wit.Project.isResource t = false := by
  cases it with
  | iface id es =>
    simp only [itemDef] at h
    cases hx : (nested false (exportDecls es)).run' ({ nom := N } : Scope) with
    | error e => rw [hx] at h; cases h
    | ok ds => rw [hx] at h; cases h; rfl
  | world id is es =>
    simp only [itemDef] at h
    cases hx : (nested false (do importDecls is; exportDecls es)).run' ({ nom := N } : Scope) with
    | error e => rw [hx] at h; cases h
    | ok ds => rw [hx] at h; cases h; rfl

/-- The type export the decoder reads for an item. -/
def itemExt (p : String × PItem) : String × Kind := (p.1, .type (typeKind p.1 (infoP p.2)))

theorem namedInfo_infoP (n : String) (it : PItem) : namedInfo n (infoP it) = infoP it := by
  cases it <;> rfl

theorem addNom_infoP (n : String) (it : PItem) : addNom n (infoP it) = pure () := by
  cases it <;> rfl

theorem unwrap_typeKind (n : String) (it : PItem) : unwrapDef (typeKind n (infoP it)) = it.kind := by
  cases it <;> rfl

/-- **The declarations of a package of items** (as projected, `Wit.Project.itemDecls`)
are read back as one type export per item, from any decoder scope with `2 k` types. -/
theorem items_dec {N : NomTable} : ∀ (items : List (String × PItem)) (k : Nat) (δ : DScope)
    (es0 : Externs), (∀ p ∈ items, p.2.Ok N) → δ.types.size = 2 * k → FromN N δ.nom →
    ∃ defs, itemsDefs N items = .ok defs ∧ (∀ p ∈ defs, Wit.Project.isResource p.2 = false) ∧
      ∃ δ', (decCDecls (Wit.Project.itemDecls k defs) [] es0).run δ =
        .ok (([], es0 ++ items.map itemExt), δ') ∧ FromN N δ'.nom
  | [], _, δ, es0, _, _, hn => ⟨[], rfl, by simp, δ, by simp [Wit.Project.itemDecls, decCDecls], hn⟩
  | (n, it) :: rest, k, δ, es0, h, hs, hn => by
    obtain ⟨t, ht, nom', hd, hn'⟩ := item_dec (h _ List.mem_cons_self) hn
    let δ2 : DScope := { δ with types := (δ.types.push (infoP it)).push (infoP it), nom := nom' }
    obtain ⟨defs, hdefs, hres, δ', hdec, hn''⟩ := items_dec rest (k + 1) δ2 (es0 ++ [itemExt (n, it)])
      (fun p hp => h p (List.mem_cons_of_mem _ hp)) (by simp [δ2, hs]; omega) hn'
    have hat : (δ.types.push (infoP it))[2 * k]? = some (infoP it) := by
      rw [← hs]; simp
    refine ⟨(n, t) :: defs, by simp [itemsDefs, ht, hdefs], ?_, δ', ?_, hn''⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact itemDef_isResource ht
      · exact hres p hp
    · have e : es0 ++ ((n, it) :: rest).map itemExt = (es0 ++ [itemExt (n, it)]) ++ rest.map itemExt := by
        simp
      rw [e, ← hdec]
      simp only [Wit.Project.itemDecls, decCDecls, decIDecl, StateT.run_bind, hd]
      simp [pushTy, decExtern, typeAt, hat, namedInfo_infoP, addNom_infoP]
      rfl

theorem project_itemsPackage (defs : List (String × DefType)) (cs : List Section)
    (hr : ∀ p ∈ defs, Wit.Project.isResource p.2 = false) (hc : ∀ c ∈ cs, Wit.Project.isCode c = true) :
    Wit.Project.project (Wit.Project.itemsPackage defs cs) = some (Wit.Project.itemDecls 0 defs) := by
  simp only [Wit.Project.project, Wit.Project.itemsPackage, Ast.sections, List.flatMap_append,
    Wit.Project.replay_append, Wit.Project.replay_itemSecs 0 defs {} hr, Option.bind_some,
    Wit.Project.replay_customs _ cs hc, Option.map_some]
  simp

theorem pkgOfWorld_items {w : Wit.Project.WorldType} {items : List (String × PItem)} {δ' : DScope}
    (h : (decCDecls w [] []).run {} = .ok (([], [] ++ items.map itemExt), δ')) :
    pkgOfWorld w = .ok (itemsPkg items, δ'.nom) := by
  simp only [pkgOfWorld, h, ok_bind, pure_ok, itemsPkg, Except.ok.injEq, Prod.mk.injEq, and_true, List.nil_append]
  clear h
  induction items with
  | nil => rfl
  | cons p ps ih =>
    simp only [PkgType.mk.injEq, List.map_cons, List.filter_cons, List.filterMap_cons] at ih ⊢
    exact ⟨ih.1, by simp [itemExt, unwrap_typeKind, ih.2]⟩

end DecodeItems

end Silmaril.Wasm.Wac.Bridge

namespace Silmaril.Wasm.Wac.Bridge.DecodeItems

open Silmaril.Wasm.Component.Binary

theorem nested_run (b : Bool) (m : TM Unit) (σ : Scope) :
    (nested b m).run σ = (fun ds => (ds, σ)) <$> (nested b m).run' { nom := σ.nom } := by
  simp only [nested, StateT.run'_eq, StateT.run_bind, StateT.run_get, pure_bind]
  cases m.run { nom := σ.nom, share := b } with
  | ok p => rfl
  | error e => rfl

/-- **`itemDef` is what the encoder writes** for an interface (`ifaceDef`): one type
definition, the wrapper component type. -/
theorem ifaceDef_run {N : NomTable} {id : String} {es : Externs} {t : DefType}
    (ht : itemDef N (.iface id es) = .ok t) (σ : Scope) (hσ : σ.nom = N) :
    (ifaceDef id es).run σ = .ok (.type (.eq σ.ntypes),
      { σ with decls := σ.decls ++ [.inst (.type t)], ntypes := σ.ntypes + 1 }) := by
  simp only [itemDef] at ht
  cases hx : (nested false (exportDecls es)).run' ({ nom := N } : Scope) with
  | error e => rw [hx] at ht; cases ht
  | ok ds =>
    rw [hx] at ht; cases ht
    simp only [ifaceDef, StateT.run_bind, nested_run _ _ σ, hσ, hx]
    simp [nested, defTy, DecodeEnc.ok_bind, DecodeEnc.pure_ok, hσ]

/-- **`itemDef` is what the encoder writes** for a world (`worldDef`). -/
theorem worldDef_run {N : NomTable} {id : String} {is es : Externs} {t : DefType}
    (ht : itemDef N (.world id is es) = .ok t) (σ : Scope) (hσ : σ.nom = N) :
    (worldDef id is es).run σ = .ok (.type (.eq σ.ntypes),
      { σ with decls := σ.decls ++ [.inst (.type t)], ntypes := σ.ntypes + 1 }) := by
  simp only [itemDef] at ht
  cases hx : (nested false (do importDecls is; exportDecls es)).run' ({ nom := N } : Scope) with
  | error e => rw [hx] at ht; cases ht
  | ok ds =>
    rw [hx] at ht; cases ht
    simp only [worldDef, StateT.run_bind, nested_run _ _ σ, hσ, hx]
    simp [nested, defTy, DecodeEnc.ok_bind, DecodeEnc.pure_ok, hσ]

end Silmaril.Wasm.Wac.Bridge.DecodeItems
