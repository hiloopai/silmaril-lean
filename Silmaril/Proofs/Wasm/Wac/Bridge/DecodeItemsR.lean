module

public import Silmaril.Wasm.Wac.Bridge.DecodeItemsR.Defs
public import Silmaril.Wasm.Wac.Bridge.DecodeItems.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeRefVal.Thms

/-!
# WAC bridge: WIT packages of several items over `EsOkR`, proofs

The proofs of `Bridge.DecodeItems` with the simulation of `Bridge.DecodeRefVal`
(`esOkR_sim`, `inst_typeR`) in place of that of `Bridge.DecodeNamed`:

* `comp_type_bR`: a component type of the fragment in either sharing mode;
* `iface_decR`, `world_decR`, `item_decR`: an item's wrapper component type is read back;
* `items_decR`, `pkgOfWorld_itemsR`: the declarations of a package of items.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open DecodeEnc (ok_bind pure_ok)
open DecodeNamed (dks decDefType_norm throw_run)
open DecodeRefVal (EsOkR MR rdEs extendR esOkR_sim inst_typeR)
open DecodeItems (PItem FromN itemDef itemsDefs nested_run' itemDef_isResource)

namespace DecodeItemsR

attribute [local simp] ok_bind pure_ok Except.map_ok DecodeIface.okb DecodeIface.errb
  DecodeIface.err_bind throw_run

/-- The empty scope of a nested scope against `MR`. -/
theorem mr_empty {N : NomTable} (b : Bool) (δ : DScope) (hn : ∀ p ∈ δ.nom, N.lookup p.1 = some p.2) :
    MR N [] { nom := N, share := b } { outer := δ.types :: δ.outer, nom := δ.nom } :=
  ⟨DecodeNamed.m_empty b δ hn, fun _ _ h => absurd h (by simp)⟩

/-- **A component type of the fragment**, in either sharing mode. -/
theorem comp_type_bR {N : NomTable} {is fs : Externs} (b : Bool) (h1 : EsOkR N [] is)
    (h2 : EsOkR N (extendR [] is) fs) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ (C : List ComponentDecl) (δi : DScope),
      (nested b (do importDecls is; exportDecls fs)).run' { nom := N } = .ok C ∧
      (decDefType (.component C)).run δ =
        .ok (.comp (dks (rdEs [] is)) (dks (rdEs (extendR [] is) fs)), { δ with nom := δi.nom }) ∧
      FromN N δi.nom := by
  obtain ⟨σa, Ea, δa, hra, hda, hma, hreadsa⟩ := (esOkR_sim h1 _ _ (mr_empty b δ hn)).1
  obtain ⟨σb, Eb, δb, hrb, hdb, hmb, hreadsb, -⟩ := (esOkR_sim h2 _ _ hma).2
  have hdecls : σb.decls = Ea ++ Eb := by rw [hdb, hda]; simp
  have hb : (decCDecls (Eb ++ []) ([] ++ dks (rdEs [] is)) []).run δa =
      (decCDecls [] ([] ++ dks (rdEs [] is)) ([] ++ dks (rdEs (extendR [] is) fs))).run δb :=
    hreadsb [] _ []
  have hdec : (decCDecls (Ea ++ Eb) [] []).run { outer := δ.types :: δ.outer, nom := δ.nom } =
      .ok ((dks (rdEs [] is), dks (rdEs (extendR [] is) fs)), δb) := by
    rw [hreadsa, ← List.append_nil Eb, hb]
    simp [decCDecls]
  refine ⟨Ea ++ Eb, δb, ?_, ?_, hmb.m.dnom⟩
  · rw [← hdecls]
    exact nested_run' (σ := { nom := N }) (by simp only [StateT.run_bind, hra]; exact hrb)
  · simp [decDefType, inNested, hdec]

/-- What the decoder reads an item's wrapper component type back as. -/
def infoPR : PItem → TInfo
  | .iface id es => .comp [] [(id, .inst (ifaceId id) (dks (rdEs [] es)))]
  | .world id is es => .comp [] [(id, .comp (ifaceId id) (dks (rdEs [] is)) (dks (rdEs (extendR [] is) es)))]

theorem iface_decR {N : NomTable} {id : String} {es : Externs} (h : EsOkR N [] es) {δ : DScope}
    (hn : FromN N δ.nom) :
    ∃ t, itemDef N (.iface id es) = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoPR (.iface id es), { δ with nom := nom' }) ∧
      FromN N nom' := by
  obtain ⟨D, δi, hr, hd, hni⟩ := inst_typeR (esOkR_sim h) (mr_empty false δ hn)
  refine ⟨_, by simp only [itemDef, StateT.run'_eq, hr]; rfl, δi.nom, ?_, hni⟩
  rw [decDefType_norm, decDefType.eq_4]
  simp [inNested, decCDecls, decIDecl, hd, pushTy, decExtern, typeAt, infoPR]

theorem world_decR {N : NomTable} {id : String} {is es : Externs} (h1 : EsOkR N [] is)
    (h2 : EsOkR N (extendR [] is) es) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ t, itemDef N (.world id is es) = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoPR (.world id is es), { δ with nom := nom' }) ∧
      FromN N nom' := by
  obtain ⟨C, δi, hr, hd, hni⟩ := comp_type_bR false h1 h2
    (δ := { outer := δ.types :: δ.outer, nom := δ.nom }) hn
  refine ⟨_, by simp only [itemDef, hr]; rfl, δi.nom, ?_, hni⟩
  rw [decDefType_norm, decDefType.eq_4]
  simp [inNested, decCDecls, decIDecl, hd, pushTy, decExtern, typeAt, infoPR]

theorem item_decR {N : NomTable} {it : PItem} (h : okR N it) {δ : DScope} (hn : FromN N δ.nom) :
    ∃ t, itemDef N it = .ok t ∧ ∃ nom',
      (decDefType (Component.Wat.normDefType t)).run δ = .ok (infoPR it, { δ with nom := nom' }) ∧
      FromN N nom' := by
  cases it with
  | iface id es => exact iface_decR h hn
  | world id is es => exact world_decR h.1 h.2 hn

/-- The type export the decoder reads for an item. -/
def itemExtR (p : String × PItem) : String × Kind := (p.1, .type (typeKind p.1 (infoPR p.2)))

theorem namedInfo_infoPR (n : String) (it : PItem) : namedInfo n (infoPR it) = infoPR it := by
  cases it <;> rfl

theorem addNom_infoPR (n : String) (it : PItem) : addNom n (infoPR it) = pure () := by
  cases it <;> rfl

theorem unwrap_typeKindR (n : String) (it : PItem) : unwrapDef (typeKind n (infoPR it)) = kindR it := by
  cases it <;> rfl

/-- **The declarations of a package of items** are read back as one type export per item. -/
theorem items_decR {N : NomTable} : ∀ (items : List (String × PItem)) (k : Nat) (δ : DScope)
    (es0 : Externs), (∀ p ∈ items, okR N p.2) → δ.types.size = 2 * k → FromN N δ.nom →
    ∃ defs, itemsDefs N items = .ok defs ∧ (∀ p ∈ defs, Wit.Project.isResource p.2 = false) ∧
      ∃ δ', (decCDecls (Wit.Project.itemDecls k defs) [] es0).run δ =
        .ok (([], es0 ++ items.map itemExtR), δ') ∧ FromN N δ'.nom
  | [], _, δ, es0, _, _, hn => ⟨[], rfl, by simp, δ, by simp [Wit.Project.itemDecls, decCDecls], hn⟩
  | (n, it) :: rest, k, δ, es0, h, hs, hn => by
    obtain ⟨t, ht, nom', hd, hn'⟩ := item_decR (h _ List.mem_cons_self) hn
    let δ2 : DScope := { δ with types := (δ.types.push (infoPR it)).push (infoPR it), nom := nom' }
    obtain ⟨defs, hdefs, hres, δ', hdec, hn''⟩ := items_decR rest (k + 1) δ2 (es0 ++ [itemExtR (n, it)])
      (fun p hp => h p (List.mem_cons_of_mem _ hp)) (by simp [δ2, hs]; omega) hn'
    have hat : (δ.types.push (infoPR it))[2 * k]? = some (infoPR it) := by
      rw [← hs]; simp
    have hres' : ∀ p ∈ (n, t) :: defs, Wit.Project.isResource p.2 = false := fun p hp =>
      (List.mem_cons.1 hp).elim (fun e => e ▸ itemDef_isResource ht) (hres p)
    refine ⟨(n, t) :: defs, by simp [itemsDefs, ht, hdefs], hres', δ', ?_, hn''⟩
    have e : es0 ++ ((n, it) :: rest).map itemExtR = (es0 ++ [itemExtR (n, it)]) ++ rest.map itemExtR := by
      simp
    rw [e, ← hdec]
    simp only [Wit.Project.itemDecls, decCDecls, decIDecl, StateT.run_bind, hd]
    simp [pushTy, decExtern, typeAt, hat, namedInfo_infoPR, addNom_infoPR]
    rfl

theorem pkgOfWorld_itemsR {w : Wit.Project.WorldType} {items : List (String × PItem)} {δ' : DScope}
    (h : (decCDecls w [] []).run {} = .ok (([], [] ++ items.map itemExtR), δ')) :
    pkgOfWorld w = .ok (itemsPkgR items, δ'.nom) := by
  simp only [pkgOfWorld, h, ok_bind, pure_ok, itemsPkgR, Except.ok.injEq, Prod.mk.injEq, and_true, List.nil_append]
  clear h
  induction items with
  | nil => rfl
  | cons p ps ih =>
    simp only [PkgType.mk.injEq, List.map_cons, List.filter_cons, List.filterMap_cons] at ih ⊢
    exact ⟨ih.1, by simp [itemExtR, unwrap_typeKindR, ih.2]⟩

end DecodeItemsR

end Silmaril.Wasm.Wac.Bridge
