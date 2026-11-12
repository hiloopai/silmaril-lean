module

public import Silmaril.Wasm.Wac.Bridge.TextX.Defs
public import Silmaril.Wasm.Wac.Bridge.Text.Thms
public import Silmaril.Wasm.Wac.FuncAlias.Thms

/-!
# WAC bridge with function type names: properties

* `ofDocX_isOk : isOk (ofDocX d) = okDocX d`, with one such equation per layer: the
  rejected documents are exactly those with world item, `use` or `include` paths WIT
  cannot express;
* `ofDocX_ok`: an accepted document maps statement by statement, with its package name
  and `targets` path;
* `ofDocX_ofDoc`: where `ofDoc` (WIT only) accepts, `ofDocX` gives its embedding
  `FuncAlias.ofDoc`; so `okDocX_of_okDoc`;
* **`elabDoc_ofDocX`**: on such documents the elaborator with function type names gives
  the graph of `Wac.elabDoc` (by `FuncAlias.elabDoc_ofDoc`), and `elabDocA_ofDocX`
  likewise up to aliases.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-! ## Acceptance -/

theorem ofIfaceItemX_isOk (i : Text.InterfaceItem) : isOk (ofIfaceItemX i) = okIfaceItemX i := by
  cases i with
  | use u => rw [ofIfaceItemX, isOk_map]; exact ofUse_isOk u
  | type d => rfl
  | export_ _ _ t => cases t <;> rfl

theorem ofIfaceItemsX_isOk (is : List Text.InterfaceItem) :
    isOk (ofIfaceItemsX is) = is.all okIfaceItemX := by
  rw [ofIfaceItemsX, isOk_mapM]; simp only [ofIfaceItemX_isOk]

theorem ofWorldPathX_isOk (imp : Bool) (p : Text.WorldItemPath) : isOk (ofWorldPathX imp p) = okWorldPathX p := by
  cases p with
  | named _ t =>
    cases t with
    | interface is => rw [ofWorldPathX, isOk_map]; exact ofIfaceItemsX_isOk is
    | _ => rfl
  | package p => rw [ofWorldPathX, isOk_map]; rfl
  | ident => rfl

theorem ofWorldItemX_isOk (i : Text.WorldItem) : isOk (ofWorldItemX i) = okWorldItemX i := by
  cases i with
  | use u => rw [ofWorldItemX, isOk_map]; exact ofUse_isOk u
  | «include» _ w ws => rw [ofWorldItemX, isOk_map]; exact ofInclude_isOk w ws
  | type d => rfl
  | import_ _ p => exact ofWorldPathX_isOk true p
  | export_ _ p => exact ofWorldPathX_isOk false p

theorem ofTypeStmtX_isOk (s : Text.TypeStatement) : isOk (ofTypeStmtX s) = okTypeStmtX s := by
  cases s with
  | interface _ _ is => rw [ofTypeStmtX, isOk_map]; exact ofIfaceItemsX_isOk is
  | world _ _ is => rw [ofTypeStmtX, isOk_map, isOk_mapM]; simp only [ofWorldItemX_isOk]; rfl
  | type d => rfl

theorem ofStmtX_isOk (s : Text.Statement) : isOk (ofStmtX s) = okStmtX s := by
  cases s with
  | import_ _ _ _ t =>
    cases t with
    | interface is => rw [ofStmtX, isOk_map]; exact ofIfaceItemsX_isOk is
    | _ => rfl
  | type s => exact ofTypeStmtX_isOk s
  | _ => rfl

/-- **Acceptance**: a document maps iff `okDocX` holds. -/
theorem ofDocX_isOk (d : Text.Document) : isOk (ofDocX d) = okDocX d := by
  rw [ofDocX, isOk_map, isOk_mapM, okDocX]; simp only [ofStmtX_isOk]

/-- **An accepted document maps statement by statement**, with its package name and its
`targets` path. -/
theorem ofDocX_ok {d : Text.Document} {d' : FuncAlias.Document} (h : ofDocX d = .ok d') :
    List.Forall₂ (fun s s' => ofStmtX s = .ok s') d.statements d'.stmts ∧
      d'.pkg = ofPkgName d.package ∧ d'.targets = d.targets.map ofPkgPath := by
  unfold ofDocX at h
  cases hm : d.statements.mapM ofStmtX with
  | error e => rw [hm] at h; cases h
  | ok ss =>
    rw [hm] at h
    have hd : d' = { pkg := ofPkgName d.package, targets := d.targets.map ofPkgPath, stmts := ss } := by
      cases h; rfl
    rw [hd]; exact ⟨mapM_forall₂ ofStmtX _ _ hm, rfl, rfl⟩

/-! ## Extending `ofDoc` -/

theorem mapM_map_of {ε α β γ : Type} (f : α → Except ε β) (g : α → Except ε γ) (h : β → γ)
    (hfg : ∀ x y, f x = .ok y → g x = .ok (h y)) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → xs.mapM g = .ok (ys.map h)
  | [], ys, e => by
    have : ys = [] := by simpa [List.mapM_nil, pure, Except.pure] using e.symm
    rw [this]; rfl
  | x :: xs, ys, e => by
    rw [List.mapM_cons] at e
    cases hx : f x with
    | error _ => rw [hx] at e; cases e
    | ok y =>
      cases hxs : xs.mapM f with
      | error _ => rw [hx, hxs] at e; cases e
      | ok ys' =>
        rw [hx, hxs] at e
        have hys : ys = y :: ys' := by cases e; rfl
        rw [hys, List.mapM_cons, hfg x y hx, mapM_map_of f g h hfg xs ys' hxs]; rfl

theorem ofTypeDeclX_of {d : Text.TypeDecl} {t : Wit.TypeDef} (h : ofTypeDecl d = .ok t) :
    ofTypeDeclX d = .inl t := by
  cases d with
  | «alias» _ _ k => cases k <;> (simp only [ofTypeDecl, reduceCtorEq] at h; try (cases h; rfl))
  | _ => cases h; rfl

theorem ofItemTypeDeclX_of {d : Text.ItemTypeDecl} {t : Wit.TypeDef} (h : ofItemTypeDecl d = .ok t) :
    ofItemTypeDeclX d = .inl t := by
  cases d with
  | resource => cases h; rfl
  | decl d => exact ofTypeDeclX_of h

theorem ofIfaceItemX_of {i : Text.InterfaceItem} {j : Wit.IfaceItem} (h : ofIfaceItem i = .ok j) :
    ofIfaceItemX i = .ok (.wit j) := by
  cases i with
  | use u =>
    simp only [ofIfaceItem] at h
    simp only [ofIfaceItemX]
    cases hu : ofUse u with
    | error _ => rw [hu] at h; cases h
    | ok u' => rw [hu] at h; cases h; rfl
  | type d =>
    simp only [ofIfaceItem] at h
    cases hd : ofItemTypeDecl d with
    | error _ => rw [hd] at h; cases h
    | ok t => rw [hd] at h; cases h; simp only [ofIfaceItemX, ofItemTypeDeclX_of hd]
  | export_ _ _ t =>
    cases t with
    | func f => cases h; rfl
    | ident _ => cases h

theorem ofIfaceItemsX_of {is : List Text.InterfaceItem} {js : List Wit.IfaceItem} (h : ofIfaceItems is = .ok js) :
    ofIfaceItemsX is = .ok (js.map .wit) :=
  mapM_map_of ofIfaceItem ofIfaceItemX _ (fun _ _ e => ofIfaceItemX_of e) is js h

theorem ofWorldPathX_of {imp : Bool} {p : Text.WorldItemPath} {e : Wit.Extern} (h : ofWorldPath p = .ok e) :
    ofWorldPathX imp p = .ok (FuncAlias.ofWorldItem (witExtern imp e)) := by
  cases p with
  | named id t =>
    cases t with
    | func f => cases h; cases imp <;> rfl
    | interface is =>
      simp only [ofWorldPath] at h
      cases hi : ofIfaceItems is with
      | error _ => rw [hi] at h; cases h
      | ok js =>
        rw [hi] at h; cases h
        simp only [ofWorldPathX, ofIfaceItemsX_of hi]
        cases imp <;> rfl
    | ident _ => cases h
  | package p =>
    simp only [ofWorldPath] at h
    cases hf : ofForeign p with
    | error _ => rw [hf] at h; cases h
    | ok q => rw [hf] at h; cases h; simp only [ofWorldPathX, hf]; cases imp <;> rfl
  | ident _ => cases h; cases imp <;> rfl

theorem map_ok {ε α β : Type} {f : α → β} {m : Except ε α} {b : β} (h : m.map f = .ok b) :
    ∃ a, m = .ok a ∧ b = f a := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, (Except.ok.inj h).symm⟩

theorem ofWorldItemX_of {i : Text.WorldItem} {j : Wit.WorldItem} (h : ofWorldItem i = .ok j) :
    ofWorldItemX i = .ok (FuncAlias.ofWorldItem j) := by
  cases i with
  | use u =>
    obtain ⟨u', hu, e⟩ : ∃ u', ofUse u = .ok u' ∧ j = .use u' := map_ok h
    rw [e]; simp only [ofWorldItemX, hu]; rfl
  | type d =>
    obtain ⟨t, hd, e⟩ : ∃ t, ofItemTypeDecl d = .ok t ∧ j = .type t := map_ok h
    rw [e]; simp only [ofWorldItemX, ofItemTypeDeclX_of hd]; rfl
  | import_ _ p =>
    obtain ⟨x, hp, e⟩ : ∃ x, ofWorldPath p = .ok x ∧ j = .import ⟨x, {}, []⟩ := map_ok h
    rw [e]; exact ofWorldPathX_of hp
  | export_ _ p =>
    obtain ⟨x, hp, e⟩ : ∃ x, ofWorldPath p = .ok x ∧ j = .export ⟨x, {}, []⟩ := map_ok h
    rw [e]; exact ofWorldPathX_of hp
  | «include» _ w ws =>
    obtain ⟨i, hi, e⟩ : ∃ i, ofInclude w ws = .ok i ∧ j = .include i := map_ok h
    rw [e]; simp only [ofWorldItemX, hi]; rfl

theorem ofTypeStmtX_of {s : Text.TypeStatement} {t : Syntax.TypeStmt} (h : ofTypeStmt s = .ok t) :
    ofTypeStmtX s = .ok (FuncAlias.ofStmt (.type t)) := by
  cases s with
  | interface _ id is =>
    obtain ⟨js, hi, e⟩ : ∃ js, ofIfaceItems is = .ok js ∧ t = .iface ⟨id, js, {}, []⟩ := map_ok h
    rw [e]; simp only [ofTypeStmtX, ofIfaceItemsX_of hi]; rfl
  | world _ id is =>
    obtain ⟨js, hw, e⟩ : ∃ js, is.mapM ofWorldItem = .ok js ∧ t = .world ⟨id, js, {}, []⟩ := map_ok h
    have hx : is.mapM ofWorldItemX = .ok (js.map FuncAlias.ofWorldItem) :=
      mapM_map_of ofWorldItem ofWorldItemX _ (fun _ _ e => ofWorldItemX_of e) is js hw
    rw [e]; simp only [ofTypeStmtX, hx]; rfl
  | type d =>
    obtain ⟨t', hd, e⟩ : ∃ t', ofTypeDecl d = .ok t' ∧ t = .type t' := map_ok h
    rw [e]; simp only [ofTypeStmtX, ofTypeDeclX_of hd, FuncAlias.ofStmt]

theorem ofStmtX_of {s : Text.Statement} {s' : Syntax.Stmt} (h : ofStmt s = .ok s') :
    ofStmtX s = .ok (FuncAlias.ofStmt s') := by
  cases s with
  | import_ _ id n ty =>
    cases ty with
    | interface is =>
      simp only [ofStmt, ofImportType] at h
      cases hi : ofIfaceItems is with
      | error _ => rw [hi] at h; cases h
      | ok js => rw [hi] at h; cases h; simp only [ofStmtX, ofIfaceItemsX_of hi]; rfl
    | _ => cases h; rfl
  | type t =>
    simp only [ofStmt] at h
    cases ht : ofTypeStmt t with
    | error _ => rw [ht] at h; cases h
    | ok t' => rw [ht] at h; cases h; exact ofTypeStmtX_of ht
  | let_ => cases h; rfl
  | export_ => cases h; rfl

/-- **`ofDocX` extends `ofDoc`**: where `ofDoc` accepts, `ofDocX` gives the embedding. -/
theorem ofDocX_ofDoc {d : Text.Document} {d' : Syntax.Document} (h : ofDoc d = .ok d') :
    ofDocX d = .ok (FuncAlias.ofDoc d') := by
  unfold ofDoc at h
  cases hm : d.statements.mapM ofStmt with
  | error _ => rw [hm] at h; cases h
  | ok ss =>
    rw [hm] at h; cases h
    unfold ofDocX
    rw [mapM_map_of ofStmt ofStmtX _ (fun _ _ e => ofStmtX_of e) _ ss hm]
    rfl

theorem okDocX_of_okDoc {d : Text.Document} (h : okDoc d = true) : okDocX d = true := by
  rw [← ofDoc_isOk] at h
  rw [← ofDocX_isOk]
  cases hd : ofDoc d with
  | error _ => rw [hd] at h; cases h
  | ok d' => rw [ofDocX_ofDoc hd]; rfl

/-- **Text to graphs, conservatively**: on a document `ofDoc` accepts, elaborating
`ofDocX` is elaborating `ofDoc`. -/
theorem elabDoc_ofDocX (env : PkgEnv) {d : Text.Document} {d' : Syntax.Document} (h : ofDoc d = .ok d') :
    (ofDocX d).map (FuncAlias.elabDoc env) = .ok (Wac.elabDoc env d') := by
  rw [ofDocX_ofDoc h, ← FuncAlias.elabDoc_ofDoc]; rfl

theorem elabDocA_ofDocX (env : PkgEnv) {d : Text.Document} {d' : Syntax.Document} (h : ofDoc d = .ok d') :
    (ofDocX d).map (FuncAlias.elabDocA env) = .ok (Wac.elabDocA env d') := by
  rw [ofDocX_ofDoc h, ← FuncAlias.elabDocA_ofDoc]; rfl

end Silmaril.Wasm.Wac.Bridge
