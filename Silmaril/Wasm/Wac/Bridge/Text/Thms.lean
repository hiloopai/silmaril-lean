module

public import Silmaril.Wasm.Wac.Bridge.Text.Defs

/-!
# WAC bridge: properties of the map from the text AST to the elaboration AST

* `ofExpr_toExpr`, `toExpr_ofExpr`: on expressions (and instantiation arguments) the
  map is a bijection; `ofArgs_toArgs`, `toArgs_ofArgs` for argument lists;
* `isOk_mapM`: a list maps when every element does;
* `ofDoc_isOk : isOk (ofDoc d) = okDoc d`, with one such equation per layer
  (`ofStmt_isOk`, `ofTypeStmt_isOk`, `ofWorldItem_isOk`, `ofIfaceItem_isOk`, …): the
  rejected documents are exactly those `okDoc` rejects, i.e. those with function type
  aliases or names, or world, `use` or `include` paths WIT cannot express;
* `ofDoc_ok`: an accepted document maps statement by statement (`List.Forall₂`), with
  the same package name and the same `targets` path;
* `ofDoc_comp`: a document without type statements and without inline interfaces is
  always accepted (compositions map totally).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm

/-! ## Expressions: a bijection -/

theorem ofPostfixes_append (e : Syntax.Expr) (ps : List Text.Postfix) (q : Text.Postfix) :
    ofPostfixes e (ps ++ [q]) = ofPostfix (ofPostfixes e ps) q := by
  induction ps generalizing e with
  | nil => rfl
  | cons p ps ih => exact ih (ofPostfix e p)

theorem ofExpr_postE (t : Text.Expr) (q : Text.Postfix) :
    ofExpr (postE t q) = ofPostfix (ofExpr t) q := by
  cases t with
  | mk p ps => simp only [postE, ofExpr, ofPostfixes_append]

mutual
/-- Text to syntax inverts syntax to text. -/
theorem ofExpr_toExpr : (e : Syntax.Expr) → ofExpr (toExpr e) = e
  | .ident _ => rfl
  | .new p as => by
    show Syntax.Expr.new ⟨p.name, p.version⟩ (ofArgs (toArgs as)) = _
    rw [ofArgs_toArgs as]
  | .paren e => by
    show Syntax.Expr.paren (ofExpr (toExpr e)) = _
    rw [ofExpr_toExpr e]
  | .access e x => by
    show ofExpr (postE (toExpr e) (.access x)) = _
    rw [ofExpr_postE, ofExpr_toExpr e]; rfl
  | .namedAccess e n => by
    show ofExpr (postE (toExpr e) (.namedAccess n)) = _
    rw [ofExpr_postE, ofExpr_toExpr e]; rfl
theorem ofArgs_toArgs : (as : List Syntax.Arg) → ofArgs (toArgs as) = as
  | [] => rfl
  | a :: as => by
    show ofArg (toArg a) :: ofArgs (toArgs as) = _
    rw [ofArg_toArg a, ofArgs_toArgs as]
theorem ofArg_toArg : (a : Syntax.Arg) → ofArg (toArg a) = a
  | .inferred _ | .spread _ | .fill => rfl
  | .named n e => by
    show Syntax.Arg.named (ofArgName (toArgName n)) (ofExpr (toExpr e)) = _
    rw [ofExpr_toExpr e]; cases n <;> rfl
end

/-- Appending postfix accesses one by one. -/
def postsE (t : Text.Expr) : List Text.Postfix → Text.Expr
  | [] => t
  | q :: qs => postsE (postE t q) qs

theorem toExpr_ofPostfix (e : Syntax.Expr) (q : Text.Postfix) :
    toExpr (ofPostfix e q) = postE (toExpr e) q := by
  cases q <;> rfl

theorem toExpr_ofPostfixes (e : Syntax.Expr) (ps : List Text.Postfix) :
    toExpr (ofPostfixes e ps) = postsE (toExpr e) ps := by
  induction ps generalizing e with
  | nil => rfl
  | cons q qs ih => rw [ofPostfixes, ih, toExpr_ofPostfix]; rfl

theorem postsE_mk (p : Text.Primary) (ps qs : List Text.Postfix) :
    postsE (.mk p ps) qs = .mk p (ps ++ qs) := by
  induction qs generalizing ps with
  | nil => simp only [postsE, List.append_nil]
  | cons q qs ih => rw [postsE, postE, ih]; simp only [List.append_assoc, List.cons_append, List.nil_append]

mutual
/-- Syntax to text inverts text to syntax. -/
theorem toExpr_ofExpr : (e : Text.Expr) → toExpr (ofExpr e) = e
  | .mk p ps => by
    show toExpr (ofPostfixes (ofPrimary p) ps) = _
    rw [toExpr_ofPostfixes, toExpr_ofPrimary p, postsE_mk]; rfl
theorem toExpr_ofPrimary : (p : Text.Primary) → toExpr (ofPrimary p) = .mk p []
  | .new p as => by
    show Text.Expr.mk (.new ⟨p.name, p.version⟩ (toArgs (ofArgs as))) [] = _
    rw [toArgs_ofArgs as]
  | .nested e => by
    show Text.Expr.mk (.nested (toExpr (ofExpr e))) [] = _
    rw [toExpr_ofExpr e]
  | .ident _ => rfl
theorem toArgs_ofArgs : (as : List Text.Arg) → toArgs (ofArgs as) = as
  | [] => rfl
  | a :: as => by
    show toArg (ofArg a) :: toArgs (ofArgs as) = _
    rw [toArg_ofArg a, toArgs_ofArgs as]
theorem toArg_ofArg : (a : Text.Arg) → toArg (ofArg a) = a
  | .inferred _ | .spread _ | .fill => rfl
  | .named n e => by
    show Text.Arg.named (toArgName (ofArgName n)) (toExpr (ofExpr e)) = _
    rw [toExpr_ofExpr e]; cases n <;> rfl
end

/-! ## Acceptance -/

theorem isOk_map {ε α β : Type} (f : α → β) (e : Except ε α) : isOk (e.map f) = isOk e := by
  cases e <;> rfl

theorem isOk_mapM {ε α β : Type} (f : α → Except ε β) (xs : List α) :
    isOk (xs.mapM f) = xs.all fun x => isOk (f x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.all_cons, ← ih]
    cases f x <;> cases List.mapM f xs <;> rfl

theorem ofTypeDecl_isOk (d : Text.TypeDecl) : isOk (ofTypeDecl d) = okTypeDecl d := by
  cases d with
  | «alias» _ _ k => cases k <;> rfl
  | _ => rfl

theorem ofItemTypeDecl_isOk (d : Text.ItemTypeDecl) : isOk (ofItemTypeDecl d) = okItemTypeDecl d := by
  cases d with
  | resource => rfl
  | decl d => exact ofTypeDecl_isOk d

theorem ofUsePath_isOk (p : Text.UsePath) : isOk (ofUsePath p) = okUsePath p := by
  cases p <;> rfl

theorem ofUse_isOk (u : Text.Use) : isOk (ofUse u) = okUse u := by
  rw [ofUse, isOk_map]; exact ofUsePath_isOk u.path

theorem ofInclude_isOk (w : Text.WorldRef) (ws : List Text.IncludeItem) :
    isOk (ofInclude w ws) = okWorldRef w := by
  rw [ofInclude, isOk_map]; cases w <;> rfl

theorem ofIfaceItem_isOk (i : Text.InterfaceItem) : isOk (ofIfaceItem i) = okIfaceItem i := by
  cases i with
  | use u => rw [ofIfaceItem, isOk_map]; exact ofUse_isOk u
  | type d => rw [ofIfaceItem, isOk_map]; exact ofItemTypeDecl_isOk d
  | export_ _ _ t => cases t <;> rfl

theorem ofIfaceItems_isOk (is : List Text.InterfaceItem) :
    isOk (ofIfaceItems is) = is.all okIfaceItem := by
  rw [ofIfaceItems, isOk_mapM]; simp only [ofIfaceItem_isOk]

theorem ofWorldPath_isOk (p : Text.WorldItemPath) : isOk (ofWorldPath p) = okWorldPath p := by
  cases p with
  | named _ t =>
    cases t with
    | interface is => rw [ofWorldPath, isOk_map]; exact ofIfaceItems_isOk is
    | _ => rfl
  | package p => rw [ofWorldPath, isOk_map]; rfl
  | ident => rfl

theorem ofWorldItem_isOk (i : Text.WorldItem) : isOk (ofWorldItem i) = okWorldItem i := by
  cases i with
  | use u => rw [ofWorldItem, isOk_map]; exact ofUse_isOk u
  | «include» _ w ws => rw [ofWorldItem, isOk_map]; exact ofInclude_isOk w ws
  | type d => rw [ofWorldItem, isOk_map]; exact ofItemTypeDecl_isOk d
  | import_ _ p => rw [ofWorldItem, isOk_map]; exact ofWorldPath_isOk p
  | export_ _ p => rw [ofWorldItem, isOk_map]; exact ofWorldPath_isOk p

theorem ofTypeStmt_isOk (s : Text.TypeStatement) : isOk (ofTypeStmt s) = okTypeStmt s := by
  cases s with
  | interface _ _ is => rw [ofTypeStmt, isOk_map]; exact ofIfaceItems_isOk is
  | world _ _ is => rw [ofTypeStmt, isOk_map, isOk_mapM]; simp only [ofWorldItem_isOk]; rfl
  | type d => rw [ofTypeStmt, isOk_map]; exact ofTypeDecl_isOk d

theorem ofImportType_isOk (t : Text.ImportType) : isOk (ofImportType t) = okImportType t := by
  cases t with
  | interface is => rw [ofImportType, isOk_map]; exact ofIfaceItems_isOk is
  | _ => rfl

theorem ofStmt_isOk (s : Text.Statement) : isOk (ofStmt s) = okStmt s := by
  cases s with
  | import_ _ _ _ t => rw [ofStmt, isOk_map]; exact ofImportType_isOk t
  | type s => rw [ofStmt, isOk_map]; exact ofTypeStmt_isOk s
  | _ => rfl

/-- **Acceptance**: a document maps iff `okDoc` holds. -/
theorem ofDoc_isOk (d : Text.Document) : isOk (ofDoc d) = okDoc d := by
  rw [ofDoc, isOk_map, isOk_mapM, okDoc]; simp only [ofStmt_isOk]

/-- Compositions map totally: no type statements and no inline interfaces. -/
theorem ofDoc_comp (d : Text.Document)
    (h : ∀ s ∈ d.statements, (∀ t, s ≠ .type t) ∧ ∀ ds x n is, s ≠ .import_ ds x n (.interface is)) :
    okDoc d = true := by
  rw [okDoc, List.all_eq_true]
  intro s hs
  have ⟨ht, hi⟩ := h s hs
  cases s with
  | type t => exact absurd rfl (ht t)
  | import_ ds x n ty =>
    cases ty with
    | interface is => exact absurd rfl (hi ds x n is)
    | _ => rfl
  | _ => rfl

/-! ## Statement by statement -/

theorem mapM_forall₂ {ε α β : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], ys, h => by
    have : ys = [] := by simpa [List.mapM_nil, pure, Except.pure] using h.symm
    rw [this]; exact .nil
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => rw [hx, hxs] at h; cases h
      | ok ys' =>
        rw [hx, hxs] at h
        have hys : ys = y :: ys' := by cases h; rfl
        rw [hys]; exact .cons hx (mapM_forall₂ f xs ys' hxs)

/-- **An accepted document maps statement by statement**, with its package name and
its `targets` path. -/
theorem ofDoc_ok {d : Text.Document} {d' : Syntax.Document} (h : ofDoc d = .ok d') :
    List.Forall₂ (fun s s' => ofStmt s = .ok s') d.statements d'.stmts ∧
      d'.pkg = ofPkgName d.package ∧ d'.targets = d.targets.map ofPkgPath := by
  unfold ofDoc at h
  cases hm : d.statements.mapM ofStmt with
  | error e => rw [hm] at h; cases h
  | ok ss =>
    rw [hm] at h
    have hd : d' = { pkg := ofPkgName d.package, targets := d.targets.map ofPkgPath, stmts := ss } := by
      cases h; rfl
    rw [hd]; exact ⟨mapM_forall₂ ofStmt _ _ hm, rfl, rfl⟩

/-- Composition statements map as written. -/
theorem ofStmt_let (ds : Text.Docs) (x : String) (e : Text.Expr) :
    ofStmt (.let_ ds x e) = .ok (.let x (ofExpr e)) := rfl

theorem ofStmt_export (ds : Text.Docs) (e : Text.Expr) (o : Text.ExportOptions) :
    ofStmt (.export_ ds e o) = .ok (.export (ofExpr e) (ofExportOpts o)) := rfl

theorem ofStmt_import_path (ds : Text.Docs) (x : String) (n : Option Text.ExternName) (p : Text.PkgPath) :
    ofStmt (.import_ ds x n (.package p)) = .ok (.import ⟨x, n.map nameStr, .path (ofPkgPath p)⟩) := rfl

end Silmaril.Wasm.Wac.Bridge
