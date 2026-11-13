module

public import Silmaril.Wasm.Wac.FuncAlias.Defs

/-!
# WAC function type names: conservativity over the WIT-only elaborator

On the embedding of the WIT-only AST, the elaborator with function type names is the
elaborator of `Silmaril.Wasm.Wac.Elab`, layer by layer:

* `ifaceItems_wit`, `ifaceExports_wit`: interface bodies of WIT items;
* `worldItems_of`, `worldKind_of`: world bodies (inline interfaces as `WExtern.iface`);
* `elabStmt_of`, `elabStmts_of`: statements;
* **`elabDoc_ofDoc`**, `elabDocA_ofDoc`: documents.

So every theorem about `Wac.elabDoc` (its relational specification `elabDoc_iff`,
typing `elabDoc_typed`, …) holds of `FuncAlias.elabDoc` on embedded documents. The
cons lemmas `witIfaceItems_cons` and `witWorldItems_cons` split the WIT elaborators'
item loops into one item and the rest.

`ifaceExports_resource_example` checks the new interface items on the first items of
wac's `resource.wac`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.FuncAlias

open Silmaril.Wasm.Wit.Binary (Sig)
open WitDecl (Scope Look WSt)

/-! ## The WIT item loops, one item at a time -/

theorem witIfaceItems_cons (L : Look) (acc : Scope × Externs) (it : Wit.IfaceItem) (rest : List Wit.IfaceItem) :
    WitDecl.ifaceItems L acc (it :: rest) =
      (WitDecl.ifaceItems L acc [it] >>= fun acc => WitDecl.ifaceItems L acc rest) := by
  obtain ⟨sc, xs⟩ := acc
  cases it with
  | type d =>
    simp only [WitDecl.ifaceItems]
    cases WitDecl.declareType sc xs d <;> rfl
  | func f =>
    simp only [WitDecl.ifaceItems]
    split <;> rfl
  | use u =>
    simp only [WitDecl.ifaceItems]
    cases WitDecl.useItems L u (xs.map (·.1)) <;> rfl

theorem witWorldItems_import (L : Look) (w : WSt) (e : Wit.WorldExtern) (rest : List Wit.WorldItem) :
    WitDecl.worldItems L w (.import e :: rest) =
      (WitDecl.worldItems L w [.import e] >>= fun w => WitDecl.worldItems L w rest) := by
  simp only [WitDecl.worldItems]
  cases WitDecl.externOf L w.sc e.ext with
  | error => rfl
  | ok nk =>
    obtain ⟨n, k⟩ := nk
    by_cases h : n ∈ w.imports.map (·.1) <;> simp only [bind, Except.bind, h, ↓reduceIte]

theorem witWorldItems_export (L : Look) (w : WSt) (e : Wit.WorldExtern) (rest : List Wit.WorldItem) :
    WitDecl.worldItems L w (.export e :: rest) =
      (WitDecl.worldItems L w [.export e] >>= fun w => WitDecl.worldItems L w rest) := by
  simp only [WitDecl.worldItems]
  cases WitDecl.externOf L w.sc e.ext with
  | error => rfl
  | ok nk =>
    obtain ⟨n, k⟩ := nk
    by_cases h : n ∈ w.exports.map (·.1) <;> simp only [bind, Except.bind, h, ↓reduceIte]

theorem witWorldItems_cons (L : Look) (w : WSt) (it : Wit.WorldItem) (rest : List Wit.WorldItem) :
    WitDecl.worldItems L w (it :: rest) =
      (WitDecl.worldItems L w [it] >>= fun w => WitDecl.worldItems L w rest) := by
  cases it with
  | «import» e => exact witWorldItems_import L w e rest
  | «export» e => exact witWorldItems_export L w e rest
  | type d =>
    simp only [WitDecl.worldItems]
    cases WitDecl.declareType w.sc w.imports d <;> rfl
  | use u =>
    simp only [WitDecl.worldItems]
    cases WitDecl.useItems L u (w.imports.map (·.1)) <;> rfl
  | «include» i => rfl

/-! ## Interfaces -/

theorem aliasOf_nil (d : Wit.TypeDef) : aliasOf [] d = none := by
  unfold aliasOf; split <;> rfl

/-- A WIT interface item, without function type names in scope. -/
theorem ifaceItem_wit (L : Look) (sc : Scope) (xs : Externs) (it : Wit.IfaceItem) :
    ifaceItem L (sc, [], xs) (.wit it) =
      (WitDecl.ifaceItems L (sc, xs) [it]).map fun a => (a.1, [], a.2) := by
  have hw : ∀ it, witItem L sc [] xs it = (WitDecl.ifaceItems L (sc, xs) [it]).map fun a => (a.1, [], a.2) := by
    intro it
    unfold witItem
    cases WitDecl.ifaceItems L (sc, xs) [it] <;> rfl
  cases it with
  | type d =>
    simp only [ifaceItem, aliasOf_nil, List.lookup_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact hw _
  | use u => exact hw _
  | func f => exact hw _

/-- **Interface bodies of WIT items** elaborate as by `WitDecl.ifaceItems`. -/
theorem ifaceItems_wit (L : Look) :
    ∀ (is : List Wit.IfaceItem) (sc : Scope) (xs : Externs),
      ifaceItems L (sc, [], xs) (is.map .wit) =
        (WitDecl.ifaceItems L (sc, xs) is).map fun a => (a.1, [], a.2)
  | [], _, _ => rfl
  | it :: rest, sc, xs => by
    rw [List.map_cons, ifaceItems, ifaceItem_wit, witIfaceItems_cons L (sc, xs) it rest]
    cases WitDecl.ifaceItems L (sc, xs) [it] with
    | error => rfl
    | ok a =>
      obtain ⟨sc', xs'⟩ := a
      exact ifaceItems_wit L rest sc' xs'

theorem ifaceExports_wit (L : Look) (is : List Wit.IfaceItem) :
    ifaceExports L (is.map .wit) = WitDecl.ifaceExports L is := by
  unfold ifaceExports WitDecl.ifaceExports
  rw [ifaceItems_wit]
  cases WitDecl.ifaceItems L ([], []) is <;> rfl

/-! ## Worlds -/

theorem externOf_iface_wit (L : Look) (root : Root) (sc : Scope) (fs : FScope) (n : String)
    (is : List Wit.IfaceItem) :
    externOf L root sc fs (.iface n (is.map .wit)) = WitDecl.externOf L sc (.iface n is) := by
  simp only [externOf, WitDecl.externOf, ifaceExports_wit]

theorem witWorldItem_eq (L : Look) (w : WSt) (it : Wit.WorldItem) :
    witWorldItem L w [] it = (WitDecl.worldItems L w [it]).map (⟨·, []⟩) := by
  unfold witWorldItem
  cases WitDecl.worldItems L w [it] <;> rfl

/-- An embedded import of an inline interface. -/
theorem worldItem_import_iface (L : Look) (root : Root) (w : WSt) (n : String) (is : List Wit.IfaceItem)
    (ds : Wit.Docs) (gs : List Wit.Gate) :
    worldItem L root ⟨w, []⟩ (.import (.iface n (is.map .wit))) =
      (WitDecl.worldItems L w [.import ⟨.iface n is, ds, gs⟩]).map (⟨·, []⟩) := by
  simp only [worldItem, WitDecl.worldItems, externOf_iface_wit]
  cases WitDecl.externOf L w.sc (.iface n is) with
  | error => rfl
  | ok nk =>
    obtain ⟨n', k⟩ := nk
    by_cases h : n' ∈ w.imports.map (·.1) <;> simp only [bind, Except.bind, h, ↓reduceIte, Except.map]

/-- An embedded export of an inline interface. -/
theorem worldItem_export_iface (L : Look) (root : Root) (w : WSt) (n : String) (is : List Wit.IfaceItem)
    (ds : Wit.Docs) (gs : List Wit.Gate) :
    worldItem L root ⟨w, []⟩ (.export (.iface n (is.map .wit))) =
      (WitDecl.worldItems L w [.export ⟨.iface n is, ds, gs⟩]).map (⟨·, []⟩) := by
  simp only [worldItem, WitDecl.worldItems, externOf_iface_wit]
  cases WitDecl.externOf L w.sc (.iface n is) with
  | error => rfl
  | ok nk =>
    obtain ⟨n', k⟩ := nk
    by_cases h : n' ∈ w.exports.map (·.1) <;> simp only [bind, Except.bind, h, ↓reduceIte, Except.map]

/-- An embedded world item, without function type names in scope. -/
theorem worldItem_of (L : Look) (root : Root) (w : WSt) (it : Wit.WorldItem) :
    worldItem L root ⟨w, []⟩ (ofWorldItem it) = (WitDecl.worldItems L w [it]).map (⟨·, []⟩) := by
  cases it with
  | «import» e =>
    obtain ⟨ext, ds, gs⟩ := e
    cases ext with
    | iface n is => exact worldItem_import_iface L root w n is ds gs
    | func n f => exact witWorldItem_eq L w _
    | path p => exact witWorldItem_eq L w _
  | «export» e =>
    obtain ⟨ext, ds, gs⟩ := e
    cases ext with
    | iface n is => exact worldItem_export_iface L root w n is ds gs
    | func n f => exact witWorldItem_eq L w _
    | path p => exact witWorldItem_eq L w _
  | type d =>
    simp only [ofWorldItem, worldItem, aliasOf_nil, List.lookup_nil, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
    exact witWorldItem_eq L w _
  | use u => exact witWorldItem_eq L w _
  | «include» i => exact witWorldItem_eq L w _

/-- **World bodies of WIT items** elaborate as by `WitDecl.worldItems`. -/
theorem worldItems_of (L : Look) (root : Root) :
    ∀ (items : List Wit.WorldItem) (w : WSt),
      worldItems L root ⟨w, []⟩ (items.map ofWorldItem) = (WitDecl.worldItems L w items).map (⟨·, []⟩)
  | [], _ => rfl
  | it :: rest, w => by
    rw [List.map_cons, worldItems, worldItem_of, witWorldItems_cons L w it rest]
    cases WitDecl.worldItems L w [it] with
    | error => rfl
    | ok w' => exact worldItems_of L root rest w'

theorem worldKind_of (L : Look) (root : Root) (items : List Wit.WorldItem) :
    worldKind L root (items.map ofWorldItem) = WitDecl.worldKind L items := by
  unfold worldKind WitDecl.worldKind
  have h := worldItems_of L root items {}
  have e : ({} : XW) = ⟨{}, []⟩ := rfl
  rw [e, h]
  cases WitDecl.worldItems L {} items <;> rfl

/-! ## Statements and documents -/

theorem witStmt_eq (cx : ECtx) (st : ESt) (s : Syntax.Stmt) :
    witStmt cx st [] s = (Wac.elabStmt cx st s).map (⟨·, []⟩) := by
  unfold witStmt
  cases Wac.elabStmt cx st s <;> rfl

/-- The `type` statement of `Wac.elabStmt` is `define`. -/
theorem elabStmt_type (cx : ECtx) (st : ESt) (t : Syntax.TypeStmt) :
    Wac.elabStmt cx st (.type t) = (typeStmt cx st t >>= fun nk => define st nk.1 nk.2) := by
  simp only [Wac.elabStmt, define]

/-- The `import` statement of `Wac.elabStmt` is `importAs`. -/
theorem elabStmt_import (cx : ECtx) (st : ESt) (i : Syntax.Import) :
    Wac.elabStmt cx st (.import i) = (importKind cx st i.ty >>= fun k => importAs st i.id (importName i k) k) := by
  simp only [Wac.elabStmt, importAs]

theorem importName_iface (id : String) (as : Option String) (is : List Wit.IfaceItem) (k : Kind) :
    importName ⟨id, as, .iface is⟩ k = as.getD id := by
  cases as <;> rfl

/-- An embedded import of an inline interface. -/
theorem elabStmt_importIface (cx : ECtx) (st : ESt) (id : String) (as : Option String)
    (is : List Wit.IfaceItem) :
    elabStmt cx ⟨st, []⟩ (.importIface id as (is.map .wit)) =
      (Wac.elabStmt cx st (.import ⟨id, as, .iface is⟩)).map (⟨·, []⟩) := by
  rw [elabStmt_import]
  simp only [elabStmt, importKind, ifaceExports_wit, importName_iface]
  cases WitDecl.ifaceExports (cx.look st) is with
  | error => rfl
  | ok es => exact (by cases importAs st id (as.getD id) (.inst none es) <;> rfl)

/-- An embedded interface declaration. -/
theorem elabStmt_iface (cx : ECtx) (st : ESt) (i : Wit.Interface) :
    elabStmt cx ⟨st, []⟩ (.iface i.name (i.items.map .wit)) =
      (Wac.elabStmt cx st (.type (.iface i))).map (⟨·, []⟩) := by
  rw [elabStmt_type]
  simp only [elabStmt, typeStmt, ifaceExports_wit]
  cases WitDecl.ifaceExports (cx.look st) i.items with
  | error => rfl
  | ok es => exact (by cases define st i.name (.type (.inst (some (cx.declId i.name)) es)) <;> rfl)

/-- An embedded world declaration. -/
theorem elabStmt_world (cx : ECtx) (st : ESt) (w : Wit.World) :
    elabStmt cx ⟨st, []⟩ (.world w.name (w.items.map ofWorldItem)) =
      (Wac.elabStmt cx st (.type (.world w))).map (⟨·, []⟩) := by
  rw [elabStmt_type]
  simp only [elabStmt, typeStmt, worldKind_of]
  cases WitDecl.worldKind (cx.look st) w.items with
  | error => rfl
  | ok r =>
    obtain ⟨is, es⟩ := r
    exact (by cases define st w.name (.type (.comp (some (cx.declId w.name)) is es)) <;> rfl)

/-- **An embedded statement** elaborates as by `Wac.elabStmt`. -/
theorem elabStmt_of (cx : ECtx) (st : ESt) (s : Syntax.Stmt) :
    elabStmt cx ⟨st, []⟩ (ofStmt s) = (Wac.elabStmt cx st s).map (⟨·, []⟩) := by
  cases s with
  | «import» i =>
    obtain ⟨id, as, ty⟩ := i
    cases ty with
    | iface is => exact elabStmt_importIface cx st id as is
    | ident x => exact witStmt_eq cx st _
    | path p => exact witStmt_eq cx st _
    | func f => exact witStmt_eq cx st _
  | type t =>
    cases t with
    | iface i => exact elabStmt_iface cx st i
    | world w => exact elabStmt_world cx st w
    | type d =>
      simp only [ofStmt, elabStmt, aliasOf_nil]
      exact witStmt_eq cx st _
  | «let» x e => exact witStmt_eq cx st _
  | «export» e o => exact witStmt_eq cx st _

theorem elabStmts_of (cx : ECtx) :
    ∀ (ss : List Syntax.Stmt) (st : ESt),
      elabStmts cx ⟨st, []⟩ (ss.map ofStmt) = (Wac.elabStmts cx st ss).map (⟨·, []⟩)
  | [], _ => rfl
  | s :: ss, st => by
    rw [List.map_cons, elabStmts, elabStmt_of]
    simp only [Wac.elabStmts]
    cases Wac.elabStmt cx st s with
    | error => rfl
    | ok st' => exact elabStmts_of cx ss st'

/-- **Conservativity**: on an embedded WIT-only document, the elaborator with function
type names is `Wac.elabDoc`. -/
theorem elabDoc_ofDoc (env : PkgEnv) (d : Syntax.Document) :
    elabDoc env (ofDoc d) = Wac.elabDoc env d := by
  unfold elabDoc Wac.elabDoc
  have e : ({} : XSt) = ⟨{}, []⟩ := rfl
  simp only [ofDoc]
  rw [e, elabStmts_of]
  cases Wac.elabStmts ⟨env, d.pkg⟩ {} d.stmts <;> rfl

theorem elabDocA_ofDoc (env : PkgEnv) (d : Syntax.Document) :
    elabDocA env (ofDoc d) = Wac.elabDocA env d :=
  elabDoc_ofDoc env.expand d

end Silmaril.Wasm.Wac.FuncAlias

namespace Silmaril.Wasm.Wac.FuncAlias

open Silmaril.Wasm.Wit.Binary (Sig TyRef Owner)

/-- wac's `resource.wac`, its first three items: `resource x; type f = func(x: borrow<x>);
f2: f;`. The function type name exports the type of its signature, `f2` the function. -/
theorem ifaceExports_resource_example (L : WitDecl.Look) :
    ifaceExports L [.wit (.type ⟨"x", .resource [], {}, []⟩),
      .funcType "f" { params := [("x", .borrow "x")] }, .funcRef "f2" "f"] =
      .ok [("x", .type (.resource "x")),
        ("f", .type (.func ⟨false, [("x", .borrow ⟨.local, "x"⟩)], none⟩)),
        ("f2", .func ⟨false, [("x", .borrow ⟨.local, "x"⟩)], none⟩)] := by
  rfl

end Silmaril.Wasm.Wac.FuncAlias
