module

public import Silmaril.Wasm.Wac.Elab.Defs

/-!
# WAC: WIT declarations as relations

Big-step relations for the WIT declarations of a document (`Silmaril.Wasm.Wac.WitDecl`):
every choice and every check of `use`, `include`, type declarations, world items and
the implicit imports of used interfaces is a premise. The data of a declaration (the
elaborated types `elabTy`/`elabSig`, the items of a type declaration `typeDecl`, the
denotation of a used type `denOf`/`usedKind`, the used interfaces `WSt.allUsed`) is
shared with the elaborator.

* `UseNamesR`, `UseR`: a `use` (each name defined in the used interface as a type, not
  declared yet);
* `IfaceItemsR`: an interface body (a type declared once, a function exported once);
* `ExternR`, `WorldItemsR`: world items (an import or export name used once);
* `RenamesR`, `IncludeItemsR`, `IncludeR`, `IncludesR`: `include … with { … }`;
* `ImplicitR`: the implicit imports of used interfaces;
* `WorldKindR`: a world body;
* `TypeStmtR`, `ImportKindR`: the type statements and import types of the elaborator
  (`typeStmt`, `importKind`), so that the premises `typeStmt … = .ok …` and
  `importKind … = .ok …` of `ElabStmt` are relations too (`typeStmt_iff`,
  `importKind_iff`).

`Silmaril.Wasm.Wac.WitDeclSpec.Thms` proves each function equivalent to its relation
(`ifaceExports_iff`, `worldKind_iff`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

namespace WitDecl

open Silmaril.Wasm.Wit.Binary (IfaceName)

/-- The names of a `use` of `I` (exports `es`), given the names `ex` declared before. -/
inductive UseNamesR (I : IfaceName) (es : Externs) (ex : List String) :
    List (String × Den) × Externs → List Wit.UseName → List (String × Den) × Externs → Prop
  | nil {acc : List (String × Den) × Externs} : UseNamesR I es ex acc [] acc
  | cons {bs : List (String × Den)} {xs : Externs} {un : Wit.UseName} {rest : List Wit.UseName}
      {r : List (String × Den) × Externs} {k : Kind} :
      es.find un.name = some (.type k) → un.bound ∉ ex → un.bound ∉ xs.map (·.1) →
      UseNamesR I es ex (bs ++ [(un.bound, denOf I un.name k)], xs ++ [(un.bound, usedKind I un.name)]) rest r →
      UseNamesR I es ex (bs, xs) (un :: rest) r

/-- A `use`: the path names an interface with an id, and its names are used. -/
inductive UseR (L : Look) (u : Wit.Use) (ex : List String) : IfaceName × List (String × Den) × Externs → Prop
  | mk {id : String} {es : Externs} {I : IfaceName} {r : List (String × Den) × Externs} :
      L.iface u.path = .ok (id, es) → ifaceNameOf id = some I → UseNamesR I es ex ([], []) u.names r →
      UseR L u ex (I, r.1, r.2)

/-- An interface body, item by item. -/
inductive IfaceItemsR (L : Look) : Scope × Externs → List Wit.IfaceItem → Scope × Externs → Prop
  | nil {acc : Scope × Externs} : IfaceItemsR L acc [] acc
  | type {sc : Scope} {xs : Externs} {d : Wit.TypeDef} {rest : List Wit.IfaceItem} {r : Scope × Externs} :
      sc.lookup d.name = none →
      IfaceItemsR L (sc ++ [(typeDecl sc d).1], xs ++ (typeDecl sc d).2) rest r →
      IfaceItemsR L (sc, xs) (.type d :: rest) r
  | func {sc : Scope} {xs : Externs} {f : Wit.FuncDef} {rest : List Wit.IfaceItem} {r : Scope × Externs} :
      f.name ∉ xs.map (·.1) →
      IfaceItemsR L (sc, xs ++ [(f.name, .func (elabSig sc f.func))]) rest r →
      IfaceItemsR L (sc, xs) (.func f :: rest) r
  | use {sc : Scope} {xs : Externs} {u : Wit.Use} {rest : List Wit.IfaceItem} {r : Scope × Externs}
      {I : IfaceName} {bs : List (String × Den)} {ys : Externs} :
      UseR L u (xs.map (·.1)) (I, bs, ys) → IfaceItemsR L (sc ++ bs, xs ++ ys) rest r →
      IfaceItemsR L (sc, xs) (.use u :: rest) r

/-- A world extern, named. -/
inductive ExternR (L : Look) (sc : Scope) : Wit.Extern → String × Kind → Prop
  | func {n : String} {f : Wit.Func} : ExternR L sc (.func n f) (n, .func (elabSig sc f))
  | iface {n : String} {items : List Wit.IfaceItem} {r : Scope × Externs} :
      IfaceItemsR L ([], []) items r → ExternR L sc (.iface n items) (n, .inst none r.2)
  | path {p : Wit.UsePath} {id : String} {es : Externs} :
      L.iface p = .ok (id, es) → ExternR L sc (.path p) (id, .inst (some id) es)

/-- The items of a world, in order; includes are kept for later. -/
inductive WorldItemsR (L : Look) : WSt → List Wit.WorldItem → WSt → Prop
  | nil {w : WSt} : WorldItemsR L w [] w
  | «import» {w r : WSt} {e : Wit.WorldExtern} {rest : List Wit.WorldItem} {n : String} {k : Kind} :
      ExternR L w.sc e.ext (n, k) → n ∉ w.imports.map (·.1) →
      WorldItemsR L { w with imports := w.imports ++ [(n, k)] } rest r → WorldItemsR L w (.import e :: rest) r
  | «export» {w r : WSt} {e : Wit.WorldExtern} {rest : List Wit.WorldItem} {n : String} {k : Kind} :
      ExternR L w.sc e.ext (n, k) → n ∉ w.exports.map (·.1) →
      WorldItemsR L { w with exports := w.exports ++ [(n, k)] } rest r → WorldItemsR L w (.export e :: rest) r
  | type {w r : WSt} {d : Wit.TypeDef} {rest : List Wit.WorldItem} :
      w.sc.lookup d.name = none →
      WorldItemsR L { w with sc := w.sc ++ [(typeDecl w.sc d).1], imports := w.imports ++ (typeDecl w.sc d).2 }
        rest r →
      WorldItemsR L w (.type d :: rest) r
  | use {w r : WSt} {u : Wit.Use} {rest : List Wit.WorldItem} {I : IfaceName} {bs : List (String × Den)}
      {ys : Externs} :
      UseR L u (w.imports.map (·.1)) (I, bs, ys) →
      WorldItemsR L { w with sc := w.sc ++ bs, imports := w.imports ++ ys, used := w.used ++ [I] } rest r →
      WorldItemsR L w (.use u :: rest) r
  | «include» {w r : WSt} {i : Wit.Include} {rest : List Wit.WorldItem} :
      WorldItemsR L { w with includes := w.includes ++ [i] } rest r → WorldItemsR L w (.include i :: rest) r

/-- The `with` clause of an include: each name renamed once. -/
inductive RenamesR : List Wit.IncludeName → List (String × String) → Prop
  | nil : RenamesR [] []
  | cons {r : Wit.IncludeName} {rs : List Wit.IncludeName} {rest : List (String × String)} :
      RenamesR rs rest → r.name ∉ rest.map (·.1) → RenamesR (r :: rs) ((r.name, r.as) :: rest)

/-- The items of an included world, added to `xs` and renamed by the remaining renamings. -/
inductive IncludeItemsR : Externs × List (String × String) → Externs → Externs × List (String × String) → Prop
  | nil {acc : Externs × List (String × String)} : IncludeItemsR acc [] acc
  | idKeep {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
      {r : Externs × List (String × String)} :
      ':' ∈ n.toList → n ∈ xs.map (·.1) → IncludeItemsR (xs, rn) rest r → IncludeItemsR (xs, rn) ((n, k) :: rest) r
  | idAdd {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
      {r : Externs × List (String × String)} :
      ':' ∈ n.toList → n ∉ xs.map (·.1) → IncludeItemsR (xs ++ [(n, k)], rn) rest r →
      IncludeItemsR (xs, rn) ((n, k) :: rest) r
  | named {xs : Externs} {rn : List (String × String)} {n : String} {k : Kind} {rest : Externs}
      {r : Externs × List (String × String)} :
      ':' ∉ n.toList → (rn.lookup n).getD n ∉ xs.map (·.1) →
      IncludeItemsR (xs ++ [((rn.lookup n).getD n, k)], rn.filter (·.1 != n)) rest r →
      IncludeItemsR (xs, rn) ((n, k) :: rest) r

/-- An `include`: imports, then exports, every renaming used. -/
inductive IncludeR (L : Look) (w : WSt) (i : Wit.Include) : WSt → Prop
  | mk {rn rn1 : List (String × String)} {wi we is es : Externs} :
      RenamesR i.names rn → L.world i.path = .ok (wi, we) →
      IncludeItemsR (w.imports, rn) wi (is, rn1) → IncludeItemsR (w.exports, rn1) we (es, []) →
      IncludeR L w i { w with imports := is, exports := es }

/-- The `include`s, in order. -/
inductive IncludesR (L : Look) : WSt → List Wit.Include → WSt → Prop
  | nil {w : WSt} : IncludesR L w [] w
  | cons {w w1 r : WSt} {i : Wit.Include} {rest : List Wit.Include} :
      IncludeR L w i w1 → IncludesR L w1 rest r → IncludesR L w (i :: rest) r

/-- The implicit imports of used interfaces: each once, unless imported. -/
inductive ImplicitR (L : Look) (imports : Externs) : Externs → List IfaceName → Externs → Prop
  | nil {acc : Externs} : ImplicitR L imports acc [] acc
  | skip {acc r : Externs} {I : IfaceName} {rest : List IfaceName} :
      (I.id ∈ imports.map (·.1) ∨ I.id ∈ acc.map (·.1)) → ImplicitR L imports acc rest r →
      ImplicitR L imports acc (I :: rest) r
  | add {acc r : Externs} {I : IfaceName} {rest : List IfaceName} {k : Kind} :
      I.id ∉ imports.map (·.1) → I.id ∉ acc.map (·.1) → L.byName I = .ok k →
      ImplicitR L imports (acc ++ [(I.id, k)]) rest r → ImplicitR L imports acc (I :: rest) r

/-- **A world body**: its items, its includes, then the implicit imports in front. -/
inductive WorldKindR (L : Look) (items : List Wit.WorldItem) : Externs × Externs → Prop
  | mk {w1 w2 : WSt} {imp : Externs} :
      WorldItemsR L {} items w1 → IncludesR L w1 w1.includes w2 → ImplicitR L w2.imports [] w2.allUsed imp →
      WorldKindR L items (imp ++ w2.imports, w2.exports)

end WitDecl

open Syntax in
/-- A type statement: an interface, a world, or a type declaration (in the top-level
scope). -/
inductive TypeStmtR (cx : ECtx) (st : ESt) : TypeStmt → String × Kind → Prop
  | iface {i : Wit.Interface} {sc : WitDecl.Scope} {xs : Externs} :
      WitDecl.IfaceItemsR (cx.look st) ([], []) i.items (sc, xs) →
      TypeStmtR cx st (.iface i) (i.name, .type (.inst (some (cx.declId i.name)) xs))
  | world {w : Wit.World} {is es : Externs} :
      WitDecl.WorldKindR (cx.look st) w.items (is, es) →
      TypeStmtR cx st (.world w) (w.name, .type (.comp (some (cx.declId w.name)) is es))
  | type {d : Wit.TypeDef} :
      TypeStmtR cx st (.type d) (d.name, ((WitDecl.typeDecl (rootScope st) d).2.head?.map (·.2)).getD default)

open Syntax in
/-- The kind an import statement imports. -/
inductive ImportKindR (cx : ECtx) (st : ESt) : ImportType → Kind → Prop
  | path {p : PkgPath} {k : Kind} : resolvePath cx st p = .ok k → ImportKindR cx st (.path p) k
  | func {f : Wit.Func} : ImportKindR cx st (.func f) (.func (WitDecl.elabSig (rootScope st) f))
  | iface {items : List Wit.IfaceItem} {sc : WitDecl.Scope} {xs : Externs} :
      WitDecl.IfaceItemsR (cx.look st) ([], []) items (sc, xs) → ImportKindR cx st (.iface items) (.inst none xs)
  | ident {x : String} {i : Nat} : st.scope.lookup x = some i → ImportKindR cx st (.ident x) (st.g.kindOf i)

end Silmaril.Wasm.Wac
