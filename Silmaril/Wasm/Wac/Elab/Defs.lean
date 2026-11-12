module

public import Silmaril.Wasm.Wac.Infer.Defs
public import Silmaril.Wasm.Wac.Implicit.Defs
public import Silmaril.Wasm.Wit.Elab.Defs
public import Silmaril.Wasm.Wac.WitDecl.Defs

/-!
# WAC: elaboration of documents into composition graphs

`elabDoc env d` elaborates a WAC document into a composition graph, following wac's
resolver (wac `5a7480c`, `crates/wac-parser/src/resolution.rs`, `AstResolver`)
statement by statement:

* `import id (as n)? : ty` adds an import node. Its name is `n`, else the package path
  as written, else the interface/world path of an identifier's instance or component
  kind, else `id`; its kind is the promoted kind of `ty` (an interface type becomes an
  instance, a world type a component). Two imports may not share a name.
* a type statement adds a type-definition node, exported under its name;
* `let x = e` binds `x` to the node of `e`; names are bound once;
* `export e`, `export e as n`, `export e...` add exports (spread exports skip names
  already exported; an export may not have the name of a type definition);
* `new p { args }` elaborates the arguments left to right (inferred and named,
  `Silmaril.Wasm.Wac.Infer`), then the spread arguments in order, checks every argument
  against the package's imports by WIT subtyping (`sub`), and, without `...`, that
  every import is given; it adds an instantiation node whose kind is the instance of
  the package's exports;
* `e.x` and `e["n"]` alias an export of an instance (one alias node per export).

After the statements, the implicit imports are resolved (`Implicit.resolve`) and the
`targets` world is checked (`checkTarget`): the composition may import only what
the world imports (at a supertype of the world's import), and must export everything
the world exports (at a subtype).

**WIT declarations.** Type statements, inline interfaces and function types are WIT
(`Wit.Syntax`), elaborated by `Silmaril.Wasm.Wac.WitDecl` with `use`, `include`, alias
expansion and the implicit imports of used interfaces; `ECtx.look` is how they see the
document. A named type of a top-level type statement or function type denotes the type
of the top-level declaration of that name (`rootScope`: an alias is expanded).
Extern-name validity (`InvalidExternName`) is not checked.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Syntax
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

/-! ## WIT types -/

mutual
/-- A WIT type; `res` are the witResources in scope. -/
def witTy (res : List String) : Wit.Ty → Silmaril.Wasm.Wit.Binary.Ty
  | .bool => .prim .bool
  | .s8 => .prim .s8
  | .s16 => .prim .s16
  | .s32 => .prim .s32
  | .s64 => .prim .s64
  | .u8 => .prim .u8
  | .u16 => .prim .u16
  | .u32 => .prim .u32
  | .u64 => .prim .u64
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .string => .prim .string
  | .errorContext => .prim .errorContext
  | .named n => if n ∈ res then .own ⟨.local, n⟩ else .ref ⟨.local, n⟩
  | .list t => .list (witTy res t)
  | .fixedList t n => .fixedList (witTy res t) n
  | .map k v => .map (witTy res k) (witTy res v)
  | .tuple ts => .tuple (witTys res ts)
  | .option t => .option (witTy res t)
  | .result a b => .result (witTyOpt res a) (witTyOpt res b)
  | .own r => .own ⟨.local, r⟩
  | .borrow r => .borrow ⟨.local, r⟩
  | .future t => .future (witTyOpt res t)
  | .stream t => .stream (witTyOpt res t)
def witTyOpt (res : List String) : Option Wit.Ty → Option Silmaril.Wasm.Wit.Binary.Ty
  | none => none
  | some t => some (witTy res t)
def witTys (res : List String) : List Wit.Ty → List Silmaril.Wasm.Wit.Binary.Ty
  | [] => []
  | t :: ts => witTy res t :: witTys res ts
end

/-- A WIT function type. -/
def witSig (res : List String) (f : Wit.Func) : Sig :=
  ⟨f.async, f.params.map fun p => (p.1, witTy res p.2), f.result.map (witTy res)⟩

/-! ## Context and state -/

/-- What elaboration reads: the packages and the document's package name. -/
structure ECtx where
  env : PkgEnv
  pkg : PkgName

/-- The node a local name is bound to. -/
def ESt.lookup (st : ESt) (x : String) : Except ElabError Nat :=
  match st.scope.lookup x with
  | some i => .ok i
  | none => .error (.undefinedName x)

/-- Bind a local name, once. -/
def ESt.bind (st : ESt) (x : String) (i : Nat) : Except ElabError ESt :=
  if (st.scope.lookup x).isSome then .error (.duplicateName x)
  else .ok { st with scope := st.scope ++ [(x, i)] }

/-- Add a node. -/
def ESt.add (st : ESt) (nd : CNode) : ESt × Nat :=
  let (g, i) := st.g.add nd
  ({ st with g }, i)

/-- A package by key. -/
def ECtx.package (cx : ECtx) (key : String) : Except ElabError PkgType :=
  match cx.env.lookup key with
  | some p => .ok p
  | none => .error (.unknownPackage key)

/-- Project a kind along export names (interfaces, instances, worlds, components). -/
def walkKind : Kind → List String → Option Kind
  | k, [] => some k
  | k, s :: ss =>
    let es? := match k with
      | .type (.inst _ es) | .inst _ es | .type (.comp _ _ es) | .comp _ _ es => some es
      | _ => none
    match es? with
    | some es => (Externs.find es s).bind fun k' => walkKind k' ss
    | none => none

/-- Resolve a package path: a local declaration (the document's own package) or a
definition of a package of the registry. -/
def resolvePath (cx : ECtx) (st : ESt) (p : PkgPath) : Except ElabError Kind :=
  match p.segments with
  | [] => .error (.packageMissingExport p.pkg "")
  | s :: ss =>
    if p.pkg = cx.pkg.name then do
      let i ← st.lookup s
      match walkKind (st.g.kindOf i) ss with
      | some k => pure k
      | none => .error (.packageMissingExport p.pkg p.str)
    else do
      let pk ← cx.package (PkgName.key ⟨p.pkg, p.version⟩)
      match (pk.defs.find s).bind fun k => walkKind k ss with
      | some k => pure k
      | none => .error (.packageMissingExport p.pkg p.str)

/-- The interface identifier of a declaration of the document's package. -/
def ECtx.declId (cx : ECtx) (name : String) : String :=
  cx.pkg.name ++ "/" ++ name ++ (match cx.pkg.version with | none => "" | some v => "@" ++ v)

/-- An interface declared in the document. -/
def ESt.localIface (st : ESt) (n : String) : Except ElabError (String × Externs) := do
  let i ← st.lookup n
  match st.g.kindOf i with
  | .type (.inst (some id) es) => pure (id, es)
  | _ => .error (.notInterface n)

/-- The key `ns:name(@version)` of a WIT package name. -/
def witPkgKey (pk : Wit.PackageName) : String :=
  pk.ns ++ ":" ++ pk.name ++ (match pk.version with | none => "" | some v => "@" ++ v.str)

/-- How WIT declarations see the document: declarations by local name, package items
by path, interfaces by structured name. -/
def ECtx.look (cx : ECtx) (st : ESt) : WitDecl.Look where
  iface
    | .local n => st.localIface n
    | .foreign pk n => do
      let key := witPkgKey pk
      let p ← cx.package key
      match p.defs.find n with
      | some (.type (.inst (some id) es)) => pure (id, es)
      | some _ => .error (.notInterface n)
      | none => .error (.packageMissingExport key n)
  world
    | .local n => do
      let i ← st.lookup n
      match st.g.kindOf i with
      | .type (.comp _ is es) | .comp _ is es => pure (is, es)
      | _ => .error (.notWorld n)
    | .foreign pk n => do
      let key := witPkgKey pk
      let p ← cx.package key
      match p.defs.find n with
      | some (.type (.comp _ is es)) => pure (is, es)
      | some _ => .error (.notWorld n)
      | none => .error (.packageMissingExport key n)
  byName I :=
    if I.pkg.ns ++ ":" ++ I.pkg.name = cx.pkg.name ∧ I.pkg.version = cx.pkg.version then do
      let (id, es) ← st.localIface I.name
      pure (.inst (some id) es)
    else do
      let key := WitDecl.pkgKeyOf I.pkg
      let p ← cx.package key
      match p.defs.find I.name with
      | some (.type (.inst id es)) => pure (.inst id es)
      | _ => .error (.packageMissingExport key I.name)

/-- The names of the top level that denote types: type declarations (an alias denotes
its definiens), as a WIT scope. -/
def rootScope (st : ESt) : WitDecl.Scope :=
  st.scope.filterMap fun (x, i) => match st.g.kindOf i with
    | .type (.value v) => some (x, .val v)
    | .type (.resource _) => some (x, .res ⟨.local, x⟩)
    | _ => none

/-! ## Aliases -/

/-- The exports of the instance node `i`. -/
def ESt.exportsOf (st : ESt) (i : Nat) (what : String) : Except ElabError Externs :=
  match (st.g.kindOf i).exports? with
  | some es => .ok es
  | none => .error (.notAnInstance what)

/-- The alias node of export `n` (of kind `k`) of instance node `i`: an existing one,
or a new one. -/
def ESt.aliasAt (st : ESt) (i : Nat) (n : String) (k : Kind) : ESt × Nat :=
  match st.g.findAlias i n with
  | some j => (st, j)
  | none => st.add ⟨.alias i n, k⟩

/-- Alias the export `n` of instance node `i`, if it has one. -/
def ESt.aliasExport (st : ESt) (i : Nat) (n : String) (what : String) :
    Except ElabError (Option (ESt × Nat)) := do
  let es ← st.exportsOf i what
  pure ((es.find n).map fun k => st.aliasAt i n k)

/-! ## Instantiation arguments -/

/-- Add an argument, once per name. -/
def insertArg (acc : List (String × Nat)) (n : String) (i : Nat) : Except ElabError (List (String × Nat)) :=
  if acc.any (·.1 == n) then .error (.duplicateInstantiationArg n) else .ok (acc ++ [(n, i)])

/-- The local names of the spread arguments, in order. -/
def spreads : List Arg → List String
  | [] => []
  | .spread x :: as => x :: spreads as
  | _ :: as => spreads as

/-- Pass the planned (import, export) pairs of a spread of instance node `i`. -/
def aliasPlan (es : Externs) (i : Nat) :
    ESt → List (String × Nat) → List (String × String) → ESt × List (String × Nat)
  | st, acc, [] => (st, acc)
  | st, acc, (n, e) :: rest =>
    let (st, j) := st.aliasAt i e ((es.find e).getD default)
    aliasPlan es i st (acc ++ [(n, j)]) rest

/-- The spread arguments, in order, after the other arguments. -/
def elabSpreads (imps : List String) :
    ESt → List (String × Nat) → List String → Except ElabError (ESt × List (String × Nat))
  | st, acc, [] => .ok (st, acc)
  | st, acc, x :: xs => do
    let i ← st.lookup x
    let es ← st.exportsOf i x
    let plan := spreadPlan es.names imps (acc.map (·.1))
    if plan.isEmpty then .error (.spreadInstantiationNoMatch x)
    else
      let (st, acc) := aliasPlan es i st acc plan
      elabSpreads imps st acc xs

/-- Type-check the arguments against the package's imports. -/
def checkArgs (pkg : String) (imps : Externs) (g : CGraph) : List (String × Nat) → Except ElabError Unit
  | [] => .ok ()
  | (n, j) :: rest =>
    match imps.find n with
    | none => .error (.missingComponentImport pkg n)
    | some k => if sub (g.kindOf j) k then checkArgs pkg imps g rest
      else .error (.mismatchedInstantiationArg n)

/-- Without `...`, every import must be given. -/
def checkAll (pkg : String) (imps : Externs) (acc : List (String × Nat)) : Except ElabError Unit :=
  match imps.find? fun q => !(acc.any (·.1 == q.1)) with
  | some q => .error (.missingInstantiationArg pkg q.1)
  | none => .ok ()

/-! ## Expressions -/

mutual
/-- Elaborate an expression to a node. -/
def elabExpr (cx : ECtx) : ESt → Expr → Except ElabError (ESt × Nat)
  | st, .ident x => do let i ← st.lookup x; pure (st, i)
  | st, .paren e => elabExpr cx st e
  | st, .access e x => do
    let (st, i) ← elabExpr cx st e
    let es ← st.exportsOf i x
    let n := tailOrSelf x es.names
    match ← st.aliasExport i n x with
    | some r => pure r
    | none => .error (.missingInstanceExport n)
  | st, .namedAccess e n => do
    let (st, i) ← elabExpr cx st e
    match ← st.aliasExport i n n with
    | some r => pure r
    | none => .error (.missingInstanceExport n)
  | st, .new p args => do
    if p.name = cx.pkg.name then .error (.unknownPackage p.key) else
    let pk ← cx.package p.key
    let imps := pk.imports.names
    let (st, acc, fill) ← elabArgs cx imps st [] args
    let (st, acc) ← elabSpreads imps st acc (spreads args)
    checkArgs p.key pk.imports st.g acc
    if fill then pure () else checkAll p.key pk.imports acc
    pure (st.add ⟨.inst p.key pk.imports acc, .inst none pk.exports⟩)

/-- Elaborate the inferred and named arguments, left to right; `true` with `...`. -/
def elabArgs (cx : ECtx) (imps : List String) :
    ESt → List (String × Nat) → List Arg → Except ElabError (ESt × List (String × Nat) × Bool)
  | st, acc, [] => .ok (st, acc, false)
  | st, acc, .inferred x :: rest => do
    let i ← st.lookup x
    let acc ← insertArg acc (inferArg st.g imps x i) i
    elabArgs cx imps st acc rest
  | st, acc, .named a e :: rest => do
    let (st, i) ← elabExpr cx st e
    let acc ← insertArg acc (namedArg imps a) i
    elabArgs cx imps st acc rest
  | st, acc, .spread _ :: rest => elabArgs cx imps st acc rest
  | st, acc, [.fill] => .ok (st, acc, true)
  | _, _, .fill :: _ :: _ => .error .fillArgumentNotLast
end

/-! ## Statements -/

/-- The kind an import statement imports, before promotion. -/
def importKind (cx : ECtx) (st : ESt) : ImportType → Except ElabError Kind
  | .path p => resolvePath cx st p
  | .func f => .ok (.func (WitDecl.elabSig (rootScope st) f))
  | .iface items => do pure (.inst none (← WitDecl.ifaceExports (cx.look st) items))
  | .ident x => do let i ← st.lookup x; pure (st.g.kindOf i)

/-- The name of an import. -/
def importName (i : Import) (k : Kind) : String :=
  match i.as with
  | some n => n
  | none => match i.ty with
    | .path p => p.str
    | .ident _ => match k with
      | .inst (some id) _ | .comp (some id) _ _ => id
      | _ => i.id
    | _ => i.id

/-- Whether node `i` is a type definition. -/
def ESt.isDefn (st : ESt) (i : Nat) : Bool :=
  match st.g.opOf? i with
  | some (.defn _) => true
  | _ => false

/-- Export node `i` as `n`. -/
def ESt.exportAs (st : ESt) (i : Nat) (n : String) : Except ElabError ESt :=
  if (st.scope.lookup n).any st.isDefn then .error (.exportConflict n)
  else if st.g.hasExport n then .error (.duplicateExport n)
  else .ok { st with g := { st.g with exports := st.g.exports ++ [(n, i)] } }

/-- Spread the exports of instance node `i` as exports, skipping exported names;
`true` when something was exported. -/
def spreadExports (es : Externs) (i : Nat) : ESt → Externs → Except ElabError (ESt × Bool)
  | st, [] => .ok (st, false)
  | st, (n, k) :: rest =>
    if st.g.hasExport n then spreadExports es i st rest
    else do
      let (st, j) := st.aliasAt i n k
      let st ← st.exportAs j n
      let (st, _) ← spreadExports es i st rest
      pure (st, true)

/-- The kind a type statement defines, and its name. -/
def typeStmt (cx : ECtx) (st : ESt) : TypeStmt → Except ElabError (String × Kind)
  | .iface i => do
    pure (i.name, .type (.inst (some (cx.declId i.name)) (← WitDecl.ifaceExports (cx.look st) i.items)))
  | .world w => do
    let (is, es) ← WitDecl.worldKind (cx.look st) w.items
    pure (w.name, .type (.comp (some (cx.declId w.name)) is es))
  | .type d => .ok (d.name, ((WitDecl.typeDecl (rootScope st) d).2.head?.map (·.2)).getD default)

/-- Elaborate a statement. -/
def elabStmt (cx : ECtx) (st : ESt) : Stmt → Except ElabError ESt
  | .import i => do
    let k ← importKind cx st i.ty
    let n := importName i k
    if n ∈ st.g.importNames then .error (.duplicateImport n) else
    let (st, j) := st.add ⟨.imp n, k.promote⟩
    st.bind i.id j
  | .type t => do
    let (n, k) ← typeStmt cx st t
    if st.g.hasExport n then .error (.declarationConflict n) else
    let (st, j) := st.add ⟨.defn n, k⟩
    let st := { st with g := { st.g with exports := st.g.exports ++ [(n, j)] } }
    st.bind n j
  | .let x e => do
    let (st, i) ← elabExpr cx st e
    st.bind x i
  | .export e opts => do
    let (st, i) ← elabExpr cx st e
    match opts with
    | .none =>
      match exportName? st.g i with
      | some n => st.exportAs i n
      | none => .error .exportRequiresAs
    | .rename n => st.exportAs i n
    | .spread => do
      let es ← st.exportsOf i "export spread"
      let (st, done) ← spreadExports es i st es
      if done then pure st else .error .spreadExportNoEffect

/-- Elaborate the statements in order. -/
def elabStmts (cx : ECtx) : ESt → List Stmt → Except ElabError ESt
  | st, [] => .ok st
  | st, s :: ss => do let st ← elabStmt cx st s; elabStmts cx st ss

/-! ## Targets -/

/-- Every import of the composition is an import of the world, at a supertype. -/
def checkTargetImports (wi : Externs) : Externs → Except ElabError Unit
  | [] => .ok ()
  | (n, k) :: rest =>
    match wi.find n with
    | none => .error (.importNotInTarget n)
    | some k' => if sub k'.promote k then checkTargetImports wi rest else .error (.targetMismatch n)

/-- Every export of the world is exported, at a subtype. -/
def checkTargetExports (g : CGraph) : Externs → Except ElabError Unit
  | [] => .ok ()
  | (n, k) :: rest =>
    match g.exports.lookup n with
    | none => .error (.missingTargetExport n)
    | some j => if sub (g.kindOf j) k.promote then checkTargetExports g rest else .error (.targetMismatch n)

/-- Check the composition against a target world (`validate_target`). -/
def checkTarget (g : CGraph) (wi we : Externs) : Except ElabError Unit := do
  checkTargetImports wi g.imports
  checkTargetExports g we

/-! ## Documents -/

/-- Check the `targets` clause, if any. -/
def checkTargets (cx : ECtx) (st : ESt) (g : CGraph) : Option PkgPath → Except ElabError Unit
  | none => .ok ()
  | some p => do
    match ← resolvePath cx st p with
    | .type (.comp _ wi we) => checkTarget g wi we
    | _ => .error (.notWorld p.str)

/-- **Elaborate a document**: the statements, then implicit imports, then `targets`. -/
def elabDoc (env : PkgEnv) (d : Document) : Except ElabError CGraph := do
  let cx : ECtx := ⟨env, d.pkg⟩
  let st ← elabStmts cx {} d.stmts
  let g ← Implicit.resolve st.g
  checkTargets cx st g d.targets
  pure g

end Silmaril.Wasm.Wac
