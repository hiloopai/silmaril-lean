module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Wit.Project.Defs

/-!
# The world a component targets: closed types and width subtyping

`Silmaril.Wasm.Wit.Project.projectX` reads a component's world off its sections, keeping
type indices. It does not apply to the components `wit-component` builds for WASI 0.3:

* the export `wasi:cli/run@0.3.0` is an instance created by instantiating a **nested
  component** (the export-wrapping shim), without type ascription; `projectX` knows no
  type for it and gives `none`;
* the type definitions the component needs for its `canon` built-ins (`stream<u8>`, the
  `result` and `future` types) sit among the world's declarations;
* an imported instance type lists only the functions the component uses (`echo` imports
  `wasi:cli/environment@0.3.0` with `get-arguments` only).

This module compares worlds the way the Component Model's subtyping does, on **closed
types**: every type index is replaced by the type it names.

* `CType` (with `CFields`, `CCases`, `CList`, `COpt`; mutual, so that `DecidableEq` is
  derived): value types, function types (with `async`), instance types (named exports),
  component types (named imports and exports), type exports (`type`), resources (by the
  name of their export) and core modules (opaque).
* `rDef` resolves a `DefType` against the type index space of its scope (with the
  enclosing scope for `alias outer 1 k`); `resolveWorld W` resolves a `WorldType`
  (the declarations of a component type) to `CType.comp imports exports`.
* `resolveAst c` replays a `BinaryP3` component's sections: types, imports, aliases of
  instance exports, `canon lift`, nested components (resolved recursively),
  `instantiate` (the instance gets the nested component's exports) and inline instances,
  exports (ascribed or not). Core items and the other built-ins define core items only and
  are skipped.
* `sub a b` (`a` usable where `b` is expected): **width subtyping on instances** (`a`
  exports every name `b` exports, at an equal type), equality elsewhere.
* `targets c W`: every import of `c` is provided by `W` at a subtype, and every export of `W`
  is provided by `c` at a subtype. This is what `wasm-tools component targets` and `wac`'s
  `targets` check (component subtyping), restricted to width subtyping of instances.

**Approximations** (none arise in the WASI 0.3 examples): resources are identified by the
name of the export that declares them (two distinct resources exported under one name are
equal here); the exports of an instantiated nested component are resolved in the nested
component's own scope, so an export whose type refers to a type the nested component
imports gets that import's declared bound, not the argument's type; function types and
value types are compared by equality (the Component Model has no subtyping on them beyond
this); `value` imports and exports are rejected; type aliases other than `alias export` and
`alias outer` are rejected.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3.World

open Silmaril.Wasm.Component.Binary (PrimValType ValType DefValType FuncType DefType InstanceDecl
  ComponentDecl ExternDesc TypeBound ItemSort SortIdx InstanceExpr AliasTarget)

/-! ## Closed types -/

mutual
/-- A closed component-level type. -/
inductive CType where
  | prim (p : PrimValType)
  | record (fs : CFields)
  | variant (cs : CCases)
  | list (t : CType)
  | tuple (ts : CList)
  | flags (ns : List String)
  | enum (ns : List String)
  | option (t : CType)
  | result (ok err : COpt)
  | own (r : CType)
  | borrow (r : CType)
  | fixedList (t : CType) (n : Nat)
  | stream (t : COpt)
  | future (t : COpt)
  | map (k v : CType)
  /-- An abstract resource, named by the export that declares it. -/
  | resource (name : String)
  | func (params : CFields) (result : COpt) (async : Bool)
  /-- An instance type: its named exports. -/
  | inst (exports : CFields)
  /-- A component type: its named imports and exports. -/
  | comp (imports exports : CFields)
  /-- The extern of a type (`(type (eq …))`). -/
  | type (t : CType)
  | coreModule

/-- Named closed types (record fields, parameters, exports). -/
inductive CFields where
  | nil
  | cons (n : String) (t : CType) (rest : CFields)

/-- Variant cases. -/
inductive CCases where
  | nil
  | cons (n : String) (t : COpt) (rest : CCases)

/-- Tuple elements. -/
inductive CList where
  | nil
  | cons (t : CType) (rest : CList)

/-- An optional closed type. -/
inductive COpt where
  | none
  | some (t : CType)
end

deriving instance DecidableEq for CType

instance : Inhabited CType := ⟨.coreModule⟩

/-- A table of named closed types. -/
abbrev Table := List (String × CType)

def CFields.ofList : Table → CFields
  | [] => .nil
  | (n, t) :: r => .cons n t (CFields.ofList r)

def CFields.toList : CFields → Table
  | .nil => []
  | .cons n t r => (n, t) :: r.toList

/-! ## Resolving value and function types -/

section Resolve
variable (ts : List CType)

def rVal : Silmaril.Wasm.Component.Binary.ValType → Option CType
  | .prim p => some (.prim p)
  | .idx k => ts[k]?

def rOpt : Option Silmaril.Wasm.Component.Binary.ValType → Option COpt
  | none => some .none
  | some v => (rVal ts v).map .some

def rFields : List (String × Silmaril.Wasm.Component.Binary.ValType) → Option CFields
  | [] => some .nil
  | (n, v) :: r => do
    let t ← rVal ts v
    let r' ← rFields r
    pure (.cons n t r')

def rCases : List (String × Option Silmaril.Wasm.Component.Binary.ValType) → Option CCases
  | [] => some .nil
  | (n, v) :: r => do
    let t ← rOpt ts v
    let r' ← rCases r
    pure (.cons n t r')

def rList : List Silmaril.Wasm.Component.Binary.ValType → Option CList
  | [] => some .nil
  | v :: r => do
    let t ← rVal ts v
    let r' ← rList r
    pure (.cons t r')

def rDefVal : DefValType → Option CType
  | .prim p => some (.prim p)
  | .record fs => (rFields ts fs).map .record
  | .variant cs => (rCases ts cs).map .variant
  | .list v => (rVal ts v).map .list
  | .tuple vs => (rList ts vs).map .tuple
  | .flags ns => some (.flags ns)
  | .enum ns => some (.enum ns)
  | .option v => (rVal ts v).map .option
  | .result ok err => do
    let a ← rOpt ts ok
    let b ← rOpt ts err
    pure (.result a b)
  | .own k => ts[k]?.map .own
  | .borrow k => ts[k]?.map .borrow
  | .fixedList v n => (rVal ts v).map (.fixedList · n)
  | .stream v => (rOpt ts v).map .stream
  | .future v => (rOpt ts v).map .future
  | .map k v => do
    let a ← rVal ts k
    let b ← rVal ts v
    pure (.map a b)

def rFunc (f : Silmaril.Wasm.Component.Binary.FuncType) : Option CType := do
  let ps ← rFields ts f.params
  let r ← rOpt ts f.result
  pure (.func ps r f.async)

/-- The closed type of an extern descriptor named `n`. -/
def rDesc (n : String) : ExternDesc → Option CType
  | .coreModule _ => some .coreModule
  | .func k | .component k | .instance k => ts[k]?
  | .type (.eq k) => ts[k]?.map .type
  | .type .subResource => some (.type (.resource n))
  | .value _ => none

end Resolve

/-! ## Instance and component types -/

/-- The scope of a component type, or of a component: its type and instance index spaces
and its imports and exports so far. -/
structure Scope where
  types : List CType := []
  insts : List Table := []
  imports : Table := []
  exports : Table := []

/-- The export `n` of instance `i`. -/
def Scope.instExport (s : Scope) (i : Nat) (n : String) : Option CType :=
  (s.insts[i]?).bind fun tab => tab.lookup n

/-- The export table of an instance type. -/
def instTable : CType → Option Table
  | .inst es => some es.toList
  | _ => none

/-- A new item of the sort of `d`, with closed type `t`. -/
def Scope.push (s : Scope) (d : ExternDesc) (t : CType) : Option Scope :=
  match d, t with
  | .type _, .type t' => some { s with types := s.types ++ [t'] }
  | .instance _, t => (instTable t).map fun tab => { s with insts := s.insts ++ [tab] }
  | _, _ => some s

/-- A type alias in a component type (`outer` against the enclosing types `o`). -/
def Scope.alias (o : List CType) (s : Scope) : Binary.Alias → Option Scope
  | ⟨.type, .outer 1 k⟩ => o[k]?.map fun t => { s with types := s.types ++ [t] }
  | ⟨.type, .outer 0 k⟩ => s.types[k]?.map fun t => { s with types := s.types ++ [t] }
  | ⟨.type, .export i n⟩ => (s.instExport i n).bind fun
    | .type t => some { s with types := s.types ++ [t] }
    | _ => none
  | ⟨.instance, .export i n⟩ => (s.instExport i n).bind fun t =>
    (instTable t).map fun tab => { s with insts := s.insts ++ [tab] }
  | ⟨.core _, _⟩ => some s
  | _ => none

mutual
/-- **The closed type of a type definition**, in a scope whose types are `ts`. -/
def rDef (ts : List CType) : DefType → Option CType
  | .val d => rDefVal ts d
  | .func f => rFunc ts f
  | .instance ds => (rInstDecls ts {} ds).map fun s => .inst (CFields.ofList s.exports)
  | .component ds => (rCompDecls ts {} ds).map fun s =>
      .comp (CFields.ofList s.imports) (CFields.ofList s.exports)
  | .resource _ _ => some (.resource s!"#{ts.length}")

/-- The declarations of an instance type, with the enclosing types `o`. -/
def rInstDecls (o : List CType) (s : Scope) : List InstanceDecl → Option Scope
  | [] => some s
  | .coreType _ :: ds => rInstDecls o s ds
  | .type dt :: ds => (rDef s.types dt).bind fun t =>
      rInstDecls o { s with types := s.types ++ [t] } ds
  | .alias a :: ds => (s.alias o a).bind fun s' => rInstDecls o s' ds
  | .export n d :: ds => (rDesc s.types n.name d).bind fun t =>
      (s.push d t).bind fun s' =>
        rInstDecls o { s' with exports := s'.exports ++ [(n.name, t)] } ds

/-- The declarations of a component type, with the enclosing types `o`. -/
def rCompDecls (o : List CType) (s : Scope) : List ComponentDecl → Option Scope
  | [] => some s
  | .import n d :: ds => (rDesc s.types n.name d).bind fun t =>
      (s.push d t).bind fun s' =>
        rCompDecls o { s' with imports := s'.imports ++ [(n.name, t)] } ds
  | .inst (.coreType _) :: ds => rCompDecls o s ds
  | .inst (.type dt) :: ds => (rDef s.types dt).bind fun t =>
      rCompDecls o { s with types := s.types ++ [t] } ds
  | .inst (.alias a) :: ds => (s.alias o a).bind fun s' => rCompDecls o s' ds
  | .inst (.export n d) :: ds => (rDesc s.types n.name d).bind fun t =>
      (s.push d t).bind fun s' =>
        rCompDecls o { s' with exports := s'.exports ++ [(n.name, t)] } ds
end

/-- **The closed type of a world** (`Wit.Project.WorldType`, the declarations of a
component type). -/
def resolveWorld (W : Silmaril.Wasm.Wit.Project.WorldType) : Option CType :=
  rDef [] (.component W)

/-! ## Components -/

/-- The index spaces of a component that its world depends on. -/
structure CSt where
  scope : Scope := {}
  funcs : List CType := []
  comps : List CType := []

/-- The closed type of an item. -/
def CSt.item (s : CSt) (x : SortIdx) : Option CType :=
  match x.sort with
  | .func => s.funcs[x.idx]?
  | .instance => (s.scope.insts[x.idx]?).map fun tab => .inst (CFields.ofList tab)
  | .type => (s.scope.types[x.idx]?).map .type
  | .component => s.comps[x.idx]?
  | .core .module => some .coreModule
  | _ => none

/-- A new item of sort `k` with closed type `t`. -/
def CSt.add (s : CSt) (k : ItemSort) (t : CType) : Option CSt :=
  match k, t with
  | .func, t => some { s with funcs := s.funcs ++ [t] }
  | .component, t => some { s with comps := s.comps ++ [t] }
  | .type, .type t' => some { s with scope := { s.scope with types := s.scope.types ++ [t'] } }
  | .instance, t => (instTable t).map fun tab =>
      { s with scope := { s.scope with insts := s.scope.insts ++ [tab] } }
  | .core _, _ => some s
  | _, _ => none

/-- The sort of the items an extern descriptor describes. -/
def descSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance _ => .instance

/-- Fold a step over the elements of a vector section. -/
def foldO {α : Type} (f : CSt → α → Option CSt) : CSt → List α → Option CSt
  | s, [] => some s
  | s, x :: xs => (f s x).bind fun s' => foldO f s' xs

def stepType (s : CSt) (dt : DefType) : Option CSt :=
  (rDef s.scope.types dt).bind fun t => s.add .type (.type t)

def stepImport (s : CSt) (i : Binary.Import) : Option CSt :=
  (rDesc s.scope.types i.name.name i.desc).bind fun t =>
    (s.add (descSort i.desc) t).map fun s' =>
      { s' with scope := { s'.scope with imports := s'.scope.imports ++ [(i.name.name, t)] } }

def stepAlias (s : CSt) (a : Binary.Alias) : Option CSt :=
  match a with
  | ⟨.core _, _⟩ => some s
  | ⟨k, .export i n⟩ => (s.scope.instExport i n).bind fun t => s.add k t
  | _ => none

def stepCanon (s : CSt) : Canon → Option CSt
  | .lift _ _ t => (s.scope.types[t]?).bind fun ft => s.add .func ft
  | _ => some s

def stepInstance (s : CSt) : InstanceExpr → Option CSt
  | .instantiate k _ => (s.comps[k]?).bind fun
    | .comp _ es => s.add .instance (.inst es)
    | _ => none
  | .exports es =>
    (es.mapM fun e => (s.item e.2).map fun t => (e.1.name, t)).bind fun tab =>
      s.add .instance (.inst (CFields.ofList tab))

def stepExport (s : CSt) (e : Binary.Export) : Option CSt :=
  let t? := match e.desc with
    | some d => rDesc s.scope.types e.name.name d
    | none => s.item e.item
  t?.bind fun t =>
    (s.add e.item.sort t).map fun s' =>
      { s' with scope := { s'.scope with exports := s'.scope.exports ++ [(e.name.name, t)] } }

mutual
/-- Replay the sections of a component. -/
def walkSecs : CSt → List Section → Option CSt
  | s, [] => some s
  | s, .component c :: ss =>
    (resolveAst c).bind fun t => (s.add .component t).bind fun s' => walkSecs s' ss
  | s, .types xs :: ss => (foldO stepType s xs).bind fun s' => walkSecs s' ss
  | s, .imports xs :: ss => (foldO stepImport s xs).bind fun s' => walkSecs s' ss
  | s, .aliases xs :: ss => (foldO stepAlias s xs).bind fun s' => walkSecs s' ss
  | s, .canons xs :: ss => (foldO stepCanon s xs).bind fun s' => walkSecs s' ss
  | s, .instances xs :: ss => (foldO stepInstance s xs).bind fun s' => walkSecs s' ss
  | s, .exports xs :: ss => (foldO stepExport s xs).bind fun s' => walkSecs s' ss
  | _, .values _ :: _ => none
  | s, _ :: ss => walkSecs s ss

/-- **The closed component type of a component**: its imports and exports. -/
def resolveAst : Ast → Option CType
  | .mk ss => (walkSecs {} ss).map fun s =>
      .comp (CFields.ofList s.scope.imports) (CFields.ofList s.scope.exports)
end

/-! ## Targeting a world -/

/-- `a` is usable where `b` is expected: an instance with at least `b`'s exports at equal
types; otherwise equal. -/
def sub (a b : CType) : Bool :=
  match a, b with
  | .inst as, .inst bs => bs.toList.all fun (n, t) => as.toList.lookup n == some t
  | a, b => decide (a = b)

/-- Every entry of `need` is provided by `have` at a subtype. -/
def provides (have_ need : Table) : Bool :=
  need.all fun (n, t) => match have_.lookup n with
    | some t' => sub t' t
    | none => false

/-- **The component `c` targets the world `W`**: `W` provides every import of `c` at a
subtype and `c` provides every export of `W` at a subtype. -/
def targets (c : Ast) (W : Silmaril.Wasm.Wit.Project.WorldType) : Bool :=
  match resolveAst c, resolveWorld W with
  | some (.comp ci ce), some (.comp wi we) => provides wi.toList ci.toList && provides ce.toList we.toList
  | _, _ => false

end Silmaril.Wasm.Component.BinaryP3.World

end
