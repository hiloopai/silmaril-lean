module

public import Silmaril.Wasm.Wac.CGraph.Defs
public import Silmaril.Wasm.Wac.Bridge.Encode.Defs
public import Silmaril.Wasm.Wit.Project.Infer.Defs
public import Silmaril.Wasm.Component.Binary.Defs

/-!
# WAC bridge: packages from component binaries

The elaborator reads its packages from a registry (`PkgEnv`). `decodePkg` reads one
package from its binary: the component's world (`Wit.Project.projectI`, the projection
with type inference of `Silmaril.Wasm.Wit.Project`) read back as kinds, the inverse
direction of the encoder's kinds-as-component-types (`Silmaril.Wasm.Wac.Bridge.Encode`):

* a type scope maps type indices to what they define (`TInfo`): a value type, a
  function, an instance, a component, a resource, or a record/variant/enum/flags
  definition not yet named;
* `(export "t" (type (eq i)))` (and the same import) names a type: later references to
  it are `Ty.ref ⟨.local, "t"⟩`, its kind is `.type (.value …)`; `(type (sub
  resource))` is the resource `t`; `own`/`borrow` of it are `Ty.own`/`Ty.borrow` of
  `⟨.local, "t"⟩` — the conventions of the elaborator's `witTy`/`witTypeKind`;
* an instance or component type is decoded in a nested scope, which sees the outer
  scopes through `(alias outer k i (type))`; aliases of type exports of instances are
  followed;
* an instance named like an interface (`ns:pkg/iface…`) has that identifier (wac sets
  the `id` of interface instances from their names).

A package's `defs` (what `ns:pkg/name` paths look up) are its type exports, by the
interface or world name after `/` (a WIT package's interfaces and worlds).

This is executable glue for `wasm-wac compose`; nothing is proved about it. Outside:
core types, values, and resources defined (rather than imported) by the component.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

/-- What a type index of a scope defines. -/
inductive TInfo where
  | val (t : Ty)
  | func (s : Sig)
  | inst (es : Externs)
  | comp (is es : Externs)
  | res (name : String)
  /-- A name of the resource `res` other than its own (`type r2 = r`). -/
  | resAlias (name res : String)
  /-- A record, variant, enum or flags definition, before it is named by an export. -/
  | nominal (d : Nominal)
  deriving Inhabited

/-- A decoding scope: its types, its instances (their exports) and the outer scopes'
types. -/
structure DScope where
  types : Array TInfo := #[]
  insts : Array Externs := #[]
  outer : List (Array TInfo) := []
  /-- The nominal definitions met so far, by name. -/
  nom : NomTable := []
  deriving Inhabited

abbrev DM := StateT DScope (Except String)

def typeAt (i : Nat) : DM TInfo := do
  match (← get).types[i]? with
  | some t => pure t
  | none => throw s!"unknown type index {i}"

def pushTy (t : TInfo) : DM Unit := modify fun s => { s with types := s.types.push t }

/-- A value type. -/
def decVal : Silmaril.Wasm.Component.Binary.ValType → DM Ty
  | .prim p => pure (.prim p)
  | .idx i => do
    match ← typeAt i with
    | .val t => pure t
    | .res r => pure (.own ⟨.local, r⟩)
    | .resAlias n _ => pure (.ref ⟨.local, n⟩)
    | _ => throw s!"type index {i} is not a value type"

def decValOpt : Option Silmaril.Wasm.Component.Binary.ValType → DM (Option Ty)
  | none => pure none
  | some v => some <$> decVal v

/-- The resource at a type index, by the name it is used under. -/
def resAt (i : Nat) : DM TyRef := do
  match ← typeAt i with
  | .res r => pure ⟨.local, r⟩
  | .resAlias n _ => pure ⟨.local, n⟩
  | _ => throw s!"type index {i} is not a resource"

/-- A defined value type. -/
def decDefVal : DefValType → DM TInfo
  | .prim p => pure (.val (.prim p))
  | .list t => do pure (.val (.list (← decVal t)))
  | .fixedList t n => do pure (.val (.fixedList (← decVal t) n))
  | .map k v => do let k ← decVal k; pure (.val (.map k (← decVal v)))
  | .option t => do pure (.val (.option (← decVal t)))
  | .result a b => do let a ← decValOpt a; pure (.val (.result a (← decValOpt b)))
  | .tuple ts => do pure (.val (.tuple (← ts.mapM decVal)))
  | .own i => do
    match ← typeAt i with
    | .resAlias n _ => pure (.val (.ref ⟨.local, n⟩))
    | _ => pure (.val (.own (← resAt i)))
  | .borrow i => do pure (.val (.borrow (← resAt i)))
  | .future t => do pure (.val (.future (← decValOpt t)))
  | .stream t => do pure (.val (.stream (← decValOpt t)))
  | .record fs => do pure (.nominal (.record (← fs.mapM fun f => do pure (f.1, ← decVal f.2))))
  | .variant cs => do pure (.nominal (.variant (← cs.mapM fun c => do pure (c.1, ← decValOpt c.2))))
  | .enum ls => pure (.nominal (.enum ls))
  | .flags ls => pure (.nominal (.flags ls))

/-- A function type. -/
def decFunc (f : Silmaril.Wasm.Component.Binary.FuncType) : DM Sig := do
  let ps ← f.params.mapM fun p => do pure (p.1, ← decVal p.2)
  pure ⟨f.async, ps, ← decValOpt f.result⟩

/-- The interface identifier carried by an extern name. -/
def ifaceId (n : String) : Option String :=
  if n.contains ':' && n.contains '/' then some n else none

/-- The kind of a type index, as the definiens of a type item named `n` (the
elaborator's `witTypeKind`: `type r2 = r` of a resource is `own<r>`). -/
def typeKind (n : String) : TInfo → Kind
  | .val t => .value t
  | .func s => .func s
  | .inst es => .inst (ifaceId n) es
  | .comp is es => .comp (ifaceId n) is es
  | .res r | .resAlias _ r => .value (.own ⟨.local, r⟩)
  | .nominal _ => .value (.ref ⟨.local, n⟩)

/-- What a named type item adds to the type index space: references to it are by
name (`witTy` of a named type). -/
def namedInfo (n : String) : TInfo → TInfo
  | .res r | .resAlias _ r => .resAlias n r
  | .val _ | .nominal _ => .val (.ref ⟨.local, n⟩)
  | t => t

/-- Record a nominal definition under a name. -/
def addNom (n : String) : TInfo → DM Unit
  | .nominal d => modify fun s => { s with nom := s.nom ++ [(n, d)] }
  | _ => pure ()

/-- An item named `n` with descriptor `d`: its kind (pushing a type index for type
items). -/
def decExtern (n : String) : ExternDesc → DM Kind
  | .func i => do
    match ← typeAt i with
    | .func s => pure (.func s)
    | _ => throw s!"`{n}`: not a function type"
  | .instance i => do
    match ← typeAt i with
    | .inst es =>
      modify fun s => { s with insts := s.insts.push es }
      pure (.inst (ifaceId n) es)
    | _ => throw s!"`{n}`: not an instance type"
  | .component i => do
    match ← typeAt i with
    | .comp is es => pure (.comp (ifaceId n) is es)
    | _ => throw s!"`{n}`: not a component type"
  | .type (.eq i) => do
    let t ← typeAt i
    pushTy (namedInfo n t)
    addNom n t
    pure (.type (typeKind n t))
  | .type .subResource => do pushTy (.res n); pure (.type (.resource n))
  | .value (.type v) => do pure (.value (← decVal v))
  | .value (.eq _) => throw s!"`{n}`: value bound"
  | .coreModule _ => throw s!"`{n}`: core module"

/-- What a type alias brings into scope. -/
def decAlias (a : Alias) : DM Unit := do
  match a.sort, a.target with
  | .type, .outer c i => do
    let s ← get
    match s.outer[c - 1]? with
    | some ts => match ts[i]? with
      | some t => pushTy t
      | none => throw s!"outer type {c} {i}"
    | none => throw s!"outer scope {c}"
  | .type, .export i n => do
    match (← get).insts[i]? with
    | some es => match es.lookup n with
      | some (.type k) => pushTy (match k with
          | .resource r => .res r
          | .value (.own r) => .resAlias n r.name
          | .value _ => .val (.ref ⟨.local, n⟩)
          | .func s => .func s
          | .inst _ es => .inst es
          | .comp _ is es => .comp is es
          | .type _ => .val (.ref ⟨.local, n⟩))
      | _ => throw s!"alias of `{n}`: not a type export"
    | none => throw s!"alias of instance {i}"
  | .instance, .export i n => do
    match (← get).insts[i]? with
    | some es => match es.lookup n with
      | some (.inst _ es') => modify fun s => { s with insts := s.insts.push es' }
      | _ => throw s!"alias of `{n}`: not an instance export"
    | none => throw s!"alias of instance {i}"
  | _, _ => pure ()

/-- Run a nested scope. -/
def inNested {α : Type} (m : DM α) : DM α := do
  let s ← get
  match m.run { outer := s.types :: s.outer, nom := s.nom } with
  | .ok (a, s') =>
    set { s with nom := s'.nom }
    pure a
  | .error e => throw e

mutual
/-- A type definition. -/
def decDefType : DefType → DM TInfo
  | .val d => decDefVal d
  | .func f => do pure (.func (← decFunc f))
  | .instance ds => do pure (.inst (← inNested (decIDecls ds [])))
  | .component ds => do
    let (is, es) ← inNested (decCDecls ds [] [])
    pure (.comp is es)
  | .resource .. => throw "resource definition"
/-- One instance declaration, adding to the exports. -/
def decIDecl : InstanceDecl → Externs → DM Externs
  | .export n d, es => do
    let k ← decExtern n.name d
    pure (es ++ [(n.name, k)])
  | .type t, es => do
    let ti ← decDefType t
    pushTy ti
    pure es
  | .alias a, es => do decAlias a; pure es
  | .coreType _, es => pure es
/-- Declarations of an instance type: its exports. -/
def decIDecls : List InstanceDecl → Externs → DM Externs
  | [], es => pure es
  | d :: ds, es => do
    let es ← decIDecl d es
    decIDecls ds es
/-- Declarations of a component type: its imports and exports. -/
def decCDecls : List ComponentDecl → Externs → Externs → DM (Externs × Externs)
  | [], is, es => pure (is, es)
  | .import n d :: ds, is, es => do
    let k ← decExtern n.name d
    decCDecls ds (is ++ [(n.name, k)]) es
  | .inst d :: ds, is, es => do
    let es ← decIDecl d es
    decCDecls ds is es
end

/-- The interface or world name of a package-level type export: `ns:pkg/name@v` is
`name`. -/
def defName (n : String) : String :=
  match n.splitOn "/" with
  | [_, r] => (r.splitOn "@").headD r
  | _ => n

/-- An interface or world of a WIT package is a component type exporting it under its
identifier; unwrap it. -/
def unwrapDef : Kind → Kind
  | .comp _ [] [(id, .inst _ es)] => .inst (some id) es
  | .comp _ [] [(id, .comp _ is es)] => .comp (some id) is es
  | k => k

/-- A package from its world, and the nominal definitions it uses. -/
def pkgOfWorld (w : Wit.Project.WorldType) : Except String (PkgType × NomTable) := do
  let ((is, es), sc) ← (decCDecls w [] []).run {}
  let defs := es.filterMap fun
    | (n, .type k) => some (defName n, .type (unwrapDef k))
    | _ => none
  pure ({ imports := is, exports := es.filter (fun p => match p.2 with | .type _ => false | _ => true), defs },
    sc.nom)

/-- **A package from its binary** (a component, or a WIT package). -/
def decodePkg (b : ByteArray) : Except String (PkgType × NomTable) := do
  let c ← match Component.Binary.parse b with
    | .ok c => pure c
    | .error _ => throw "malformed component"
  match Wit.Project.projectI c with
  | some w => pkgOfWorld w
  | none => throw "the component's world cannot be projected"

end Silmaril.Wasm.Wac.Bridge
