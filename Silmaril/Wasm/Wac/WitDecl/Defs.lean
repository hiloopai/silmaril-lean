module

public import Silmaril.Wasm.Wac.CGraph.Defs
public import Silmaril.Wasm.Wac.Names.Defs
public import Silmaril.Wasm.Wit.Syntax.Defs

/-!
# WAC: WIT declarations inside a document (`use`, `include`, aliases)

The type statements of a WAC document (interfaces, worlds, type declarations) and the
inline interfaces of imports are WIT (`Wit.Syntax`). This module elaborates them to
item kinds, following wac's resolver (wac `5a7480c`,
`crates/wac-parser/src/resolution.rs`: `interface_items`, `world_items`,
`item_type_decl`, `use_type`, `world_item_path`, `world_include`, `ty`):

* **Scopes.** Items are elaborated in order; a name denotes what was declared before it
  in the same interface or world (`Scope`, wac's `local_item`). A record, variant, enum
  or flags type `t` denotes the reference `t` (`Ty.ref ⟨.local, t⟩`); a resource `r`
  denotes `own<r>`; an **alias** `type x = T` denotes the elaborated `T` itself, so
  every use of `x` is *expanded* (wac's `resolve_value_type`, which the subtype checker
  applies before comparing value types).
* **`use path.{t as u}`** binds `u` to the type `t` of the interface `path` (a
  declaration of the document or an interface of a package) and exports (in an
  interface) or imports (in a world) it as the alias `.type (.value (.ref ⟨I, t⟩))`
  where `I` is the used interface's name; `u` denotes `ref ⟨I, t⟩` (`own`/`borrow` of
  it for a resource). This is the representation of a used type in resolved WIT
  (`Wit.Binary`, `TyDefKind.type (.ref ⟨.iface i, t⟩)`), so a used type compares equal
  to the same use in a package. Errors: `undefinedInterfaceType`, `useConflict`,
  `notInterfaceValueType`, `notInterface`.
* **Worlds** import and export functions (typed in the world's scope), inline
  interfaces and interfaces by path (`duplicateWorldItem` on a repeated name); type
  declarations and `use`s add imports. **`include w with { a as b }`** is processed
  after the other items, in order: every import and export of `w` is added, renamed by
  the `with` clause; a name with `:` (an interface id) is added only if absent, any
  other name clashing with an existing item is `worldIncludeConflict`; a `with` name
  occurring twice is `duplicateWorldIncludeName`, one matching nothing
  `missingWorldInclude`.
* **Implicit imports of used interfaces** (wac's `World::implicit_imported_interfaces`):
  the interfaces a world `use`s, and those its imported interfaces `use` (recognised by
  their exported aliases `ref ⟨I, t⟩`), are added *in front of* the world's imports,
  unless imported already, as resolved WIT worlds have them. So `targets` checks them
  as wac's `validate_target` does.

How the document is consulted (interfaces and worlds by path, interfaces by name) is
the parameter `Look`, implemented by `Silmaril.Wasm.Wac.Elab`.

**Restrictions.** Aliases are expanded within an interface or world; a used type is
kept as the reference `ref ⟨I, t⟩` even when `t` is an alias in `I` (as in resolved
WIT). Record, variant, enum and flags types are compared by reference, not
structurally (wac compares them structurally). Field and case types are not
elaborated, and names not in scope are references (wac reports `UndefinedName`). A
resource used through a chain of `use`s denotes `ref`, not `own`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName PackageName)

namespace WitDecl

/-- What a name of an interface or world scope denotes. -/
inductive Den where
  /-- A value type (an alias is its definiens). -/
  | val (t : Silmaril.Wasm.Wit.Binary.Ty)
  /-- A resource. -/
  | res (r : TyRef)
  deriving Repr, DecidableEq, Inhabited

/-- The names of an interface or world, in order. -/
abbrev Scope := List (String × Den)

/-- The value type a name denotes. -/
def Scope.ty (sc : Scope) (n : String) : Silmaril.Wasm.Wit.Binary.Ty :=
  match sc.lookup n with
  | some (.val t) => t
  | some (.res r) => .own r
  | none => .ref ⟨.local, n⟩

/-- The resource a name denotes (in `own<r>`, `borrow<r>`). -/
def Scope.res (sc : Scope) (n : String) : TyRef :=
  match sc.lookup n with
  | some (.res r) => r
  | some (.val (.ref r)) | some (.val (.own r)) => r
  | _ => ⟨.local, n⟩

mutual
/-- A WIT type in a scope. -/
def elabTy (sc : Scope) : Wit.Ty → Silmaril.Wasm.Wit.Binary.Ty
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
  | .named n => sc.ty n
  | .list t => .list (elabTy sc t)
  | .fixedList t n => .fixedList (elabTy sc t) n
  | .map k v => .map (elabTy sc k) (elabTy sc v)
  | .tuple ts => .tuple (elabTys sc ts)
  | .option t => .option (elabTy sc t)
  | .result a b => .result (elabTyOpt sc a) (elabTyOpt sc b)
  | .own r => .own (sc.res r)
  | .borrow r => .borrow (sc.res r)
  | .future t => .future (elabTyOpt sc t)
  | .stream t => .stream (elabTyOpt sc t)
def elabTyOpt (sc : Scope) : Option Wit.Ty → Option Silmaril.Wasm.Wit.Binary.Ty
  | none => none
  | some t => some (elabTy sc t)
def elabTys (sc : Scope) : List Wit.Ty → List Silmaril.Wasm.Wit.Binary.Ty
  | [] => []
  | t :: ts => elabTy sc t :: elabTys sc ts
end

/-- A WIT function type in a scope. -/
def elabSig (sc : Scope) (f : Wit.Func) : Sig :=
  ⟨f.async, f.params.map fun p => (p.1, elabTy sc p.2), f.result.map (elabTy sc)⟩

/-- The extern name and kind of a resource function (`method_extern_name`). -/
def resFunc (sc : Scope) (r : String) (rf : Wit.ResourceFunc) : String × Kind :=
  match rf.kind with
  | .ctor => ("[constructor]" ++ r,
      .func ⟨false, rf.func.params.map (fun p => (p.1, elabTy sc p.2)),
        some ((rf.func.result.map (elabTy sc)).getD (.own (sc.res r)))⟩)
  | .method n => ("[method]" ++ r ++ "." ++ n,
      .func ⟨rf.func.async, ("self", .borrow (sc.res r)) :: rf.func.params.map (fun p => (p.1, elabTy sc p.2)),
        rf.func.result.map (elabTy sc)⟩)
  | .static n => ("[static]" ++ r ++ "." ++ n, .func (elabSig sc rf.func))

/-! ## Interface names -/

/-- The text before the first `d` and, if `d` occurs, the text after it. -/
def splitStr (d : Char) (s : String) : String × Option String :=
  match splitAt d s.toList with
  | (a, b) => (String.ofList a, b.map String.ofList)

/-- The structured name of an interface id `ns:name/iface(@version)?`. -/
def ifaceNameOf (id : String) : Option IfaceName :=
  match splitStr ':' id with
  | (_, none) => none
  | (ns, some r) =>
    match splitStr '/' r with
    | (_, none) => none
    | (name, some r2) =>
      match splitStr '@' r2 with
      | (iface, v) => some ⟨⟨ns, name, v⟩, iface⟩

/-- The package key `ns:name(@version)` of a package name. -/
def pkgKeyOf (p : PackageName) : String :=
  p.ns ++ ":" ++ p.name ++ (match p.version with | none => "" | some v => "@" ++ v)

/-! ## How declarations see the document -/

/-- The document, as WIT declarations consult it. -/
structure Look where
  /-- The interface a path names (a declaration or a package interface): its id and
  exports. -/
  iface : Wit.UsePath → Except ElabError (String × Externs)
  /-- The world (or component type) a path names: its imports and exports. -/
  world : Wit.UsePath → Except ElabError (Externs × Externs)
  /-- The interface of a name (for the implicit imports of used interfaces). -/
  byName : IfaceName → Except ElabError Kind

/-- What a used type `t` of the interface `I` denotes: `own`/`borrow` of `ref ⟨I, t⟩` for a
resource, `ref ⟨I, t⟩` otherwise. -/
def denOf (I : IfaceName) (t : String) : Kind → Den
  | .resource _ => .res ⟨.iface I, t⟩
  | _ => .val (.ref ⟨.iface I, t⟩)

/-- The item a used type `t` of `I` adds: the alias of `ref ⟨I, t⟩`. -/
def usedKind (I : IfaceName) (t : String) : Kind := .type (.value (.ref ⟨.iface I, t⟩))

/-- The names of a `use` of the interface `I` (id `id`, exports `es`): for each, its
binding and its item; `ex` are the names already declared. -/
def useNames (I : IfaceName) (id : String) (es : Externs) (ex : List String) :
    List (String × Den) × Externs → List Wit.UseName → Except ElabError (List (String × Den) × Externs)
  | acc, [] => .ok acc
  | (bs, xs), un :: rest =>
    match es.find un.name with
    | none => .error (.undefinedInterfaceType un.name id)
    | some (.type k) =>
      if un.bound ∈ ex ∨ un.bound ∈ xs.map (·.1) then .error (.useConflict un.bound)
      else useNames I id es ex (bs ++ [(un.bound, denOf I un.name k)], xs ++ [(un.bound, usedKind I un.name)]) rest
    | some _ => .error (.notInterfaceValueType un.name)

/-- The items a `use` adds: the used interface, the bindings and the aliases. -/
def useItems (L : Look) (u : Wit.Use) (ex : List String) :
    Except ElabError (IfaceName × List (String × Den) × Externs) := do
  let (id, es) ← L.iface u.path
  match ifaceNameOf id with
  | none => .error (.notInterface id)
  | some I => do
    let r ← useNames I id es ex ([], []) u.names
    pure (I, r.1, r.2)

/-! ## Type declarations -/

/-- A type declaration: its binding, then the items it adds (the type, and a
resource's functions). -/
def typeDecl (sc : Scope) (d : Wit.TypeDef) : (String × Den) × Externs :=
  match d.kind with
  | .resource fns =>
    let b : String × Den := (d.name, .res ⟨.local, d.name⟩)
    (b, (d.name, .type (.resource d.name)) :: fns.map (resFunc (sc ++ [b]) d.name))
  | .alias t =>
    let v := elabTy sc t
    ((d.name, .val v), [(d.name, .type (.value v))])
  | _ =>
    let v : Silmaril.Wasm.Wit.Binary.Ty := .ref ⟨.local, d.name⟩
    ((d.name, .val v), [(d.name, .type (.value v))])

/-- Declare a type, once. -/
def declareType (sc : Scope) (xs : Externs) (d : Wit.TypeDef) : Except ElabError (Scope × Externs) :=
  if (sc.lookup d.name).isSome then .error (.duplicateName d.name) else
  let (b, items) := typeDecl sc d
  .ok (sc ++ [b], xs ++ items)

/-! ## Interfaces -/

/-- The scope and exports of an interface body, item by item. -/
def ifaceItems (L : Look) : Scope × Externs → List Wit.IfaceItem → Except ElabError (Scope × Externs)
  | acc, [] => .ok acc
  | (sc, xs), .type d :: rest => do
    let acc ← declareType sc xs d
    ifaceItems L acc rest
  | (sc, xs), .func f :: rest =>
    if f.name ∈ xs.map (·.1) then .error (.duplicateInterfaceExport f.name)
    else ifaceItems L (sc, xs ++ [(f.name, .func (elabSig sc f.func))]) rest
  | (sc, xs), .use u :: rest => do
    let (_, bs, ys) ← useItems L u (xs.map (·.1))
    ifaceItems L (sc ++ bs, xs ++ ys) rest

/-- The exports of an interface body. -/
def ifaceExports (L : Look) (items : List Wit.IfaceItem) : Except ElabError Externs := do
  let (_, xs) ← ifaceItems L ([], []) items
  pure xs

/-! ## Worlds -/

/-- An elaborated world under construction. -/
structure WSt where
  sc : Scope := []
  imports : Externs := []
  exports : Externs := []
  /-- The interfaces the world `use`s. -/
  used : List IfaceName := []
  /-- The `include`s, processed last. -/
  includes : List Wit.Include := []
  deriving Inhabited

/-- A world extern, named. -/
def externOf (L : Look) (sc : Scope) : Wit.Extern → Except ElabError (String × Kind)
  | .func n f => .ok (n, .func (elabSig sc f))
  | .iface n items => do pure (n, .inst none (← ifaceExports L items))
  | .path p => do
    let (id, es) ← L.iface p
    pure (id, .inst (some id) es)

/-- The items of a world, in order (includes are kept for later). -/
def worldItems (L : Look) : WSt → List Wit.WorldItem → Except ElabError WSt
  | w, [] => .ok w
  | w, .import e :: rest => do
    let (n, k) ← externOf L w.sc e.ext
    if n ∈ w.imports.map (·.1) then .error (.duplicateWorldItem n)
    else worldItems L { w with imports := w.imports ++ [(n, k)] } rest
  | w, .export e :: rest => do
    let (n, k) ← externOf L w.sc e.ext
    if n ∈ w.exports.map (·.1) then .error (.duplicateWorldItem n)
    else worldItems L { w with exports := w.exports ++ [(n, k)] } rest
  | w, .type d :: rest => do
    let (sc, is) ← declareType w.sc w.imports d
    worldItems L { w with sc, imports := is } rest
  | w, .use u :: rest => do
    let (I, bs, ys) ← useItems L u (w.imports.map (·.1))
    worldItems L { w with sc := w.sc ++ bs, imports := w.imports ++ ys, used := w.used ++ [I] } rest
  | w, .include i :: rest => worldItems L { w with includes := w.includes ++ [i] } rest

/-- The `with` renamings of an include, once each. -/
def renames : List Wit.IncludeName → Except ElabError (List (String × String))
  | [] => .ok []
  | r :: rs => do
    let rest ← renames rs
    if r.name ∈ rest.map (·.1) then .error (.duplicateWorldIncludeName r.name) else pure ((r.name, r.as) :: rest)

/-- Add the items `its` of an included world to `xs`, renaming by `rn` (consumed). -/
def includeItems : Externs × List (String × String) → Externs → Except ElabError (Externs × List (String × String))
  | acc, [] => .ok acc
  | (xs, rn), (n, k) :: rest =>
    if ':' ∈ n.toList then
      includeItems (if n ∈ xs.map (·.1) then xs else xs ++ [(n, k)], rn) rest
    else
      let n' := (rn.lookup n).getD n
      let rn' := rn.filter (·.1 != n)
      if n' ∈ xs.map (·.1) then .error (.worldIncludeConflict n')
      else includeItems (xs ++ [(n', k)], rn') rest

/-- Process an `include`. -/
def includeWorld (L : Look) (w : WSt) (i : Wit.Include) : Except ElabError WSt := do
  let rn ← renames i.names
  let (wi, we) ← L.world i.path
  let (is, rn) ← includeItems (w.imports, rn) wi
  let (es, rn) ← includeItems (w.exports, rn) we
  match rn with
  | [] => pure { w with imports := is, exports := es }
  | (n, _) :: _ => .error (.missingWorldInclude n)

/-- The interfaces an imported instance `use`s: the owners of its exported aliases. -/
def usedBy (es : Externs) : List IfaceName :=
  es.filterMap fun p => match p.2 with
    | .type (.value (.ref ⟨.iface I, _⟩)) => some I
    | _ => none

/-- The implicit imports of the used interfaces: `(id, instance)`, in order of first use,
once each, except those imported already. -/
def implicitIfaces (L : Look) (imports : Externs) : Externs → List IfaceName → Except ElabError Externs
  | acc, [] => .ok acc
  | acc, I :: rest =>
    if I.id ∈ imports.map (·.1) ∨ I.id ∈ acc.map (·.1) then implicitIfaces L imports acc rest
    else do
      let k ← L.byName I
      implicitIfaces L imports (acc ++ [(I.id, k)]) rest

/-- Process the `include`s in order. -/
def includeWorlds (L : Look) : WSt → List Wit.Include → Except ElabError WSt
  | w, [] => .ok w
  | w, i :: rest => do
    let w ← includeWorld L w i
    includeWorlds L w rest

/-- The interfaces a world uses: its own `use`s, then those of its imported instances. -/
def WSt.allUsed (w : WSt) : List IfaceName :=
  w.used ++ w.imports.flatMap fun p => match p.2 with
    | .inst _ es => usedBy es
    | _ => []

/-- **The imports and exports of a world body.** -/
def worldKind (L : Look) (items : List Wit.WorldItem) : Except ElabError (Externs × Externs) := do
  let w ← worldItems L {} items
  let w ← includeWorlds L w w.includes
  let imp ← implicitIfaces L w.imports [] w.allUsed
  pure (imp ++ w.imports, w.exports)

end WitDecl

end Silmaril.Wasm.Wac
