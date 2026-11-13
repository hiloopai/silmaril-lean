module

public import Silmaril.Wasm.Wac.Bridge.Decode.Defs
public import Silmaril.Wasm.Wac.WitDecl.Defs

/-!
# WAC bridge: a decoder for resource definitions and `use` across interfaces

`Bridge.DecodeGaps` shows two kinds of packages that `decodePkg` (`Bridge.Decode`) does not
read: a component that **defines and exports a resource**, whose projection refers to the
resource by `(alias outer 0 i (type))`, which `decAlias` reads in the enclosing scope; and
a WIT package with an interface that **uses** a type of another interface, whose wrapper
component type imports the used interface, so that `unwrapDef` does not unwrap it, and
whose used types become local names, losing their owner.

`decodePkgU` is a second decoder, a variant of `decodePkg` (whose functions it reuses
through `onBase`) with three changes:

* `(alias outer 0 i (type))` is the type `i` of the **current** scope (the binary format's
  reading of count 0);
* an imported (or aliased) instance whose name is an interface identifier `ns:pkg/i@v` is
  recorded with its interface name (`UScope.ids`, beside `DScope.insts`). A type alias of an
  export `t` of such an instance `I` is a **used type**: `own<…>`/`borrow<…>` of it and
  references to it are `Ty.own`/`Ty.borrow`/`Ty.ref` of `⟨.iface I, t⟩`, and a type item
  `(export "u" (type (eq i)))` of it has the kind `.type (.value (.ref ⟨.iface I, t⟩))`. These
  are the elaborator's readings of `use I.{t as u}` (`WitDecl.denOf`, `WitDecl.usedKind`), so
  `WitDecl.usedBy` finds the used interface;
* a package definition that is a wrapper component type **with imports** exporting one
  instance (wit-component's layout of an interface that uses others) is unwrapped to that
  interface (`unwrapU`).

A used type is kept in the type index space as `.val (.own ⟨.iface I, t⟩)` (a resource) or
`.val (.ref ⟨.iface I, t⟩)` (any other type): `isUsed`.

`naCs` says that a list of declarations contains no `alias` declaration at any depth. On such
declarations the two decoders agree (`Bridge.DecodeUse.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner IfaceName)

namespace DecodeUse

/-- A decoding scope of `decodePkgU`: the scope of `decodePkg`, and for each of its
instances (`base.insts`) the interface it is, if its name is an interface identifier. -/
structure UScope where
  base : DScope := {}
  ids : Array (Option IfaceName) := #[]
  deriving Inhabited

abbrev UM := StateT UScope (Except String)

/-- Run a computation of `decodePkg` on the base scope. -/
def onBase {α : Type} (m : DM α) : UM α := fun u =>
  match m.run u.base with
  | .ok (a, b) => .ok (a, { u with base := b })
  | .error e => .error e

/-- The interface named by an extern name, if it is an interface identifier. -/
def ifaceOf (n : String) : Option IfaceName := (ifaceId n).bind WitDecl.ifaceNameOf

/-- A used type, as the type index space keeps it. -/
def isUsed : TInfo → Bool
  | .val (.own ⟨.iface _, _⟩) => true
  | .val (.ref ⟨.iface _, _⟩) => true
  | _ => false

/-- The used resource at a type index. -/
def usedRes : TInfo → Option TyRef
  | .val (.own ⟨.iface I, n⟩) => some ⟨.iface I, n⟩
  | _ => none

/-- What an alias of the type export `n` (of kind `k`) of the interface `I` adds to the
type index space: a resource of `I`, or a reference to the type `n` of `I` (to the
original owner, if `I` itself re-exports a used type). -/
def usedInfo (I : IfaceName) (n : String) : Kind → TInfo
  | .resource _ => .val (.own ⟨.iface I, n⟩)
  | .value (.ref ⟨.iface J, m⟩) => .val (.ref ⟨.iface J, m⟩)
  | _ => .val (.ref ⟨.iface I, n⟩)

/-- `namedInfo`, keeping used types: a type item naming a used type is that used type. -/
def namedInfoU (n : String) (t : TInfo) : TInfo := if isUsed t then t else namedInfo n t

/-- `typeKind`, for used types `WitDecl.usedKind`'s definiens: `ref ⟨I, t⟩`. -/
def typeKindU (n : String) (t : TInfo) : Kind :=
  if isUsed t then
    match t with
    | .val (.own r) => .value (.ref r)
    | t => typeKind n t
  else typeKind n t

/-- A defined value type: `own`/`borrow` of a used resource, else as `decDefVal`. -/
def decDefValU : DefValType → UM TInfo
  | .own i => do
    match usedRes (← onBase (typeAt i)) with
    | some r => pure (.val (.own r))
    | none => onBase (decDefVal (.own i))
  | .borrow i => do
    match usedRes (← onBase (typeAt i)) with
    | some r => pure (.val (.borrow r))
    | none => onBase (decDefVal (.borrow i))
  | d => onBase (decDefVal d)

/-- An item named `n` with descriptor `d`: instances record their interface; type items
keep used types; otherwise as `decExtern`. -/
def decExternU (n : String) : ExternDesc → UM Kind
  | .instance i => do
    match ← onBase (typeAt i) with
    | .inst es =>
      modify fun u => { base := { u.base with insts := u.base.insts.push es }, ids := u.ids.push (ifaceOf n) }
      pure (.inst (ifaceId n) es)
    | _ => throw s!"`{n}`: not an instance type"
  | .type (.eq i) => do
    let t ← onBase (typeAt i)
    onBase (pushTy (namedInfoU n t))
    onBase (addNom n t)
    pure (.type (typeKindU n t))
  | d => onBase (decExtern n d)

/-- What an alias brings into scope: `outer 0` is the current scope; a type export of an
interface instance is a used type; an aliased instance records its interface. -/
def decAliasU (a : Alias) : UM Unit :=
  match a.sort, a.target with
  | .type, .outer 0 i => do
    match (← get).base.types[i]? with
    | some t => onBase (pushTy t)
    | none => throw s!"outer type 0 {i}"
  | .type, .export i n => do
    let u ← get
    match u.base.insts[i]?, u.ids[i]? with
    | some es, some (some I) =>
      match es.lookup n with
      | some (.type k) => onBase (pushTy (usedInfo I n k))
      | _ => throw s!"alias of `{n}`: not a type export"
    | _, _ => onBase (decAlias a)
  | .instance, .export _ n => do
    onBase (decAlias a)
    modify fun u => { u with ids := u.ids.push (ifaceOf n) }
  | _, _ => onBase (decAlias a)

/-- Run a nested scope. -/
def inNestedU {α : Type} (m : UM α) : UM α := do
  let u ← get
  match m.run { base := { outer := u.base.types :: u.base.outer, nom := u.base.nom } } with
  | .ok (a, u') =>
    set { u with base := { u.base with nom := u'.base.nom } }
    pure a
  | .error e => throw e

mutual
/-- A type definition. -/
def decDefTypeU : DefType → UM TInfo
  | .val d => decDefValU d
  | .func f => do pure (.func (← onBase (decFunc f)))
  | .instance ds => do pure (.inst (← inNestedU (decIDeclsU ds [])))
  | .component ds => do
    let (is, es) ← inNestedU (decCDeclsU ds [] [])
    pure (.comp is es)
  | .resource .. => throw "resource definition"
/-- One instance declaration, adding to the exports. -/
def decIDeclU : InstanceDecl → Externs → UM Externs
  | .export n d, es => do
    let k ← decExternU n.name d
    pure (es ++ [(n.name, k)])
  | .type t, es => do
    let ti ← decDefTypeU t
    onBase (pushTy ti)
    pure es
  | .alias a, es => do decAliasU a; pure es
  | .coreType _, es => pure es
/-- Declarations of an instance type: its exports. -/
def decIDeclsU : List InstanceDecl → Externs → UM Externs
  | [], es => pure es
  | d :: ds, es => do
    let es ← decIDeclU d es
    decIDeclsU ds es
/-- Declarations of a component type: its imports and exports. -/
def decCDeclsU : List ComponentDecl → Externs → Externs → UM (Externs × Externs)
  | [], is, es => pure (is, es)
  | .import n d :: ds, is, es => do
    let k ← decExternU n.name d
    decCDeclsU ds (is ++ [(n.name, k)]) es
  | .inst d :: ds, is, es => do
    let es ← decIDeclU d es
    decCDeclsU ds is es
end

/-- A wrapper component type with imports exporting one instance: wit-component's layout
of an interface that uses types of the interfaces it imports. -/
def isUseWrap : Kind → Bool
  | .comp _ (_ :: _) [(_, .inst _ _)] => true
  | _ => false

/-- `unwrapDef`, also unwrapping the wrapper of an interface that uses others. -/
def unwrapU : Kind → Kind
  | .comp _ (_ :: _) [(id, .inst _ es)] => .inst (some id) es
  | k => unwrapDef k

/-- The package of the imports `is` and exports `es` of a world, definitions unwrapped by
`f`. -/
def pkgWith (f : Kind → Kind) (is es : Externs) : PkgType :=
  { imports := is, exports := es.filter (fun p => match p.2 with | .type _ => false | _ => true),
    defs := es.filterMap fun
      | (n, .type k) => some (defName n, .type (f k))
      | _ => none }

/-- A package from its world, and the nominal definitions it uses. -/
def pkgOfWorldU (w : Wit.Project.WorldType) : Except String (PkgType × NomTable) := do
  let ((is, es), sc) ← (decCDeclsU w [] []).run {}
  pure (pkgWith unwrapU is es, sc.base.nom)

/-- **A package from its binary**, reading resource definitions and used types. -/
def decodePkgU (b : ByteArray) : Except String (PkgType × NomTable) := do
  let c ← match Component.Binary.parse b with
    | .ok c => pure c
    | .error _ => throw "malformed component"
  match Wit.Project.projectI c with
  | some w => pkgOfWorldU w
  | none => throw "the component's world cannot be projected"

/-! ## Declarations without aliases -/

mutual
/-- A type definition with no `alias` declaration inside. -/
def naD : DefType → Bool
  | .component ds => naCs ds
  | .instance ds => naIs ds
  | _ => true
/-- An instance declaration that is not an alias and contains none. -/
def naI : InstanceDecl → Bool
  | .alias _ => false
  | .type t => naD t
  | _ => true
/-- Instance declarations without aliases. -/
def naIs : List InstanceDecl → Bool
  | [] => true
  | d :: ds => naI d && naIs ds
/-- A component declaration without aliases. -/
def naC : ComponentDecl → Bool
  | .import .. => true
  | .inst d => naI d
/-- **Component declarations without aliases**, at any depth. -/
def naCs : List ComponentDecl → Bool
  | [] => true
  | d :: ds => naC d && naCs ds
end

/-- No exported type of `es` is a wrapper that `unwrapU` reads as an interface using others. -/
def noUseDefs (es : Externs) : Bool :=
  es.all fun p => match p.2 with
    | .type k => !isUseWrap k
    | _ => true

end DecodeUse

end Silmaril.Wasm.Wac.Bridge
