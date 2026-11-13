module

public import Silmaril.Wasm.Wit.Syntax.Defs

/-!
# WIT: name resolution

Resolution of the names of a set of WIT packages (a `Universe`: a document's packages
together with the packages it depends on), as relations, and the functions computing
them.

* `ResolvesTo U k p path i`: in package `p`, the path of a `use`, `include` or
  interface import/export denotes the interface or world (`k`) `i`. A local name is an
  item of `p` or, failing that, a top-level `use … as name;` of `p` naming a foreign
  item; a foreign path `ns:pkg/name@v` must name an item of a package of `U`
  (versions match exactly). `resolve` computes it.
* Scopes. Types live in interfaces, in worlds and in inline interfaces of worlds
  (`Owner`); a `TypeId` is an owner and a name. The scope of an owner is its type
  definitions and its `use`d names (`Owner.src?`; the first binding of a name counts,
  and validity requires names to be unique).
* `Denotes U i x t`: the name `x` of interface `i` denotes the type `t`, following
  `use` chains across interfaces. `Binds U o x t`: the same for any owner. `denote`
  and `bind` compute them with fuel.
* `IsResource U t`: `t` is a resource, possibly through `type r2 = r;` aliases;
  `isRes` computes it with fuel.
* The dependency graphs: `IfaceEdge` (interface `use`s), `TypeEdge` (references
  between type definitions) and `WorldEdge` (world `include`s), with node lists and
  dependency functions for `Silmaril.Wasm.Wit.Graph.kahn`.

`Silmaril.Wasm.Wit.Resolve.Thms` proves the functions sound for the relations, and
complete once the fuel exceeds the ranks of acyclic graphs.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-- A set of packages in which names are resolved. -/
abbrev Universe := List Package

/-- The kinds of package items a path resolves to. -/
inductive Kind where
  | iface | world
  deriving Repr, DecidableEq, Inhabited

/-- A package item (interface or world): its package and its name. -/
structure ItemId where
  pkg : PackageName
  name : Name
  deriving Repr, DecidableEq, Inhabited

/-- The last component of a path. -/
def UsePath.name : UsePath → Name
  | .local n | .foreign _ n => n

/-- The name a top-level `use` binds. -/
def TopUse.bound (u : TopUse) : Name := u.as.getD u.path.name

/-- The interface of a package with a given name. -/
def Package.iface? (P : Package) (n : Name) : Option Interface :=
  P.items.findSome? fun
    | .iface i => if i.name = n then some i else none
    | _ => none

/-- The world of a package with a given name. -/
def Package.world? (P : Package) (n : Name) : Option World :=
  P.items.findSome? fun
    | .world w => if w.name = n then some w else none
    | _ => none

/-- The path a top-level `use` of a package binds to a name. -/
def Package.topUse? (P : Package) (n : Name) : Option UsePath :=
  P.items.findSome? fun
    | .use u => if u.bound = n then some u.path else none
    | _ => none

/-- The package of a universe with a given name. -/
def Universe.pkg? (U : Universe) (p : PackageName) : Option Package :=
  U.find? fun P => P.name = p

/-- The interface with a given id. -/
def Universe.iface? (U : Universe) (i : ItemId) : Option Interface :=
  (U.pkg? i.pkg).bind (·.iface? i.name)

/-- The world with a given id. -/
def Universe.world? (U : Universe) (i : ItemId) : Option World :=
  (U.pkg? i.pkg).bind (·.world? i.name)

/-- The universe has an item of kind `k` with id `i`. -/
def Universe.has (U : Universe) : Kind → ItemId → Bool
  | .iface, i => (U.iface? i).isSome
  | .world, i => (U.world? i).isSome

/-- The path a top-level `use` of package `p` binds to `n`. -/
def Universe.topUse? (U : Universe) (p : PackageName) (n : Name) : Option UsePath :=
  (U.pkg? p).bind (·.topUse? n)

/-! ## Paths -/

/-- In package `p`, `path` resolves to the item `i` of kind `k`. -/
inductive ResolvesTo (U : Universe) (k : Kind) (p : PackageName) : UsePath → ItemId → Prop
  /-- `ns:pkg/name@v` names an item of a package of the universe. -/
  | foreign {q : PackageName} {n : Name} :
      U.has k ⟨q, n⟩ = true → ResolvesTo U k p (.foreign q n) ⟨q, n⟩
  /-- A local name of an item of `p`. -/
  | «local» {n : Name} : U.has k ⟨p, n⟩ = true → ResolvesTo U k p (.local n) ⟨p, n⟩
  /-- A local name bound by a top-level `use ns:pkg/m as n;` (local items take
  precedence; a valid package has no clash). -/
  | alias {n : Name} {q : PackageName} {m : Name} :
      U.has k ⟨p, n⟩ = false → U.topUse? p n = some (.foreign q m) →
      U.has k ⟨q, m⟩ = true → ResolvesTo U k p (.local n) ⟨q, m⟩

/-- Path resolution (`ResolvesTo`) as a function. -/
def resolve (U : Universe) (k : Kind) (p : PackageName) : UsePath → Option ItemId
  | .foreign q n => if U.has k ⟨q, n⟩ then some ⟨q, n⟩ else none
  | .local n =>
    if U.has k ⟨p, n⟩ then some ⟨p, n⟩
    else match U.topUse? p n with
      | some (.foreign q m) => if U.has k ⟨q, m⟩ then some ⟨q, m⟩ else none
      | _ => none

/-! ## Scopes -/

/-- An owner of type definitions. -/
inductive Owner where
  /-- A package interface. -/
  | iface (i : ItemId)
  /-- A world (its own type definitions and `use`s). -/
  | world (w : ItemId)
  /-- An inline interface `name: interface { … }` imported (`isExport = false`) or
  exported by a world. -/
  | inline (w : ItemId) (isExport : Bool) (name : Name)
  deriving Repr, DecidableEq, Inhabited

/-- The package of an owner. -/
def Owner.pkg : Owner → PackageName
  | .iface i | .world i | .inline i _ _ => i.pkg

/-- A type: its owner and name. -/
structure TypeId where
  owner : Owner
  name : Name
  deriving Repr, DecidableEq, Inhabited

/-- The items of an inline interface of a world. -/
def World.inline? (W : World) (isExport : Bool) (n : Name) : Option (List IfaceItem) :=
  W.items.findSome? fun
    | .import ⟨.iface m items, _, _⟩ => if !isExport ∧ m = n then some items else none
    | .export ⟨.iface m items, _, _⟩ => if isExport ∧ m = n then some items else none
    | _ => none

/-- An item that binds names in a scope. -/
inductive ScopeItem where
  | type (d : TypeDef)
  | use (u : Use)
  deriving Repr, DecidableEq, Inhabited

/-- The scope item of an interface item. -/
def IfaceItem.scope : IfaceItem → Option ScopeItem
  | .type d => some (.type d)
  | .use u => some (.use u)
  | .func _ => none

/-- The scope item of a world item. -/
def WorldItem.scope : WorldItem → Option ScopeItem
  | .type d => some (.type d)
  | .use u => some (.use u)
  | _ => none

/-- The scope items of an owner. -/
def Owner.scope (U : Universe) : Owner → Option (List ScopeItem)
  | .iface i => (U.iface? i).map fun I => I.items.filterMap IfaceItem.scope
  | .world w => (U.world? w).map fun W => W.items.filterMap WorldItem.scope
  | .inline w e n => ((U.world? w).bind (·.inline? e n)).map (·.filterMap IfaceItem.scope)

/-- What binds a name in a scope: a type definition, or `use path.{name}`. -/
inductive Src where
  | type (d : TypeDef)
  | use (path : UsePath) (name : Name)
  deriving Repr, DecidableEq, Inhabited

/-- What a scope item binds to `x`. -/
def ScopeItem.src? (x : Name) : ScopeItem → Option Src
  | .type d => if d.name = x then some (.type d) else none
  | .use u => (u.names.find? fun un => un.bound = x).map fun un => .use u.path un.name

/-- What binds `x` in the scope of an owner (the first binding). -/
def Owner.src? (U : Universe) (o : Owner) (x : Name) : Option Src :=
  (o.scope U).bind (·.findSome? (·.src? x))

/-- The definition of a type. -/
def Universe.typeDef? (U : Universe) (t : TypeId) : Option TypeDef :=
  match t.owner.src? U t.name with
  | some (.type d) => some d
  | _ => none

/-! ## Denotation of names -/

/-- The name `x` of interface `i` denotes the type `t`. -/
inductive Denotes (U : Universe) : ItemId → Name → TypeId → Prop
  /-- `x` is defined in `i`. -/
  | type {i : ItemId} {x : Name} {d : TypeDef} :
      (Owner.iface i).src? U x = some (.type d) → Denotes U i x ⟨.iface i, x⟩
  /-- `use path.{y as x}` in `i`, and `y` denotes `t` in the interface `path`. -/
  | use {i : ItemId} {x : Name} {path : UsePath} {y : Name} {j : ItemId} {t : TypeId} :
      (Owner.iface i).src? U x = some (.use path y) → ResolvesTo U .iface i.pkg path j →
      Denotes U j y t → Denotes U i x t

/-- The name `x` denotes `t` in the scope of the owner `o`. -/
inductive Binds (U : Universe) (o : Owner) (x : Name) : TypeId → Prop
  | type {d : TypeDef} : o.src? U x = some (.type d) → Binds U o x ⟨o, x⟩
  | use {path : UsePath} {y : Name} {j : ItemId} {t : TypeId} :
      o.src? U x = some (.use path y) → ResolvesTo U .iface o.pkg path j →
      Denotes U j y t → Binds U o x t

/-- `t` is a resource type, directly or through aliases `type r2 = r;`. -/
inductive IsResource (U : Universe) : TypeId → Prop
  | resource {t : TypeId} {d : TypeDef} {fs : List ResourceFunc} :
      U.typeDef? t = some d → d.kind = .resource fs → IsResource U t
  | alias {t : TypeId} {d : TypeDef} {n : Name} {t' : TypeId} :
      U.typeDef? t = some d → d.kind = .alias (.named n) → Binds U t.owner n t' →
      IsResource U t' → IsResource U t

/-- `Denotes` with fuel. -/
def denote (U : Universe) : Nat → ItemId → Name → Option TypeId
  | 0, _, _ => none
  | f + 1, i, x =>
    match (Owner.iface i).src? U x with
    | some (.type _) => some ⟨.iface i, x⟩
    | some (.use path y) => (resolve U .iface i.pkg path).bind fun j => denote U f j y
    | none => none

/-- `Binds` with fuel for the `use` chains. -/
def bind (U : Universe) (f : Nat) (o : Owner) (x : Name) : Option TypeId :=
  match o.src? U x with
  | some (.type _) => some ⟨o, x⟩
  | some (.use path y) => (resolve U .iface o.pkg path).bind fun j => denote U f j y
  | none => none

/-- `IsResource` with fuel `f` for `use` chains and `g` for alias chains. -/
def isRes (U : Universe) (f : Nat) : Nat → TypeId → Bool
  | 0, _ => false
  | g + 1, t =>
    match U.typeDef? t with
    | some ⟨_, .resource _, _, _⟩ => true
    | some ⟨_, .alias (.named n), _, _⟩ =>
      match bind U f t.owner n with
      | some t' => isRes U f g t'
      | none => false
    | _ => false

/-! ## References of types -/

/-- How a type expression refers to a name: as a type, or as the resource of a handle
(`own<r>`, `borrow<r>`). -/
inductive RefKind where
  | plain | handle
  deriving Repr, DecidableEq, Inhabited

/-- A reference to a name. -/
abbrev Ref := RefKind × Name

mutual
/-- The names a type expression refers to. -/
def Ty.refs : Ty → List Ref
  | .named n => [(.plain, n)]
  | .own n | .borrow n => [(.handle, n)]
  | .list t | .option t | .fixedList t _ => t.refs
  | .map k v => k.refs ++ v.refs
  | .tuple ts => Ty.refsList ts
  | .result a b => Ty.refsOpt a ++ Ty.refsOpt b
  | .future a | .stream a => Ty.refsOpt a
  | _ => []
/-- `Ty.refs` of an optional type. -/
def Ty.refsOpt : Option Ty → List Ref
  | none => []
  | some t => t.refs
/-- `Ty.refs` of a list of types. -/
def Ty.refsList : List Ty → List Ref
  | [] => []
  | t :: ts => t.refs ++ Ty.refsList ts
end

/-- The names a type definition refers to (resource functions excluded: a resource's
methods may mention the resource itself). -/
def TypeDef.refs (d : TypeDef) : List Ref :=
  match d.kind with
  | .alias t => t.refs
  | .record fs => fs.flatMap fun f => f.ty.refs
  | .variant cs => cs.flatMap fun c => Ty.refsOpt c.ty
  | .enum _ | .flags _ | .resource _ => []

/-! ## Dependency graphs -/

/-- The interfaces of a universe. -/
def Universe.ifaceIds (U : Universe) : List ItemId :=
  U.flatMap fun P => P.items.filterMap fun
    | .iface I => some ⟨P.name, I.name⟩
    | _ => none

/-- The worlds of a universe. -/
def Universe.worldIds (U : Universe) : List ItemId :=
  U.flatMap fun P => P.items.filterMap fun
    | .world W => some ⟨P.name, W.name⟩
    | _ => none

/-- The inline-interface owners of a world. -/
def World.inlineOwners (w : ItemId) (W : World) : List Owner :=
  W.items.filterMap fun
    | .import ⟨.iface n _, _, _⟩ => some (.inline w false n)
    | .export ⟨.iface n _, _, _⟩ => some (.inline w true n)
    | _ => none

/-- All owners of a universe. -/
def Universe.owners (U : Universe) : List Owner :=
  U.ifaceIds.map .iface ++ U.worldIds.flatMap fun w =>
    .world w :: match U.world? w with
      | some W => W.inlineOwners w
      | none => []

/-- All type definitions of a universe. -/
def Universe.typeIds (U : Universe) : List TypeId :=
  U.owners.flatMap fun o => ((o.scope U).getD []).filterMap fun
    | .type d => some ⟨o, d.name⟩
    | .use _ => none

/-- `i` uses a name of `j`. -/
def IfaceEdge (U : Universe) (i j : ItemId) : Prop :=
  ∃ I u, U.iface? i = some I ∧ IfaceItem.use u ∈ I.items ∧ ResolvesTo U .iface i.pkg u.path j

/-- The interfaces an interface uses. -/
def ifaceDeps (U : Universe) (i : ItemId) : List ItemId :=
  match U.iface? i with
  | some I => I.items.filterMap fun
    | .use u => resolve U .iface i.pkg u.path
    | _ => none
  | none => []

/-- The definition of `t` refers to `t'`. -/
def TypeEdge (U : Universe) (t t' : TypeId) : Prop :=
  ∃ d, U.typeDef? t = some d ∧ ∃ r ∈ d.refs, Binds U t.owner r.2 t'

/-- The types the definition of `t` refers to, with fuel `f` for `use` chains. -/
def typeDeps (U : Universe) (f : Nat) (t : TypeId) : List TypeId :=
  match U.typeDef? t with
  | some d => d.refs.filterMap fun r => bind U f t.owner r.2
  | none => []

/-- World `w` includes world `w'`. -/
def WorldEdge (U : Universe) (w w' : ItemId) : Prop :=
  ∃ W i, U.world? w = some W ∧ WorldItem.include i ∈ W.items ∧
    ResolvesTo U .world w.pkg i.path w'

/-- The worlds a world includes. -/
def worldDeps (U : Universe) (w : ItemId) : List ItemId :=
  match U.world? w with
  | some W => W.items.filterMap fun
    | .include i => resolve U .world w.pkg i.path
    | _ => none
  | none => []

end Silmaril.Wasm.Wit
