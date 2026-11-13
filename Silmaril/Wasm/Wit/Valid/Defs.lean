module

public import Silmaril.Wasm.Wit.Name.Defs
public import Silmaril.Wasm.Wit.Resolve.Defs
public import Silmaril.Wasm.Wit.Graph.Defs

/-!
# WIT: validation

`Valid U` states that a universe of WIT packages is well formed:

* package names are unique and valid; in each package, item names are unique and
  identifiers are kebab case (`Silmaril.Wasm.Wit.Name`); gates are accepted
  combinations (`GatesOk`);
* in each interface, world and inline interface, the names bound by type definitions,
  `use`s and functions are unique; world import names (named imports, type definitions,
  `use`d names) and export names are unique;
* record fields, variant cases, enum cases and flags are non-empty lists of unique
  valid labels (at most 32 flags); a resource has at most one constructor, which is
  synchronous and returns nothing explicitly, and unique method/static names;
  parameter names are unique; fixed-size lists have a positive length; function
  results contain no `borrow` (syntactically);
* name resolution (`Silmaril.Wasm.Wit.Resolve`): every referenced name denotes a type in
  its scope, every handle `own<r>`/`borrow<r>` a resource; every `use` path resolves
  to an interface and its names denote types there; interface imports/exports resolve
  to interfaces; `include` resolves to a world whose named imports/exports contain the
  `with` sources; top-level `use` names a foreign interface or world;
* the `use` graph of interfaces, the reference graph of type definitions and the
  `include` graph of worlds are acyclic.

The structural part `ValidWith L U` is parametric in the four resolution facts it
needs (`Leaves`): `specLeaves U` takes them from the relations of `Resolve`, and
`funLeaves U F G` from the fuelled functions. `check U` runs `Graph.kahn` on the three
graphs and decides `ValidWith (funLeaves …) U`. `Silmaril.Wasm.Wit.Valid.Thms` proves
`check U = true ↔ Valid U`.

Not checked here (later passes): the elaboration of `include` (the merged world,
clashes after `with` renaming), `borrow` in results through type aliases,
consistency of gates with package versions and features, and version matching other
than exact equality.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit

/-! ## Shapes of type expressions -/

mutual
/-- Every subexpression satisfies `p`. -/
def Ty.all (p : Ty → Bool) (t : Ty) : Bool :=
  p t && match t with
    | .list a | .option a | .fixedList a _ => Ty.all p a
    | .map k v => Ty.all p k && Ty.all p v
    | .tuple ts => Ty.allList p ts
    | .result a b => Ty.allOpt p a && Ty.allOpt p b
    | .future a | .stream a => Ty.allOpt p a
    | _ => true
/-- `Ty.all` on an optional type. -/
def Ty.allOpt (p : Ty → Bool) : Option Ty → Bool
  | none => true
  | some t => Ty.all p t
/-- `Ty.all` on a list of types. -/
def Ty.allList (p : Ty → Bool) : List Ty → Bool
  | [] => true
  | t :: ts => Ty.all p t && Ty.allList p ts
end

/-- Fixed-size lists have a positive length. -/
def Ty.shapeOk : Ty → Bool := Ty.all fun
  | .fixedList _ n => 0 < n
  | _ => true

/-- No `borrow` occurs syntactically. -/
def Ty.noBorrow : Ty → Bool := Ty.all fun
  | .borrow _ => false
  | _ => true

/-! ## Names bound by items -/

/-- The names an interface item binds. -/
def IfaceItem.names : IfaceItem → List Name
  | .type d => [d.name]
  | .use u => u.names.map UseName.bound
  | .func f => [f.name]

/-- The import names a world item binds. -/
def WorldItem.importNames : WorldItem → List Name
  | .import ⟨.func n _, _, _⟩ | .import ⟨.iface n _, _, _⟩ => [n]
  | .type d => [d.name]
  | .use u => u.names.map UseName.bound
  | _ => []

/-- The export names a world item binds. -/
def WorldItem.exportNames : WorldItem → List Name
  | .export ⟨.func n _, _, _⟩ | .export ⟨.iface n _, _, _⟩ => [n]
  | _ => []

/-- The named imports and exports of a world (what `include … with` may rename). -/
def World.externNames (W : World) : List Name :=
  W.items.flatMap fun
    | .import ⟨.func n _, _, _⟩ | .import ⟨.iface n _, _, _⟩
    | .export ⟨.func n _, _, _⟩ | .export ⟨.iface n _, _, _⟩ => [n]
    | _ => []

/-- The name a package item binds. -/
def PackageItem.name : PackageItem → Name
  | .iface i => i.name
  | .world w => w.name
  | .use u => u.bound

/-- The method or static function name of a resource function. -/
def ResourceFuncKind.name? : ResourceFuncKind → Option Name
  | .ctor => none
  | .method n | .static n => some n

/-- A path names a foreign package. -/
def UsePath.isForeign : UsePath → Bool
  | .foreign _ _ => true
  | .local _ => false

/-! ## Resolution facts -/

/-- The resolution facts validation depends on. -/
structure Leaves where
  /-- In the scope of an owner, a reference denotes a type (a resource for handles). -/
  ref : Owner → Ref → Prop
  /-- In a package, a `use` path resolves to an interface in which a name denotes a
  type. -/
  use : PackageName → UsePath → Name → Prop
  /-- In a package, a path resolves to an item of a kind. -/
  path : Kind → PackageName → UsePath → Prop
  /-- In a package, an `include` path resolves to a world with the given named imports
  or exports. -/
  incl : PackageName → UsePath → List Name → Prop

/-- Decidability of the resolution facts. -/
class Leaves.Dec (L : Leaves) where
  ref : ∀ o r, Decidable (L.ref o r)
  use : ∀ p path y, Decidable (L.use p path y)
  path : ∀ k p path, Decidable (L.path k p path)
  incl : ∀ p path ns, Decidable (L.incl p path ns)

instance (L : Leaves) [h : L.Dec] (o : Owner) (r : Ref) : Decidable (L.ref o r) := h.ref o r
instance (L : Leaves) [h : L.Dec] (p : PackageName) (path : UsePath) (y : Name) :
    Decidable (L.use p path y) := h.use p path y
instance (L : Leaves) [h : L.Dec] (k : Kind) (p : PackageName) (path : UsePath) :
    Decidable (L.path k p path) := h.path k p path
instance (L : Leaves) [h : L.Dec] (p : PackageName) (path : UsePath) (ns : List Name) :
    Decidable (L.incl p path ns) := h.incl p path ns

/-- The resolution facts given by the relations of `Resolve`. -/
def specLeaves (U : Universe) : Leaves where
  ref o r := ∃ t, Binds U o r.2 t ∧ (r.1 = .handle → IsResource U t)
  use p path y := ∃ j t, ResolvesTo U .iface p path j ∧ Denotes U j y t
  path k p path := ∃ j, ResolvesTo U k p path j
  incl p path ns := ∃ w W, ResolvesTo U .world p path w ∧ U.world? w = some W ∧
    ∀ n ∈ ns, n ∈ W.externNames

/-- `ref` computed with fuel. -/
def refB (U : Universe) (F G : Nat) (o : Owner) (r : Ref) : Bool :=
  match bind U F o r.2 with
  | some t => r.1 == .plain || isRes U F G t
  | none => false

/-- `use` computed with fuel. -/
def useB (U : Universe) (F : Nat) (p : PackageName) (path : UsePath) (y : Name) : Bool :=
  match resolve U .iface p path with
  | some j => (denote U F j y).isSome
  | none => false

/-- `incl` computed. -/
def inclB (U : Universe) (p : PackageName) (path : UsePath) (ns : List Name) : Bool :=
  match resolve U .world p path with
  | some w =>
    match U.world? w with
    | some W => ns.all fun n => W.externNames.contains n
    | none => false
  | none => false

/-- The resolution facts given by the fuelled functions. -/
def funLeaves (U : Universe) (F G : Nat) : Leaves where
  ref o r := refB U F G o r = true
  use p path y := useB U F p path y = true
  path k p path := (resolve U k p path).isSome = true
  incl p path ns := inclB U p path ns = true

instance (U : Universe) (F G : Nat) : (funLeaves U F G).Dec where
  ref _ _ := inferInstanceAs (Decidable (_ = true))
  use _ _ _ := inferInstanceAs (Decidable (_ = true))
  path _ _ _ := inferInstanceAs (Decidable (_ = true))
  incl _ _ _ := inferInstanceAs (Decidable (_ = true))

/-! ## Structural validity -/

section
variable (L : Leaves)

/-- A type expression is well formed in the scope of `o`. -/
def TyOk (o : Owner) (t : Ty) : Prop := t.shapeOk = true ∧ ∀ r ∈ t.refs, L.ref o r

/-- A function type is well formed in the scope of `o`. -/
def FuncOk (o : Owner) (f : Func) : Prop :=
  (f.params.map (·.1)).Nodup ∧ (∀ p ∈ f.params, ValidId p.1 ∧ TyOk L o p.2) ∧
    ∀ t ∈ f.result, TyOk L o t ∧ t.noBorrow = true

/-- A resource function is well formed. -/
def ResourceFuncOk (o : Owner) (rf : ResourceFunc) : Prop :=
  GatesOk rf.gates ∧ (∀ n ∈ rf.kind.name?, ValidId n) ∧ FuncOk L o rf.func ∧
    (rf.kind = .ctor → rf.func.result = none ∧ rf.func.async = false)

/-- Non-empty unique valid labels. -/
def LabelsOk (ns : List Name) : Prop := ns ≠ [] ∧ ns.Nodup ∧ ∀ n ∈ ns, ValidId n

/-- The body of a type definition is well formed. -/
def KindOk (o : Owner) : TypeDefKind → Prop
  | .alias t => TyOk L o t
  | .record fs => LabelsOk (fs.map (·.name)) ∧ ∀ f ∈ fs, TyOk L o f.ty
  | .variant cs => LabelsOk (cs.map (·.name)) ∧ ∀ c ∈ cs, ∀ t ∈ c.ty, TyOk L o t
  | .enum ls => LabelsOk (ls.map (·.name))
  | .flags ls => LabelsOk (ls.map (·.name)) ∧ ls.length ≤ 32
  | .resource fns =>
    (fns.filter fun rf => rf.kind == .ctor).length ≤ 1 ∧
      (fns.filterMap (·.kind.name?)).Nodup ∧ ∀ rf ∈ fns, ResourceFuncOk L o rf

/-- A type definition is well formed. -/
def TypeDefOk (o : Owner) (d : TypeDef) : Prop :=
  ValidId d.name ∧ GatesOk d.gates ∧ KindOk L o d.kind

/-- A `use` in package `p` is well formed. -/
def UseOk (p : PackageName) (u : Use) : Prop :=
  GatesOk u.gates ∧ L.path .iface p u.path ∧
    ∀ un ∈ u.names, ValidId un.name ∧ (∀ a ∈ un.as, ValidId a) ∧ L.use p u.path un.name

/-- An interface item is well formed. -/
def IfaceItemOk (o : Owner) : IfaceItem → Prop
  | .type d => TypeDefOk L o d
  | .use u => UseOk L o.pkg u
  | .func f => ValidId f.name ∧ GatesOk f.gates ∧ FuncOk L o f.func

/-- The items of an interface (or inline interface) owned by `o` are well formed. -/
def ItemsOk (o : Owner) (items : List IfaceItem) : Prop :=
  (items.flatMap IfaceItem.names).Nodup ∧ ∀ it ∈ items, IfaceItemOk L o it

/-- An interface of package `p` is well formed. -/
def InterfaceOk (p : PackageName) (I : Interface) : Prop :=
  ValidId I.name ∧ GatesOk I.gates ∧ ItemsOk L (.iface ⟨p, I.name⟩) I.items

/-- What an import (`isExport = false`) or export of world `w` names is well formed. -/
def ExternOk (w : ItemId) (isExport : Bool) : Extern → Prop
  | .func n f => ValidId n ∧ FuncOk L (.world w) f
  | .iface n items => ValidId n ∧ ItemsOk L (.inline w isExport n) items
  | .path p => L.path .iface w.pkg p

/-- An item of world `w` is well formed. -/
def WorldItemOk (w : ItemId) : WorldItem → Prop
  | .import e => GatesOk e.gates ∧ ExternOk L w false e.ext
  | .export e => GatesOk e.gates ∧ ExternOk L w true e.ext
  | .use u => UseOk L w.pkg u
  | .type d => TypeDefOk L (.world w) d
  | .include i =>
    GatesOk i.gates ∧ (i.names.map (·.name)).Nodup ∧ (∀ n ∈ i.names, ValidId n.as) ∧
      L.incl w.pkg i.path (i.names.map (·.name))

/-- A world of package `p` is well formed. -/
def WorldOk (p : PackageName) (W : World) : Prop :=
  ValidId W.name ∧ GatesOk W.gates ∧ (W.items.flatMap WorldItem.importNames).Nodup ∧
    (W.items.flatMap WorldItem.exportNames).Nodup ∧ ∀ it ∈ W.items, WorldItemOk L ⟨p, W.name⟩ it

/-- An item of package `P` is well formed. -/
def PackageItemOk (p : PackageName) : PackageItem → Prop
  | .iface I => InterfaceOk L p I
  | .world W => WorldOk L p W
  | .use u => GatesOk u.gates ∧ ValidId u.bound ∧ u.path.isForeign = true ∧
    (L.path .iface p u.path ∨ L.path .world p u.path)

/-- A package is well formed. -/
def PackageOk (P : Package) : Prop :=
  P.name.Valid ∧ (P.items.map PackageItem.name).Nodup ∧ ∀ it ∈ P.items, PackageItemOk L P.name it

/-- The structural validity of a universe, given the resolution facts. -/
def ValidWith (U : Universe) : Prop := (U.map (·.name)).Nodup ∧ ∀ P ∈ U, PackageOk L P

end

/-! ## Decidability -/

section
variable (L : Leaves) [L.Dec]

instance (o : Owner) (t : Ty) : Decidable (TyOk L o t) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ ∈ _, _))
instance (o : Owner) (f : Func) : Decidable (FuncOk L o f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _ ∈ _, _))
instance (o : Owner) (rf : ResourceFunc) : Decidable (ResourceFuncOk L o rf) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _ ∈ _, _) ∧ _ ∧ _))
instance (ns : List Name) : Decidable (LabelsOk ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (o : Owner) (k : TypeDefKind) : Decidable (KindOk L o k) :=
  match k with
  | .alias _ => inferInstanceAs (Decidable (TyOk L o _))
  | .record _ | .variant _ | .flags _ | .resource _ => inferInstanceAs (Decidable (_ ∧ _))
  | .enum _ => inferInstanceAs (Decidable (LabelsOk _))
instance (o : Owner) (d : TypeDef) : Decidable (TypeDefOk L o d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (p : PackageName) (u : Use) : Decidable (UseOk L p u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (o : Owner) (it : IfaceItem) : Decidable (IfaceItemOk L o it) :=
  match it with
  | .type _ => inferInstanceAs (Decidable (TypeDefOk L o _))
  | .use _ => inferInstanceAs (Decidable (UseOk L _ _))
  | .func _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (o : Owner) (items : List IfaceItem) : Decidable (ItemsOk L o items) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (p : PackageName) (I : Interface) : Decidable (InterfaceOk L p I) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (w : ItemId) (b : Bool) (e : Extern) : Decidable (ExternOk L w b e) :=
  match e with
  | .func _ _ | .iface _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .path _ => inferInstanceAs (Decidable (L.path _ _ _))
instance (w : ItemId) (it : WorldItem) : Decidable (WorldItemOk L w it) :=
  match it with
  | .import _ | .export _ => inferInstanceAs (Decidable (_ ∧ _))
  | .use _ => inferInstanceAs (Decidable (UseOk L _ _))
  | .type _ => inferInstanceAs (Decidable (TypeDefOk L _ _))
  | .include _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (p : PackageName) (W : World) : Decidable (WorldOk L p W) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
instance (p : PackageName) (it : PackageItem) : Decidable (PackageItemOk L p it) :=
  match it with
  | .iface _ => inferInstanceAs (Decidable (InterfaceOk L _ _))
  | .world _ => inferInstanceAs (Decidable (WorldOk L _ _))
  | .use _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (P : Package) : Decidable (PackageOk L P) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (U : Universe) : Decidable (ValidWith L U) :=
  inferInstanceAs (Decidable (_ ∧ _))

end

/-! ## Validity and the checker -/

/-- A valid universe of WIT packages. -/
structure Valid (U : Universe) : Prop where
  /-- Names, labels, gates and resolution of every package. -/
  pkgs : ValidWith (specLeaves U) U
  /-- Interface `use`s are acyclic. -/
  ifaceAcyclic : ∃ r : ItemId → Nat, ∀ i j, IfaceEdge U i j → r j < r i
  /-- Type definitions do not refer to themselves, directly or indirectly. -/
  typeAcyclic : ∃ s : TypeId → Nat, ∀ t t', TypeEdge U t t' → s t' < s t
  /-- World `include`s are acyclic. -/
  worldAcyclic : ∃ r : ItemId → Nat, ∀ w w', WorldEdge U w w' → r w' < r w

/-- The validity checker. -/
def check (U : Universe) : Bool :=
  Graph.kahn (ifaceDeps U) U.ifaceIds &&
    Graph.kahn (typeDeps U U.ifaceIds.length) U.typeIds &&
    Graph.kahn (worldDeps U) U.worldIds &&
    decide (ValidWith (funLeaves U U.ifaceIds.length U.typeIds.length) U)

/-- The packages of a document are valid on their own, in a universe with their
dependencies `deps`. -/
def Document.check (d : Document) (deps : Universe := []) : Bool := Wit.check (d.packages ++ deps)

end Silmaril.Wasm.Wit
