module

public import Silmaril.Wasm.Wit.Binary.Model.Defs

/-!
# WIT packages as type-only components: the encoder

`encodePackage deps p` is the component that wit-component's `encode`
(wit-component `0.263.0`, `src/encoding/wit.rs` and `src/encoding/types.rs`)
writes for the package `p`, as an abstract component (`Component.Binary.Ast`);
its bytes are `Component.Binary.encode` of it. The algorithm is transcribed
step by step, with the same state:

* each interface of `p` becomes a component type that imports every interface
  it uses types from (`liveDeps`, types only), aliases the used types out of
  those instances, and exports the interface itself as an instance type
  (`encodeIface`);
* each world becomes a component type exporting a component type whose
  imports and exports are the world's (`encodeWorld`);
* inside one index space, anonymous types are shared by structure
  (`Maps.anon`, wit-component's `def_to_index`), function types by signature
  (`Maps.funcs`, `func_type_map`), named types by name (`Maps.named`,
  `id_to_index`); a foreign type is aliased out of its instance once per
  component type (`Enc.outerTypes`, `outer_type_map`).

Named types must be defined before they are used (wit-parser's resolver
sorts the types of an interface topologically); a use before the definition
is an encoding error here, where wit-component would define the type at the
use. Functions are encoded resource by resource (`sortFuncs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

/-! ## Lookup tables -/

/-- The first value of key `k`. -/
def lookup {α : Type} [DecidableEq α] (k : α) : List (α × Nat) → Option Nat
  | [] => none
  | (a, n) :: xs => if a = k then some n else lookup k xs

/-- The type tables of one index space (wit-component's `TypeEncodingMaps`);
the newest entry comes first. -/
structure Maps where
  named : List (TyRef × Nat) := []
  anon : List (Ty × Nat) := []
  funcs : List (Sig × Nat) := []
  deriving Repr, Inhabited

/-- One index space being written: its declarations (in order), its number of
types, its tables. -/
structure Space (δ : Type) where
  decls : List δ := []
  count : Nat := 0
  maps : Maps := {}
  deriving Inhabited

/-- Encoder state: the component type being written, the instance type being
written inside it (if any), the instances of the component type and the
foreign types aliased out of them. -/
structure Enc where
  outer : Space ComponentDecl := {}
  inner : Option (Space InstanceDecl) := none
  insts : Nat := 0
  instOf : List (IfaceName × Nat) := []
  outerTypes : List ((IfaceName × String) × Nat) := []
  /-- Whether named types of the component type are imported (world types). -/
  importTypes : Bool := false
  deriving Inhabited

abbrev EncM := StateT Enc (Except String)

namespace Enc

def fail {α : Type} (msg : String) : EncM α := throw msg

/-- The tables of the current index space. -/
def maps : EncM Maps := do
  let e ← get
  pure (match e.inner with | some s => s.maps | none => e.outer.maps)

def setMaps (m : Maps) : EncM Unit := modify fun e =>
  match e.inner with
  | some s => { e with inner := some { s with maps := m } }
  | none => { e with outer := { e.outer with maps := m } }

/-- Append a type-defining declaration to the current space; its index. -/
def defType (t : DefType) : EncM Nat := do
  let e ← get
  match e.inner with
  | some s =>
    set { e with inner := some { s with decls := s.decls ++ [InstanceDecl.type t], count := s.count + 1 } }
    pure s.count
  | none =>
    set { e with outer := { e.outer with decls := e.outer.decls ++ [ComponentDecl.inst (.type t)], count := e.outer.count + 1 } }
    pure e.outer.count

/-- Silmaril.Wasm.Component.Binary.Export (or, for world types, import) a type of the current space under
`n`; the index of the new type. -/
def exportType (n : String) (b : TypeBound) : EncM Nat := do
  let e ← get
  match e.inner with
  | some s =>
    set { e with inner := some { s with decls := s.decls ++ [InstanceDecl.export ↑n (.type b)], count := s.count + 1 } }
    pure s.count
  | none =>
    let d : ComponentDecl := if e.importTypes then .import ↑n (.type b) else .inst (.export ↑n (.type b))
    set { e with outer := { e.outer with decls := e.outer.decls ++ [d], count := e.outer.count + 1 } }
    pure e.outer.count

def insertNamed (r : TyRef) (k : Nat) : EncM Unit := do
  let m ← maps
  setMaps { m with named := (r, k) :: m.named }

def insertAnon (t : Ty) (k : Nat) : EncM Unit := do
  let m ← maps
  setMaps { m with anon := (t, k) :: m.anon }

/-- The alias of type `n` of the imported interface `i` in the component
type, made once (`outer_type_map`). -/
def outerAliasSt (i : IfaceName) (n : String) (e : Enc) : Except String (Nat × Enc) :=
  match lookup i e.instOf with
  | none => .error s!"type `{n}` of interface `{i.id}` used before the interface is imported"
  | some inst =>
    match lookup (i, n) e.outerTypes with
    | some k => .ok (k, e)
    | none => .ok (e.outer.count,
      { e with outer := { e.outer with decls := e.outer.decls ++ [ComponentDecl.inst (.alias ⟨.type, .export inst n⟩)],
                                       count := e.outer.count + 1 },
               outerTypes := ((i, n), e.outer.count) :: e.outerTypes })

/-- Inside an instance type, the outer alias of the outer type `k`. -/
def innerAliasSt (k : Nat) (e : Enc) : Nat × Enc :=
  match e.inner with
  | some s => (s.count, { e with inner := some { s with decls := s.decls ++ [InstanceDecl.alias ⟨.type, .outer 1 k⟩],
                                                         count := s.count + 1 } })
  | none => (k, e)

/-- `import_type`: alias the type `n` of the imported interface `i`. -/
def importType (i : IfaceName) (n : String) : EncM Nat := do
  let k ← (outerAliasSt i n : EncM Nat)
  (fun e => .ok (innerAliasSt k e) : EncM Nat)

/-- The index of a named type, aliasing it in when it is foreign. -/
def refIdx (r : TyRef) : EncM Nat := do
  let m ← maps
  match lookup r m.named with
  | some k => pure k
  | none =>
    match r.owner with
    | .local => fail s!"type `{r.name}` used before its definition"
    | .iface i => do
      let k ← importType i r.name
      insertNamed r k
      pure k

/-- Look an anonymous type up, or define it with `mk` and record it. -/
def anon (t : Ty) (mk : EncM DefValType) : EncM Silmaril.Wasm.Component.Binary.ValType := do
  let m ← maps
  match lookup t m.anon with
  | some k => pure (.idx k)
  | none => do
    let d ← mk
    let k ← defType (.val d)
    insertAnon t k
    pure (.idx k)

mutual
/-- `encode_valtype`. -/
def valType : Ty → EncM Silmaril.Wasm.Component.Binary.ValType
  | .prim p => pure (.prim p)
  | .ref r => .idx <$> refIdx r
  | .list t => anon (.list t) (.list <$> valType t)
  | .fixedList t n => anon (.fixedList t n) ((.fixedList · n) <$> valType t)
  | .map k v => anon (.map k v) (do
      let a ← valType k
      let b ← valType v
      pure (.map a b))
  | .option t => anon (.option t) (.option <$> valType t)
  | .result o e => anon (.result o e) (do
      let a ← optValType o
      let b ← optValType e
      pure (.result a b))
  | .tuple ts => anon (.tuple ts) (.tuple <$> valTypes ts)
  | .own r => anon (.own r) (.own <$> refIdx r)
  | .borrow r => anon (.borrow r) (.borrow <$> refIdx r)
  | .future t => anon (.future t) (.future <$> optValType t)
  | .stream t => anon (.stream t) (.stream <$> optValType t)

def optValType : Option Ty → EncM (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some t => some <$> valType t

def valTypes : List Ty → EncM (List Silmaril.Wasm.Component.Binary.ValType)
  | [] => pure []
  | t :: ts => do
    let a ← valType t
    let b ← valTypes ts
    pure (a :: b)
end

/-- The definition of a type as a fresh definition (for a named type whose
kind is not a reference); its components are encoded first. -/
def structural : Ty → EncM DefValType
  | .prim p => pure (.prim p)
  | .ref _ => fail "a reference has no structural definition"
  | .list t => .list <$> valType t
  | .fixedList t n => (.fixedList · n) <$> valType t
  | .map k v => do
    let a ← valType k
    let b ← valType v
    pure (.map a b)
  | .option t => .option <$> valType t
  | .result o e => do
    let a ← optValType o
    let b ← optValType e
    pure (.result a b)
  | .tuple ts => .tuple <$> valTypes ts
  | .own r => .own <$> refIdx r
  | .borrow r => .borrow <$> refIdx r
  | .future t => .future <$> optValType t
  | .stream t => .stream <$> optValType t

def fields : List (Labeled Ty) → EncM (List (String × Silmaril.Wasm.Component.Binary.ValType))
  | [] => pure []
  | f :: fs => do
    let a ← valType f.ty
    let b ← fields fs
    pure ((f.name, a) :: b)

def cases : List (Labeled (Option Ty)) → EncM (List (String × Option Silmaril.Wasm.Component.Binary.ValType))
  | [] => pure []
  | c :: cs => do
    let a ← optValType c.ty
    let b ← cases cs
    pure ((c.name, a) :: b)

def params : List (String × Ty) → EncM (List (String × Silmaril.Wasm.Component.Binary.ValType))
  | [] => pure []
  | p :: ps => do
    let a ← valType p.2
    let b ← params ps
    pure ((p.1, a) :: b)

/-- The index a named type's definition gets (before it is named). -/
def typeDefIdx : TyDefKind → EncM Nat
  | .record fs => do
    let fs ← fields fs
    defType (.val (.record fs))
  | .variant cs => do
    let cs ← cases cs
    defType (.val (.variant cs))
  | .enum cs => defType (.val (.enum (cs.map (·.name))))
  | .flags fs => defType (.val (.flags (fs.map (·.name))))
  | .type (.ref r) => refIdx r
  | .type t => do
    let d ← structural t
    defType (.val d)
  | .resource => fail "unreachable"

/-- Encode the named type `td` of the current space (`encode_valtype` of a
named type id). -/
def typeDef (td : TypeDef) : EncM Unit :=
  match td.kind with
  | .resource => do
    let k ← exportType td.name .subResource
    insertNamed ⟨.local, td.name⟩ k
  | kind => do
    let idx ← typeDefIdx kind
    let k ← exportType td.name (.eq idx)
    insertNamed ⟨.local, td.name⟩ k

def typeDefs : List TypeDef → EncM Unit
  | [] => pure ()
  | td :: tds => do
    typeDef td
    typeDefs tds

/-- `encode_func_type`. -/
def funcType (f : Func) : EncM Nat := do
  let m ← maps
  match lookup f.sig m.funcs with
  | some k => pure k
  | none => do
    let ps ← params f.params
    let r ← optValType f.result
    let k ← defType (.func ⟨ps, r, f.async⟩)
    let m ← maps
    setMaps { m with funcs := (f.sig, k) :: m.funcs }
    pure k

/-- Begin an instance type (`push_instance`). -/
def push : EncM Unit := modify fun e => { e with inner := some {} }

/-- End an instance type and define it in the component type
(`pop_instance` and `ty().instance(..)`); its type index. The instance is
recorded as the next instance (of interface `i`, if named). -/
def pop (i : Option IfaceName) : EncM Nat := do
  let e ← get
  let some s := e.inner | fail "no instance type"
  let k := e.outer.count
  set { e with inner := none, outer := { e.outer with decls := e.outer.decls ++ [ComponentDecl.inst (.type (.instance s.decls))], count := k + 1 }, insts := e.insts + 1, instOf := match i with | some i => (i, e.insts) :: e.instOf | none => e.instOf }
  pure k

end Enc

open Enc

/-! ## Interfaces and worlds -/

/-- wit-component's order of functions: those of each resource, in the order
of the resources among the types, then the freestanding ones. -/
def funcKey (types : List TypeDef) (f : Func) : Nat :=
  match f.kind.resource? with
  | none => types.length
  | some r => (types.findIdx? (·.name = r)).getD types.length

def sortFuncs (types : List TypeDef) (fs : List Func) : List Func :=
  (List.range (types.length + 1)).flatMap fun i => fs.filter (funcKey types · = i)

/-- Silmaril.Wasm.Component.Binary.Export the function `f` from the instance type being written. -/
def exportFunc (f : Func) : EncM Unit := do
  let k ← funcType f
  modify fun e => match e.inner with
    | some s => { e with inner := some { s with decls := s.decls ++ [InstanceDecl.export ↑f.mangled (.func k)] } }
    | none => e

def exportFuncs : List Func → EncM Unit
  | [] => pure ()
  | f :: fs => do
    exportFunc f
    exportFuncs fs

/-- `encode_instance`: an instance type with the types and functions of an
interface body; its type index in the component type. -/
def encodeInstance (i : Option IfaceName) (body : Interface) : EncM Nat := do
  push
  typeDefs body.types
  exportFuncs (sortFuncs body.types body.funcs)
  pop i

/-- An instance type with the types (only) of an interface body. -/
def encodeTypesOnly (i : IfaceName) (body : Interface) : EncM Nat := do
  push
  typeDefs body.types
  pop (some i)

/-- The interfaces an interface uses types from (`interface_direct_deps`). -/
def directDeps (body : Interface) : List IfaceName :=
  body.types.filterMap fun td => match td.kind with
    | .type (.ref ⟨.iface j, _⟩) => some j
    | _ => none

/-- `add_live_interfaces`: dependencies first (depth first, each once), then
`i`; `fuel` bounds the depth. -/
def liveDeps (env : Env) : Nat → IfaceName → List IfaceName → List IfaceName
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    if i ∈ acc then acc else
    let deps := match lookup' i env with
      | some b => directDeps b
      | none => []
    let acc := deps.foldl (fun acc j => liveDeps env fuel j acc) acc
    if i ∈ acc then acc else acc ++ [i]
where
  lookup' (i : IfaceName) : Env → Option Interface
    | [] => none
    | (j, b) :: xs => if j = i then some b else lookup' i xs

def Env.find? (env : Env) (i : IfaceName) : Option Interface := liveDeps.lookup' i env

/-- Emit a declaration in the component type. -/
def emit (d : ComponentDecl) : EncM Unit :=
  modify fun e => { e with outer := { e.outer with decls := e.outer.decls ++ [d] } }

/-- One part of an interface's component type: the interface itself
(exported) or a live dependency (imported, types only). -/
def ifacePart (env : Env) (i : IfaceName) (body : Interface) (j : IfaceName) : EncM Unit :=
  if j = i then do
    let k ← encodeInstance (some i) body
    emit (.inst (.export ↑i.id (.instance k)))
  else
    match env.find? j with
    | some b => do
      let k ← encodeTypesOnly j b
      emit (.import ↑j.id (.instance k))
    | none => fail s!"unknown interface `{j.id}`"

/-- The parts of an interface's component type, in the order of `live`. -/
def ifaceParts (env : Env) (i : IfaceName) (body : Interface) : List IfaceName → EncM Unit
  | [] => pure ()
  | j :: js => do
    ifacePart env i body j
    ifaceParts env i body js

/-- `encode_interface`: the component type of interface `i`. -/
def encodeIface (env : Env) (i : IfaceName) (body : Interface) : Except String (List ComponentDecl) := do
  let ((), e) ← (ifaceParts env i body (liveDeps env (env.length + 1) i [])).run {}
  pure e.outer.decls

/-- One import (`imp`) or export of a world. -/
def worldItem (env : Env) (imp : Bool) : WorldItem → EncM Unit
  | .ifaceRef j _ _ => do
    let some b := env.find? j | fail s!"unknown interface `{j.id}`"
    let k ← encodeInstance (some j) b
    emit (if imp then .import ↑j.id (.instance k) else .inst (.export ↑j.id (.instance k)))
  | .ifaceInline n b => do
    let k ← encodeInstance none b
    emit (if imp then .import ↑n (.instance k) else .inst (.export ↑n (.instance k)))
  | .func f => do
    let k ← funcType f
    emit (if imp then .import ↑f.mangled (.func k) else .inst (.export ↑f.mangled (.func k)))
  | .type td =>
    if imp then do
      modify fun e => { e with importTypes := true }
      typeDef td
      modify fun e => { e with importTypes := false }
    else fail "a world cannot export a type"

def worldItems (env : Env) (imp : Bool) : List WorldItem → EncM Unit
  | [] => pure ()
  | it :: its => do
    worldItem env imp it
    worldItems env imp its

/-- `encode_world`: the component type of a world. -/
def encodeWorld (env : Env) (w : World) : Except String (List ComponentDecl) := do
  let ((), e) ← (do worldItems env true w.imports; worldItems env false w.exports).run {}
  pure e.outer.decls

/-! ## Packages -/

/-- The environment of a package: its own interfaces, then `deps`. -/
def Package.env (p : Package) (deps : Env) : Env :=
  p.interfaces.map (fun (n, b) => (p.name.iface n, b)) ++ deps

/-- The two sections exporting the `k`-th item (type index `2 k`). -/
def itemSections (k : Nat) (name : String) (decls : List ComponentDecl) : List Section :=
  [.types [.component decls], .exports [⟨↑name, ⟨.type, 2 * k⟩, none⟩]]

/-- The component type wrapping a world: it defines the world's component
type and exports it as `ns:pkg/world`. -/
def worldWrapper (p : PackageName) (n : String) (decls : List ComponentDecl) : List ComponentDecl :=
  [.inst (.type (.component decls)), .inst (.export ↑(p.iface n).id (.component 0))]

/-- An interface of the package, with its component type. -/
def encodeIfaceItem (env : Env) (p : PackageName) (nb : String × Interface) :
    Except String (String × List ComponentDecl) := do
  let ds ← encodeIface env (p.iface nb.1) nb.2
  pure (nb.1, ds)

/-- A world of the package, with its wrapper component type. -/
def encodeWorldItem (env : Env) (p : PackageName) (nw : String × World) :
    Except String (String × List ComponentDecl) := do
  let ds ← encodeWorld env nw.2
  pure (nw.1, worldWrapper p nw.1 ds)

/-- The sections exporting the items, the `k`-th from index `k`. -/
def allItemSections (items : List (String × List ComponentDecl)) (k : Nat := 0) : List Section :=
  (items.zipIdx k).flatMap fun x => itemSections x.2 x.1.1 x.1.2

/-- The item sections of a package (without custom sections). -/
def encodeItems (deps : Env) (p : Package) : Except String (List Section) := do
  let env := p.env deps
  let ifs ← p.interfaces.mapM (encodeIfaceItem env p.name)
  let ws ← p.worlds.mapM (encodeWorldItem env p.name)
  pure (allItemSections (ifs ++ ws))

end Silmaril.Wasm.Wit.Binary
