module

public import Silmaril.Wasm.Wac.Bridge.Decode.Defs

/-!
# WAC: the type of a component binary, by inference over its sections

`Bridge.decodePkg` reads a package's type off the *world* of the component
(`Wit.Project.projectI`), which keeps the component's own type indices and so fails on
components whose exported instances have no instance type of their own: an inline instance
`(instance (export "f" (func 0)))` exported without an ascription, or an instance of a nested
component (the shim components of `wit-component`, so every component `wasm-tools component
new` or `jco` writes for an interface export).

`typeOf c` infers the kinds directly, replaying the sections with one table per index space:

* types: as `Bridge.decDefType` (value, function, instance and component types, with their
  outer aliases); functions: the signature of their type (`canon lift`, imports, aliases);
  instances: their export tables; components: their imports and exports;
* a nested component `(component …)` is inferred recursively in a nested scope;
  `(instantiate c …)` has the exports of component `c`; an inline instance the kinds of its
  items; `(alias export i "n" …)` the kind of export `n` of instance `i`;
* an export has the kind of its item, or of its ascription when it has one.

Core modules, core instances, core types and custom sections have no component-level type
and are skipped; `canon lower` and the resource built-ins define core functions only.
A resource *definition* (`(type (resource …))`) takes the next type index under a placeholder
name, and is named by the first export (or inline-instance item) of that index: it is then the
resource of that name (`.type (.resource n)`), as an exported resource of a world
(`typeItem`). Outside: `start`, values, and outer aliases of anything but types. Like `decodePkg`, this is executable glue with no theorem: the tests
compare the composed binaries with `wac` and validate them with `wasm-tools`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open Silmaril.Wasm.Wac.Bridge (DScope DM TInfo)

/-- The state of the inference. -/
structure TS where
  sc : DScope := {}
  funcs : Array Sig := #[]
  comps : Array (Externs × Externs) := #[]
  imports : Externs := []
  exports : Externs := []
  deriving Inhabited

abbrev TM := StateT TS (Except String)

/-- Run a computation of the decoder on the type scope. -/
def liftD {α : Type} (m : DM α) : TM α := do
  let s ← get
  match m.run s.sc with
  | .ok (a, sc) => set { s with sc := sc }; pure a
  | .error e => throw e

def funcAt (i : Nat) : TM Sig := do
  match (← get).funcs[i]? with
  | some f => pure f
  | none => throw s!"unknown function index {i}"

def instAt (i : Nat) : TM Externs := do
  match (← get).sc.insts[i]? with
  | some es => pure es
  | none => throw s!"unknown instance index {i}"

def compAt (i : Nat) : TM (Externs × Externs) := do
  match (← get).comps[i]? with
  | some c => pure c
  | none => throw s!"unknown component index {i}"

def pushFunc (f : Sig) : TM Unit := modify fun s => { s with funcs := s.funcs.push f }
def pushInst (es : Externs) : TM Unit :=
  modify fun s => { s with sc := { s.sc with insts := s.sc.insts.push es } }
def pushComp (c : Externs × Externs) : TM Unit := modify fun s => { s with comps := s.comps.push c }

/-- Allocate the index of an item of kind `k` (types and instances are allocated by the
decoder's `decExtern`). -/
def pushKind : Kind → TM Unit
  | .func f => pushFunc f
  | .comp _ is es => pushComp (is, es)
  | _ => pure ()

/-- The placeholder name of the resource defined at type index `i`, until an export (or an
item of an inline instance) names it. -/
def defResName (i : Nat) : String := "<resource " ++ toString i ++ ">"

/-- A placeholder name of a defined resource. -/
def isDefRes (r : String) : Bool := r.startsWith "<resource "

/-- A type import of a wit-component shim component (`import-type-…`): the shim imports each
type of an exported interface under this name and exports it under the interface's own name. -/
def isShimImport (m : String) : Bool := "import-type-".isPrefixOf m

/-- The kind of a type item named `n` for the type index `i`: a resource defined in this
component (still under its placeholder name) is named `n` there and is the resource `n`, as
an exported resource of a world (`(export "n" (type (sub resource)))`). An export of a
resource under another name than its own is the resource `n` too: this is how
wit-component's shim components export the resource they import (`import-type-counter`,
instantiated with the defined resource, exported as `counter`). Likewise a record, variant,
enum or flags type the shim imports as `import-type-r` and exports as `r` is the nominal type `r`
(the same definition): the exported instance defines it, rather than referring to the shim's
import. Any other type is as `decExtern`/`typeKind` read it. -/
def typeItem (n : String) (i : Nat) (alloc : Bool) : TM Kind := do
  match ← liftD (Bridge.typeAt i) with
  | .res r =>
    if isDefRes r then do
      liftD (modify fun sc => { sc with types := sc.types.set! i (.res n) })
      if alloc then liftD (Bridge.pushTy (.res n))
      pure (.type (.resource n))
    else if alloc then
      if r ≠ n then do
        liftD (Bridge.pushTy (.res n))
        pure (.type (.resource n))
      else liftD (Bridge.decExtern n (.type (.eq i)))
    else pure (.type (Bridge.typeKind n (.res r)))
  | .val (.ref ⟨.local, m⟩) =>
    if alloc && m ≠ n && isShimImport m then do
      match ← liftD (do pure ((← get).nom.lookup m)) with
      | some d =>
        liftD (modify fun sc => { sc with nom := sc.nom ++ [(n, d)] })
        liftD (Bridge.pushTy (.val (.ref ⟨.local, n⟩)))
        pure (.type (.value (.ref ⟨.local, n⟩)))
      | none => liftD (Bridge.decExtern n (.type (.eq i)))
    else if alloc then liftD (Bridge.decExtern n (.type (.eq i)))
    else pure (.type (Bridge.typeKind n (.val (.ref ⟨.local, m⟩))))
  | t =>
    if alloc then liftD (Bridge.decExtern n (.type (.eq i)))
    else pure (.type (Bridge.typeKind n t))

/-- The kind of an item of the component, named `n`, allocating its new index (an export or an
item of an inline instance allocates nothing; `alloc` says which). -/
def itemKind (n : String) (x : SortIdx) (alloc : Bool) : TM Kind := do
  match x.sort with
  | .func => do
    let f ← funcAt x.idx
    if alloc then pushFunc f
    pure (.func f)
  | .instance => do
    let es ← instAt x.idx
    if alloc then pushInst es
    pure (.inst (Bridge.ifaceId n) es)
  | .component => do
    let (is, es) ← compAt x.idx
    if alloc then pushComp (is, es)
    pure (.comp none is es)
  | .type => typeItem n x.idx alloc
  | _ => throw s!"`{n}`: item of an unsupported sort"

/-- One alias. -/
def alias_ (a : Alias) : TM Unit := do
  match a.sort, a.target with
  | .core _, _ => pure ()
  | .func, .export i n => do
    match (← instAt i).lookup n with
    | some (.func f) => pushFunc f
    | _ => throw s!"alias of `{n}`: not a function export"
  | .component, .export i n => do
    match (← instAt i).lookup n with
    | some (.comp _ is es) => pushComp (is, es)
    | _ => throw s!"alias of `{n}`: not a component export"
  | .type, _ | .instance, .export .. => liftD (Bridge.decAlias a)
  | _, _ => throw "alias: unsupported sort or target"

/-- One canonical definition: only `canon lift` defines a component function. -/
def canon_ : Canon → TM Unit
  | .lift _ _ t => do
    match ← liftD (Bridge.typeAt t) with
    | .func f => pushFunc f
    | _ => throw s!"canon lift: type {t} is not a function type"
  | _ => pure ()

/-- One import. -/
def import_ (i : Import) : TM Unit := do
  let k ← liftD (Bridge.decExtern i.name.name i.desc)
  pushKind k
  modify fun s => { s with imports := s.imports ++ [(i.name.name, k)] }

/-- One export. -/
def export_ (e : Export) : TM Unit := do
  let n := e.name.name
  let k ← match e.desc with
    | some d => do
      let k ← liftD (Bridge.decExtern n d)
      pushKind k
      pure k
    | none => itemKind n e.item true
  modify fun s => { s with exports := s.exports ++ [(n, k)] }

/-- One instance expression. -/
def instance_ : InstanceExpr → TM Unit
  | .instantiate c _ => do pushInst (← compAt c).2
  | .exports es => do
    let ks ← es.mapM fun e => do pure (e.1.name, ← itemKind e.1.name e.2 false)
    pushInst ks

/-- The placeholder name of a record, variant, enum or flags type defined at index `i` and used
by index before any export names it. -/
def anonName (i : Nat) : String := "<type " ++ toString i ++ ">"

open Silmaril.Wasm.Wac.Bridge in
/-- A value type, where a not yet named record, variant, enum or flags type at an index reads as
a reference to its placeholder name (`anonName`), instead of failing. wit-component's
components define the types of an exported interface anonymously at the top level and use them
by index in the functions they lift, before passing them to the shim component that names
them (`(with "import-type-r" (type i))`); the inference reads the exported instance's types off
the shim's exports, so these placeholders do not reach the package's type. -/
def decValL : ValType → DM Ty
  | .prim p => pure (.prim p)
  | .idx i => do
    match ← typeAt i with
    | .nominal _ => pure (.ref ⟨.local, anonName i⟩)
    | _ => decVal (.idx i)

/-- An optional value type, leniently. -/
def decValOptL : Option ValType → DM (Option Ty)
  | none => pure none
  | some v => some <$> decValL v

open Silmaril.Wasm.Wac.Bridge in
/-- A defined type, leniently: `decDefType` with `decValL` for the value types of function
types, anonymous value types, records and variants (everything else keeps `decDefType`). -/
def decDefTypeL : DefType → DM TInfo
  | .func f => do
    let ps ← f.params.mapM fun p => do pure (p.1, ← decValL p.2)
    pure (.func ⟨f.async, ps, ← decValOptL f.result⟩)
  | .val (.list t) => do pure (.val (.list (← decValL t)))
  | .val (.fixedList t n) => do pure (.val (.fixedList (← decValL t) n))
  | .val (.option t) => do pure (.val (.option (← decValL t)))
  | .val (.result a b) => do let a ← decValOptL a; pure (.val (.result a (← decValOptL b)))
  | .val (.tuple ts) => do pure (.val (.tuple (← ts.mapM decValL)))
  | .val (.record fs) => do
    pure (.nominal (.record (← fs.mapM fun f => do pure (f.1, ← decValL f.2))))
  | .val (.variant cs) => do
    pure (.nominal (.variant (← cs.mapM fun c => do pure (c.1, ← decValOptL c.2))))
  | t => decDefType t

/-- A defined type: `decDefType` when it succeeds, else `decDefTypeL` from the same scope. -/
def decDefTypeT (t : DefType) : DM TInfo := fun sc =>
  match (Bridge.decDefType t).run sc with
  | .ok p => .ok p
  | .error _ => (decDefTypeL t).run sc

theorem decDefTypeT_ok {t : DefType} {sc : Bridge.DScope} {p : TInfo × Bridge.DScope}
    (h : (Bridge.decDefType t).run sc = .ok p) : (decDefTypeT t).run sc = .ok p := by
  show (match (Bridge.decDefType t).run sc with
    | .ok p => Except.ok p
    | .error _ => (decDefTypeL t).run sc) = Except.ok p
  rw [h]

/-- One type definition. -/
def type_ : DefType → TM Unit
  | .resource .. => do
    let i := (← get).sc.types.size
    liftD (Bridge.pushTy (.res (defResName i)))
  | t => do
    let ti ← liftD (decDefTypeT t)
    liftD (Bridge.pushTy ti)

/-- Run a nested component's inference. -/
def nested {α : Type} (m : TM α) : TM α := do
  let s ← get
  match m.run { sc := { outer := s.sc.types :: s.sc.outer, nom := s.sc.nom } } with
  | .ok (a, s') =>
    set { s with sc := { s.sc with nom := s'.sc.nom } }
    pure a
  | .error e => throw e

mutual
/-- The imports and exports of a component. -/
def ofAst : Ast → TM (Externs × Externs)
  | .mk ss => do
    ofSecs ss
    let s ← get
    pure (s.imports, s.exports)
/-- The sections of a component. -/
def ofSecs : List Section → TM Unit
  | [] => pure ()
  | s :: ss => do ofSec s; ofSecs ss
/-- One section. -/
def ofSec : Section → TM Unit
  | .custom .. | .coreModule _ | .coreInstances _ | .coreTypes _ => pure ()
  | .component c => do pushComp (← nested (ofAst c))
  | .instances xs => xs.forM instance_
  | .aliases xs => xs.forM alias_
  | .types xs => xs.forM type_
  | .canons xs => xs.forM canon_
  | .imports xs => xs.forM import_
  | .exports xs => xs.forM export_
  | .start _ => throw "start functions are not supported"
  | .values _ => throw "values are not supported"
end

/-- **The type of a component binary as a package**, and the nominal definitions it uses.
Type exports are the package's definitions (by name after `/`), as in `Bridge.pkgOfWorld`. -/
def typeOf (c : Ast) : Except String (PkgType × Bridge.NomTable) := do
  let ((is, es), s) ← (ofAst c).run {}
  let defs := es.filterMap fun
    | (n, .type k) => some (Bridge.defName n, .type (Bridge.unwrapDef k))
    | _ => none
  let exps := es.filter fun p => match p.2 with
    | .type _ => false
    | _ => true
  pure ({ imports := is, exports := exps, defs := defs }, s.sc.nom)

/-- **A package from its binary**: `Bridge.decodePkg` (the world, by projection) when it
applies, else `typeOf`. -/
def decodeAny (b : ByteArray) : Except String (PkgType × Bridge.NomTable) :=
  match Bridge.decodePkg b with
  | .ok r => .ok r
  | .error e => match Component.Binary.parse b with
    | .error _ => .error e
    | .ok c => match typeOf c with
      | .ok r => .ok r
      | .error e' => .error s!"{e}; by inference: {e'}"

end Silmaril.Wasm.Wac.TypeOf
