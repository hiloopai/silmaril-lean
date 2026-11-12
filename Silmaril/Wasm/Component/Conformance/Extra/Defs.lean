module

public import Silmaril.Wasm.Component.Conformance.Valid.Defs

/-!
# Validation rules the copied reference validator does not have

The copied validator (`Reference.check?`, silmaril's transcription at component-model
`a25fc0b`) lists in its headers the rules it leaves out; the conformance scripts at `d095e2f`
test some of them (`tests/component-wast/triage.tsv`, class `ref-unmodelled`). This module
adds the ones that need no change of the copied validator, as an extra check run after it on
the same reference syntax (`validateFull`):

* **names** (`validation/extern-names.wast`): an interface name's version is a SemVer 2.0.0
  version (`major.minor.patch`, numeric identifiers without leading zeros, `-` pre-release and
  `+` build identifiers non-empty over `[0-9A-Za-z-]`, numeric pre-release identifiers
  without leading zeros), as wasmparser parses it with the `semver` crate; nested namespaces
  and projections (🪺) are rejected unless `nested`;
* **attributes** (`validation/attributes.wast`, `binary/binary.wast` line 1497): at most one
  attribute of each kind (`Binary.md`: a validation rule; wasmparser rejects it while
  decoding); an `implements` value is an interface name; `implements` only on an item of
  sort instance, and only with a plain name;
* **core modules** (`validation/core-modules.wast`): no two imports of a core module or core
  module type with the same `(module, name)` pair (wasmparser: they mangle to the same
  single-level name);
* **annotated names** (`validation/annotated-names.wast`): in each import or export namespace
  (a component's or a component type's imports, the exports of a component, of a component or
  instance type, of an instance built from exports), `[constructor]R` names a function whose
  one result is `own<T>` or `result<own<T>, …>`, `[method]R.m` a function whose first
  parameter is `self: borrow<T>`, and `[static]R.m` a function, where in the first two `T` is
  the resource that this namespace names `R`, and in the third some resource of the namespace
  is named `R`. Resource identities are followed through the index space of types
  (`Scope`): an imported `(sub resource)` and a defined resource are new, `(eq i)`, an export
  without ascription and a repeated alias of the same instance export are the same, an alias
  and an export ascribed `(sub resource)` are new. A rule whose function type or resource the
  scope cannot follow (an aliased function, a type outside the scope) is not checked.

Not modelled here (they need the copied validator's type contexts, i.e. a change under
`Silmaril/Raw`): the visibility of types inside an exported instance
(`validation/external-visibility.wast` line 459) and the fresh resource introduced by an
export ascribed `(sub resource)` for type equality (`validation/resources.wast` line 578);
the rule that a resource in a bag-of-exports instance's function has a name of that instance
(`annotated-names.wast` line 177), whose wasmparser semantics this module does not follow.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance.Extra

open Silmaril.Wasm.Component

/-! ## SemVer 2.0.0 -/

/-- A numeric identifier: digits, no leading zero. -/
def numId (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all Char.isDigit && (cs.length == 1 || cs.head? != some '0')

/-- An alphanumeric identifier: non-empty, over `[0-9A-Za-z-]`. -/
def alnumId (cs : List Char) : Bool := !cs.isEmpty && cs.all fun c => c.isAlphanum || c == '-'

/-- A pre-release identifier: alphanumeric, and numeric ones without a leading zero. -/
def preId (cs : List Char) : Bool := alnumId cs && (!cs.all Char.isDigit || numId cs)

/-- 🔗 `canonversion`: `[1-9][0-9]*`, `0.[1-9][0-9]*` or `0.0.[1-9][0-9]*`. -/
def canonVersion (cs : List Char) : Bool :=
  let pos (d : List Char) := numId d && d != ['0']
  match Syntax.splitAll '.' cs with
  | [a] => pos a
  | [z, a] => z == ['0'] && pos a
  | [z, z', a] => z == ['0'] && z' == ['0'] && pos a
  | _ => false

/-- `cs` is a SemVer 2.0.0 version. -/
def semver (cs : List Char) : Bool :=
  let core := cs.takeWhile fun c => c != '-' && c != '+'
  let coreOk := match Syntax.splitAll '.' core with
    | [a, b, c] => numId a && numId b && numId c
    | _ => false
  let (pre, build) : Option (List Char) × Option (List Char) :=
    match cs.drop core.length with
    | '-' :: r =>
      let p := r.takeWhile (· != '+')
      (some p, match r.drop p.length with
        | '+' :: b => some b
        | _ => none)
    | '+' :: b => (none, some b)
    | _ => (none, none)
  coreOk && pre.all (fun p => (Syntax.splitAll '.' p).all preId) &&
    build.all fun b => (Syntax.splitAll '.' b).all alnumId

example : semver "1.0.0".toList && semver "123456.7890.488".toList && semver "0.0.0+abcd".toList &&
    semver "0.0.0+abcd-efg".toList && semver "0.0.0-abcd+efg".toList &&
    semver "0.0.0-abcd.1.2+efg.4.ee.5".toList := by decide

example : ["", ".", "1.", "a.2", "2.b", "2.0x0", "2.0.0+", "2.0.0-", "01.0.0", "1.0.0-01"].all
    (fun s => !semver s.toList) := by decide

/-! ## Names and attributes -/

/-- The sort an extern descriptor names. -/
def descSort : Syntax.ExternDesc → Syntax.Sort_
  | .coreModule _ => .core .module_
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance_ _ => .instance_

/-- What is wrong with an interface name, if anything (`canon`: 🔗 canonical versions
admitted). -/
def interfaceProblem (nested canon : Bool) (s : String) : Option String :=
  match Syntax.externNameKind s with
  | .interface i =>
    if i.nested && !nested then
      some s!"`{s}`: nested namespaces and projections (🪺) are not enabled"
    else match i.version with
      | some v =>
        if semver v.toList || (canon && canonVersion v.toList) then none
        else some s!"`{s}`: `{v}` is not a SemVer version"
      | none => none
  | _ => none

/-- What is wrong with an extern name and its attributes, given the sort of the item it names
(`none`: not known). -/
def nameProblem (nested : Bool) (n : Syntax.ExternName) (sort : Option Syntax.Sort_) :
    Option String :=
  let count (p : Syntax.Attribute → Bool) := (n.attrs.filter p).length
  if count (· matches .implements _) > 1 then some s!"`{n.name}`: duplicate `implements` attribute"
  else if count (· matches .externalId _) > 1 then
    some s!"`{n.name}`: duplicate `external-id` attribute"
  else if count (· matches .versionSuffix _) > 1 then
    some s!"`{n.name}`: duplicate `version-suffix` attribute"
  else match interfaceProblem nested true n.name with
  | some e => some e
  | none =>
    match n.attrs.findSome? (fun | .implements i => some i | _ => none) with
    | none => none
    | some i =>
      if sort != some .instance_ then some s!"`{n.name}`: only instances can have an `implements`"
      else match Syntax.externNameKind n.name with
        | .plain _ =>
          match Syntax.externNameKind i with
          | .interface _ => none
          | .plain _ => some s!"`implements` value `{i}` must be an interface name"
          | .invalid => some s!"`implements` value `{i}` is not a valid name"
        | _ => some s!"name `{n.name}` is not valid with `implements`"

/-! ## Core modules -/

/-- The first repeated element of a list. -/
def firstDup? {α : Type} [BEq α] : List α → Option α
  | [] => none
  | a :: as => if as.contains a then some a else firstDup? as

def dupImportProblem (pairs : List (String × String)) : Option String :=
  (firstDup? pairs).map fun (m, n) => s!"duplicate import name `{m}:{n}`"

def coreTypeProblem : Syntax.CoreTypeDef → Option String
  | .module_ decls => dupImportProblem (decls.filterMap fun
      | .import_ m n _ => some (m, n)
      | _ => none)
  | .rec_ _ => none

/-! ## Annotated names -/

/-- An entry of the index space of types. -/
inductive TE where
  /-- A resource type with an identity. -/
  | res (id : Nat)
  /-- A defined type. -/
  | defn (t : Syntax.DefType)
  /-- Not followed. -/
  | other

/-- One scope: a component, or a component or instance type. -/
structure Scope where
  types : Array TE := #[]
  /-- The type index of each function (`none`: not followed). -/
  funcs : Array (Option Nat) := #[]
  /-- Resource names of the import and export namespaces (first one wins). -/
  importNames : List (Nat × String) := []
  exportNames : List (Nat × String) := []

/-- The state of the walk: fresh resource identities, and aliases already seen. -/
structure St where
  next : Nat := 0
  aliases : List ((Nat × String) × Nat) := []

def fresh : StateM St Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- The identity of the alias of export `n` of instance `i` (the same for a repeat). -/
def aliasId (i : Nat) (n : String) : StateM St Nat := do
  match (← get).aliases.lookup (i, n) with
  | some r => pure r
  | none =>
    let r ← fresh
    modify fun s => { s with aliases := ((i, n), r) :: s.aliases }
    pure r

def Scope.type? (sc : Scope) (i : Nat) : TE := sc.types.getD i .other

/-- The resource a type index denotes, if followed. -/
def Scope.resOf? (sc : Scope) (i : Nat) : Option Nat :=
  match sc.type? i with
  | .res r => some r
  | _ => none

/-- `own<T>` (or `borrow<T>` when `borrow`) at value type `t`: the resource `T`. -/
def Scope.handleOf? (sc : Scope) (borrow : Bool) : Syntax.VT → Option (Option Nat)
  | .idx i => match sc.type? i with
    | .defn (.val (.own k)) => if borrow then none else some (sc.resOf? k)
    | .defn (.val (.borrow k)) => if borrow then some (sc.resOf? k) else none
    | _ => none
  | .prim _ => none

/-- The function type of type index `i`, if followed. -/
def Scope.funcType? (sc : Scope) (i : Nat) : Option Syntax.FuncType :=
  match sc.type? i with
  | .defn (.func ft) => some ft
  | _ => none

/-- `[constructor]R` results: `own<T>`, or `result<own<T>, E?>`. -/
def Scope.ctorRes? (sc : Scope) (t : Syntax.VT) : Option (Option Nat) :=
  match sc.handleOf? false t with
  | some r => some r
  | none => match t with
    | .idx i => match sc.type? i with
      | .defn (.val (.result (some ok) _)) => sc.handleOf? false ok
      | _ => none
    | .prim _ => none

/-- Check resource `r?` (`none`: not followed) against name `R` in namespace `names`. -/
def resourceName (names : List (Nat × String)) (rname : String) (r? : Option Nat) :
    Option String :=
  match r? with
  | none => none
  | some r => match names.lookup r with
    | none => some "resource used in function does not have a name in this context"
    | some n => if n == rname then none else
      some s!"function does not match expected resource name `{n}`"

/-- The annotated-name rules for name `n` of an item of sort `sort` and function type index
`fty?`, in namespace `names`. -/
def annotProblem (sc : Scope) (names : List (Nat × String)) (n : String) (sort : Syntax.Sort_)
    (fty? : Option Nat) : Option String :=
  let need := fun (k : Syntax.FuncType → Option String) =>
    if sort != .func then some s!"`{n}` is not a func" else
    match fty?.bind sc.funcType? with
    | some ft => k ft
    | none => none
  match Syntax.externNameKind n with
  | .plain (.constructor r) => need fun ft =>
    match ft.result with
    | none => some s!"`{n}`: function should return one value"
    | some t => match sc.ctorRes? t with
      | none => some s!"`{n}`: function should return `(own $T)` or `(result (own $T))`"
      | some r? => resourceName names r r?
  | .plain (.method none r _) => need fun ft =>
    match ft.params with
    | [] => some s!"`{n}`: function should have at least one argument"
    | (p, t) :: _ =>
      if p != "self" then some s!"`{n}`: function should have a first argument called `self`"
      else match sc.handleOf? true t with
        | none => some s!"`{n}`: function should take a first argument of `(borrow $T)`"
        | some r? => resourceName names r r?
  | .plain (.static none r _) => need fun _ =>
    if names.any (·.2 == r) then none
    else some s!"`{n}`: static resource name is not known in this context"
  | _ => none

/-! ## The walk -/

/-- A problem found so far, or the scope. -/
abbrev W := ExceptT String (StateM St)

def check (o : Option String) : W Unit :=
  match o with
  | some e => throw e
  | none => pure ()

/-- The type entry a type bound introduces under name `n`. -/
def boundEntry (sc : Scope) : Syntax.TypeBound → W TE
  | .subResource => do pure (.res (← fresh))
  | .eq i => pure (sc.type? i)

/-- Name the resource of entry `e` as `n` in a namespace. -/
def nameRes (names : List (Nat × String)) (n : String) : TE → List (Nat × String)
  | .res r => names ++ [(r, n)]
  | _ => names

/-- An import (`imp`) or export of a declarator or definition with descriptor `d`. -/
def externDecl (nested : Bool) (imp : Bool) (sc : Scope) (n : Syntax.ExternName)
    (d : Syntax.ExternDesc) : W Scope := do
  check (nameProblem nested n (some (descSort d)))
  let names := if imp then sc.importNames else sc.exportNames
  let fty? := match d with
    | .func i => some i
    | _ => none
  check (annotProblem sc names n.name (descSort d) fty?)
  match d with
  | .type b =>
    let e ← boundEntry sc b
    let sc := { sc with types := sc.types.push e }
    pure (if imp then { sc with importNames := nameRes sc.importNames n.name e }
      else { sc with exportNames := nameRes sc.exportNames n.name e })
  | .func i => pure { sc with funcs := sc.funcs.push (some i) }
  | _ => pure sc

/-- An alias: new identities for types, unfollowed functions. -/
def aliasDef (sc : Scope) : Syntax.Alias → W Scope
  | .export_ i name .type => do pure { sc with types := sc.types.push (.res (← aliasId i name)) }
  | .outer _ _ .type => do pure { sc with types := sc.types.push (.res (← fresh)) }
  | .export_ _ _ .func | .outer _ _ .func => pure { sc with funcs := sc.funcs.push none }
  | _ => pure sc

mutual

/-- A type definition: its declarators are scopes of their own. -/
def defType (nested : Bool) (sc : Scope) (t : Syntax.DefType) : W Scope := do
  match t with
  | .component ds => let _ ← componentDecls nested {} ds
  | .instance_ ds => let _ ← instanceDecls nested {} ds
  | _ => pure ()
  match t with
  | .resource _ _ => pure { sc with types := sc.types.push (.res (← fresh)) }
  | t => pure { sc with types := sc.types.push (.defn t) }

def instanceDecl (nested : Bool) (sc : Scope) : Syntax.InstanceDecl → W Scope
  | .coreType t => do check (coreTypeProblem t); pure sc
  | .type t => defType nested sc t
  | .alias a => aliasDef sc a
  | .export_ n d => externDecl nested false sc n d

def instanceDecls (nested : Bool) (sc : Scope) : List Syntax.InstanceDecl → W Scope
  | [] => pure sc
  | d :: ds => do instanceDecls nested (← instanceDecl nested sc d) ds

def componentDecls (nested : Bool) (sc : Scope) : List Syntax.ComponentDecl → W Scope
  | [] => pure sc
  | .import_ n d :: ds => do componentDecls nested (← externDecl nested true sc n d) ds
  | .decl d :: ds => do componentDecls nested (← instanceDecl nested sc d) ds

end

/-- The type of item `si` as an export ascription would see it. -/
def itemEntry (sc : Scope) (si : Syntax.SortIdx Syntax.Sort_) : TE :=
  if si.sort == .type then sc.type? si.idx else .other

mutual

/-- One definition of a component. -/
def definition (nested : Bool) (sc : Scope) :
    Syntax.Definition Silmaril.Wasm.Module → W Scope
  | .coreModule m => do
    check (dupImportProblem (m.imports.map fun i => (i.moduleName, i.name)))
    pure sc
  | .coreType t => do check (coreTypeProblem t); pure sc
  | .component defs => do let _ ← definitions nested {} defs; pure sc
  | .instance_ (.exports items) => do
    -- a bag of exports: a namespace of its own
    let mut names : List (Nat × String) := []
    for (n, si) in items do
      check (nameProblem nested n (some si.sort))
      let fty? := if si.sort == .func then (sc.funcs.getD si.idx none) else none
      check (annotProblem sc names n.name si.sort fty?)
      names := nameRes names n.name (itemEntry sc si)
    pure sc
  | .alias a => aliasDef sc a
  | .type t => defType nested sc t
  | .canon (.lift _ _ t) => pure { sc with funcs := sc.funcs.push (some t) }
  | .import_ n d => externDecl nested true sc n d
  | .export_ n si asc => do
    check (nameProblem nested n (some si.sort))
    let fty? : Option Nat := match asc with
      | some (.func i) => some i
      | _ => if si.sort == .func then sc.funcs.getD si.idx none else none
    check (annotProblem sc sc.exportNames n.name si.sort fty?)
    match si.sort with
    | .type =>
      let e ← match asc with
        | some (.type b) => boundEntry sc b
        | _ => pure (sc.type? si.idx)
      pure { sc with types := sc.types.push e, exportNames := nameRes sc.exportNames n.name e }
    | .func => pure { sc with funcs := sc.funcs.push fty? }
    | _ => pure sc
  | _ => pure sc

def definitions (nested : Bool) (sc : Scope) :
    List (Syntax.Definition Silmaril.Wasm.Module) → W Scope
  | [] => pure sc
  | d :: ds => do definitions nested (← definition nested sc d) ds

end

/-- **The extra rules** on a component (`nested`: 🪺 enabled): the first problem, if any. -/
def extraProblem (nested : Bool) (c : RefComponent) : Option String :=
  match ((definitions nested {} c).run).run {} with
  | (.error e, _) => some e
  | (.ok _, _) => none

/-- The copied validator, then the extra rules, at the runner's `features`. -/
def validateFull (c : RefComponent) : Except String Reference.ComponentType := do
  let t ← validate c
  match extraProblem features.nestedNames c with
  | some e => .error s!"extra rule: {e}"
  | none => pure t

end Silmaril.Wasm.Component.Conformance.Extra
