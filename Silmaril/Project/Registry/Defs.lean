module

public import Lean
public import Silmaril.Problems.Basic

/-!
# Silmaril projects: the registry (v0.1)

The core of the registry (layer 0): one environment extension holds every project **record**
`{kind, name, module, fields}`, one generic command adds them, and a table of **kind handlers** says what Lean checks and fills for each kind:

```
silmaril <kind> [<name>] [:= <value>] (<key> := <value>)*
name  ::= ident | "string"
value ::= "string" | 123 | true | false | ident | [value, …]
```

`:= v` fills the kind's main field (`decl` by default; each handler names its own, e.g.
`format` for `format_default`, `children` for `children`, `proof` for
`decomposition`/`refutation_route`). An identifier
value is resolved as a constant only for the keys `decl`, `proof` and `rel` (and must name an
imported module for `module`); for any other key it is a literal name, so
`(children := [demo.a, demo.b])` reads naturally. A `format` field is resolved through the
family defaults and stores the exact format name. `(sid := "<64 hex>")` overrides an object's
derived sid (Rust derives the defaults).

**Kind handlers.** A record kind registers itself with `@[silmaril_kind k] def h : Handler`
in any module: `silmaril k …` then runs `h` (its main key, whether `(module := …)` is allowed,
and its check-and-fill function). A kind without a handler is stored as written, with a
required name; `sil project check` owns the list of kinds and fields (`schema/`). This module
has no handler. The layers register theirs, each in its own module, and the header
`Silmaril.Project.Defs` imports them all:

| module | layer | kinds and sugar |
|---|---|---|
| `Registry.Dag.Defs` | 0, the DAG | `judgement`, `group`, `decomposition`, `refutation_route`, `tasks`, `conjecture` |
| `Registry.Predicate.Defs` | 1, relational problems | `@[predicate]`, `@[answers]`, `problem … :=`, `instance` |
| `Registry.Artifacts.Defs` | 2, artifacts | `artifacts`, `artifact` |
| `Registry.Value.Defs` | 3, formats and values | `artifact_type`, `format`, `format_default`, `format_law`, `value`, `problem … about` |
| `Registry.Room.Defs` | 4, rooms | `room`, `problem … in R :=` |
| `Registry.Load.Defs` | records files | `load`: the records of TOML files (`silmaril.records.v0.2`) |
| `Registry.Attr.Defs` | attribute forms | `@[problem "N" (k := v)*]` (any arity, `room`), `@[conjecture]`, `@[value]` (a certificate) |

Only layer 3, and the loader that runs its sugar, import the definitions of
`Silmaril.Project.Core` (and through them Mathlib); this module and layers 0, 1, 2 and 4 import only
`Lean`, `Lake.Toml` and silmaril's problem registry.

Sugar forms (each expands to ordinary declarations and generic records):

* `silmaril load "silmaril/records.toml"`: read a records file (or every records file below a
  directory) and run each of its tables as the command of the same kind (`Registry.Load.Defs`,
  `docs/projects/silmaril-projects.md`); this is the default way to write a project's records;

* `silmaril artifacts "silmaril/artifacts.toml"`: read the package's TOML artifact registry
  (path relative to the package root) and add one `artifact` record per entry;
* `silmaril value N : fmt := src (| fmt := src)* (k := v)*`: a named value, its
  `include_bytes` declarations, the obligation `N.parses` and one `N.agrees.k` per extra
  source;
* `silmaril problem N about X (k := v)* : P [:= proof]`: the problem `X.Satisfies P`, its
  `children` edges to X's obligations and the proved route `¬ X.parses → ¬ N`; with a proof,
  the solutions `N.sol` and `N.parses_sol` (of `X.parses`, by `parses_of_satisfies`);
* `silmaril format_law F law := proof (rel := R)`;
* `silmaril tasks (module := M) (prefix := P)`: every `Task.x : Prop` of `M` as the open
  problem `P.x_in_snake_case` (an alias definition plus a judgement with `expect := "OPN"`);
* `silmaril group G (children := […])`: a group record and its `children` record.

**Problems over arguments**. A problem is a definition `P : α₀ → … → αₙ₋₁ → Prop`; every
binder (implicit and instance-implicit ones too) is an argument with its position and, unless
Lean made it inaccessible, its name. Arity 0 is a closed problem (and also silmaril's
`@[problem]`).

* `@[problem "N" (k := v)*]` on a definition (`Registry.Attr.Defs`; `@[predicate "N"]` is the
  older spelling), or `silmaril problem N (k := v)* := P` for an existing
  definition `P` or a term (which becomes the definition `N`); the fields go to `N`'s judgement;
* `@[answers "N" s]` on a theorem, with `s` one SZS status checked against its shape:
  `thm` `∀ x⃗, P x⃗`, `sat` `∃ x⃗, P x⃗` (with the witnesses, when the proof is a literal
  `⟨w₀, …, h⟩`), `uns` `∀ x⃗, ¬ P x⃗`, `csa` `∃ x⃗, ¬ P x⃗`. At arity 0 it is `@[solves]`
  (`thm`, `sat`) or `@[refutes]` (`uns`, `csa`). SAT and CSA together are *contingent*;
* `silmaril instance N (k := v)* := G (x := t) (2 := u)…`: fix arguments of `G` by binder name
  or position; a registered value given for a binder of its value type makes the instance
  `X.Satisfies (fun v => G … v …)`. The definition `N`, its `predicate` record and an
  `instance` record (the edge `G → N`: THM and UNS go down, SAT and CSA up);
* `silmaril conjecture N (k := v)* : P`: `def Task.N : Prop := P`, the problem `N` and its
  judgement `(expect := "OPN")`;
* `silmaril room R := decl` (or `(decl := …)`) over silmaril's `Room`, and
  `silmaril problem N in R := φ` for a sentence `φ : R.Sen`: the predicate
  `fun M => Silmaril.Project.Room.Problem R φ M` over the room's models, so that THM is validity,
  SAT satisfiability, UNS unsatisfiability, CSA a countermodel, and `(M := m)` is `m ⊨ φ`.

**Names**: dotted, segments `[a-z][a-z0-9_-]*` or all digits, at most 200 bytes; a
leading `.` is reserved. Problem names may also be legacy silmaril ids containing `/`.

**What Lean checks**: the name grammar, `(kind, name)` uniqueness, keys given once, sid
shape, and the kind handlers below. Cross-references are checked by `sil project check`, which
owns the list of kinds and fields (`schema.rs`).

| kind | Lean checks | Lean fills |
|---|---|---|
| `artifact_type` | `decl : ArtifactType` | |
| `artifact` (from `artifacts`) | `cid` shape, `type` registered, names, size of value sources | `registry` |
| `format` | `decl : Format T V`, an `artifact_type` with decl `T`; not a family | `input`, `value_type`, `printer` |
| `format_default` | the target is a format `<family>.…`; the family is not a format | |
| `format_law` | `proof : RoundTrip F` or `SoundFor F rel` | |
| `value` | sources resolve, sizes match, one value type | `decl`, `format`, `parses`, `agrees`, `sources` |
| `predicate` | `∀ x⃗, Prop`, no universe parameters | `decl`, `arity`, `args`, `room` |
| `answer` | the theorem has the shape of its status | `decl`, `status`, `witness` (`axioms` in the dump) |
| `instance` | arguments exist, once each; terms elaborate; values have the binder's type | `of`, `decl`, `args` |
| `room` | `decl : Silmaril.Logic.Institution.Room`, universe-monomorphic | `sen`, `mod` |
| `judgement` | the problem exists; `values` are values | |
| `decomposition` / `refutation_route` | `c₁ → … → cₙ → p` / `¬c → ¬p` between problems | `parent`, `children` / `child` |

`#silmaril [kind]` lists records; `#silmaril_dump "PATH"` writes `silmaril.project-dump.v0.1`.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- The schema string of the dump. -/
def dumpSchema : String := "silmaril.project-dump.v0.1"

/-! ## Names -/

/-- A name segment: `[a-z][a-z0-9_-]*` or all digits. -/
def validSegment (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    (c.isLower && cs.all fun c => c.isLower || c.isDigit || c == '_' || c == '-') ||
      (c.isDigit && cs.all Char.isDigit)

/-- A name: dotted segments, at most 200 bytes. A leading `.` is reserved. -/
def validName (n : String) : Bool :=
  n.utf8ByteSize ≤ 200 && (n.splitOn ".").all validSegment

/-- A legacy silmaril problem id (`zlib/1.3.1/…`), accepted for problems only. -/
def legacyId (n : String) : Bool := validId n && n.contains '/'

/-- A sub-name: `parent.label`, or `parent.(i+1)` for an index. -/
def subName (parent : String) : String ⊕ Nat → String
  | .inl l => parent ++ "." ++ l
  | .inr i => parent ++ "." ++ toString (i + 1)

/-- `parent.1 … parent.n`. -/
def subNames (parent : String) (n : Nat) : List String :=
  (List.range n).map (subName parent ∘ .inr)

/-- A sid: 64 lowercase hex digits. -/
def validSid (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The Lean name of a dotted name: one component per segment. -/
def nameToLean (n : String) : Name := (n.splitOn ".").foldl Name.mkStr .anonymous

/-- A Lean name as a dotted name (no escaping). -/
def leanToName (n : Name) : String := n.toString (escape := false)

/-- `firstLower` → `first_lower`. -/
def snakeCase (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c.isUpper then
      out := (if out.isEmpty then out else out.push '_').push c.toLower
    else out := out.push c
  return out

/-! ## Records -/

/-- One project record. `fields` are the keys other than `kind`, `name` and `module`. -/
structure Record where
  /-- The record kind (`format`, `value`, `judgement`, …). -/
  kind : String
  /-- The record name; unique per kind. -/
  name : String
  /-- The module that declares the record. -/
  module : Name
  /-- The fields, in source order. -/
  fields : Array (String × Json) := #[]
  deriving Inhabited

namespace Record

/-- A field. -/
def get? (r : Record) (key : String) : Option Json :=
  (r.fields.find? (·.1 == key)).map (·.2)

/-- A string field. -/
def str? (r : Record) (key : String) : Option String :=
  match r.get? key with | some (.str s) => some s | _ => none

/-- What identifies the record within its kind: its `decl` for an `answer` (a problem has many
answers), else its name. -/
def key (r : Record) : String :=
  if r.kind == "answer" then (r.str? "decl").getD r.name else r.name

/-- The record as a flat object: `kind`, `name`, `module`, then the fields sorted by key. An
unnamed artifact (keyed by its `cid`) has no `name`. -/
def toPairs (r : Record) : List (String × Json) :=
  let name := if r.kind == "artifact" && r.str? "cid" == some r.name then [] else [("name", .str r.name)]
  [("kind", .str r.kind)] ++ name ++ [("module", .str (toString r.module))] ++
    (r.fields.qsort (·.1 < ·.1)).toList

end Record

/-- Every record, keyed by `(kind, name)`. -/
initialize recordExt : SimplePersistentEnvExtension Record (Std.HashMap (String × String) Record) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map r => map.insert (r.kind, r.key) r
    addImportedFn := fun mods =>
      mods.foldl (fun map rs => rs.foldl (fun map r => map.insert (r.kind, r.key) r) map) {}
  }

/-- Every record: imported modules in order, then the current module. -/
def records (env : Environment) : Array Record := allEntries recordExt env

/-- The record `(kind, name)` (for an `answer`, `(kind, decl)`), if declared. -/
def findRecord? (env : Environment) (kind name : String) : Option Record :=
  (recordExt.getState env)[(kind, name)]?

/-- Kinds whose name defaults to the full name of their proof. -/
def proofNameKinds : List String := ["format_law", "decomposition", "refutation_route"]

/-- Kinds whose name is a problem (or group) name, so a legacy `/` id is accepted. -/
def problemNameKinds : List String :=
  ["judgement", "children", "root", "detached", "predicate", "answer", "instance"]

/-- Add a record, checking its name, its sid override and that `(kind, name)` is new. -/
def addRecord (r : Record) : CoreM Unit := do
  let env ← getEnv
  if r.name.startsWith "." then
    throwError "silmaril {r.kind}: {r.name.quote}: relative names (a leading `.`) are reserved"
  unless validName r.name || (problemNameKinds.contains r.kind && legacyId r.name) ||
      (proofNameKinds.contains r.kind && env.contains r.name.toName) do
    throwError "silmaril {r.kind}: {r.name.quote} is not a name: `.`-separated segments \
      `[a-z][a-z0-9_-]*` or all digits, at most 200 bytes"
  if let some sid := r.get? "sid" then
    unless (match sid with | .str s => validSid s | _ => false) do
      throwError "silmaril {r.kind} {r.name}: `sid` must be 64 lowercase hex digits"
  if let some prev := findRecord? env r.kind r.key then
    throwError "silmaril {r.kind} {r.key.quote} is already declared in {prev.module}"
  modifyEnv (recordExt.addEntry · r)

/-- Resolve a format reference: an exact format name, else a family default. -/
def resolveFormat (ref : String) : CoreM String := do
  let env ← getEnv
  if (findRecord? env "format" ref).isSome then return ref
  if let some d := findRecord? env "format_default" ref then
    if let some f := d.str? "format" then return f
  throwError "silmaril: no format or format family {ref.quote} is declared or imported"

/-- The `decl` of the record `(kind, name)`, which must already be declared. -/
def recordDecl (kind ofKind name : String) : CoreM Name := do
  let some r := findRecord? (← getEnv) ofKind name
    | throwError "silmaril {kind}: no `silmaril {ofKind} {name}` is declared or imported"
  let some d := r.str? "decl" | throwError "silmaril {kind}: {ofKind} {name.quote} has no `decl`"
  return d.toName

/-! ## Fields -/

/-- A field value. -/
declare_syntax_cat silmarilValue
syntax str : silmarilValue
syntax num : silmarilValue
syntax ident : silmarilValue
syntax "[" silmarilValue,* "]" : silmarilValue

/-- A name: an identifier (`demo.config`) or a string (`"some.ns.problems.5"`). -/
syntax silmarilName := ident <|> str

/-- A field `(key := value)`; `module` is accepted as a key although it is a keyword. -/
syntax silmarilField := "(" (&"module" <|> &"prefix" <|> ident) " := " silmarilValue ")"

/-- Parsed fields, plus the constant each constant-valued field resolved to. -/
structure Fields where
  /-- The fields as stored. -/
  values : Array (String × Json) := #[]
  /-- The constant-valued fields. -/
  consts : Array (String × Name) := #[]

namespace Fields

/-- A field. -/
def get? (fs : Fields) (key : String) : Option Json := (fs.values.find? (·.1 == key)).map (·.2)

/-- A required string field. -/
def str (fs : Fields) (kind key : String) : CoreM String := do
  let some (.str s) := fs.get? key | throwError "silmaril {kind}: `({key} := …)` is required"
  return s

/-- A required constant field. -/
def const (fs : Fields) (kind key : String) : CoreM Name := do
  let some (_, n) := fs.consts.find? (·.1 == key)
    | throwError "silmaril {kind}: `({key} := <constant>)` is required"
  return n

/-- Add a field; fails if present. -/
def push (fs : Fields) (kind key : String) (v : Json) (c : Option Name := none) : CoreM Fields := do
  if (fs.get? key).isSome then throwError "silmaril {kind}: `{key}` is given twice (or is filled in by Lean)"
  return { values := fs.values.push (key, v), consts := fs.consts ++ (c.map (key, ·)).toArray }

/-- Replace a field's value. -/
def set (fs : Fields) (key : String) (v : Json) : Fields :=
  { fs with values := fs.values.map fun (k, w) => if k == key then (k, v) else (k, w) }

/-- Remove a field. -/
def erase (fs : Fields) (key : String) : Fields :=
  { values := fs.values.filter (·.1 != key), consts := fs.consts.filter (·.1 != key) }

end Fields

/-- The keys whose identifier values are constants. -/
def constKeys : List String := ["decl", "proof", "rel"]

/-- The key of a field. -/
def fieldKey (k : Syntax) : String :=
  if k.isIdent then k.getId.toString else (k.getHead?.map (·.getAtomVal)).getD ""

/-- The string of a `silmarilName`. -/
def nameOf (stx : Syntax) : String :=
  if stx[0].isIdent then leanToName stx[0].getId else (stx[0].isStrLit?.getD "")

/-- Elaborate a field value. -/
partial def elabValue (key : String) (v : Syntax) : CoreM (Json × Option Name) := do
  match v with
  | `(silmarilValue| $s:str) => return (.str s.getString, none)
  | `(silmarilValue| $n:num) => return (toJson n.getNat, none)
  | `(silmarilValue| [$vs,*]) =>
    return (.arr (← vs.getElems.mapM fun v => return (← elabValue key v).1), none)
  | `(silmarilValue| $i:ident) =>
    let n := i.getId
    if n == `true then return (.bool true, none)
    if n == `false then return (.bool false, none)
    if key == "module" then
      let env ← getEnv
      unless env.header.moduleNames.contains n || n == env.mainModule do
        throwErrorAt i "silmaril: module {n} is not imported"
      return (.str n.toString, some n)
    unless constKeys.contains key do return (.str (leanToName n), none)
    let c ← realizeGlobalConstNoOverloadWithInfo i
    return (.str c.toString, some c)
  | _ => throwErrorAt v "silmaril: unexpected value"

/-- `expect` in any case: an SZS code in upper case (`thm` is `THM`), or `contingent`. -/
def normExpect (s : String) : String :=
  if s.toLower == "contingent" then "contingent" else s.toUpper

/-- Parse `(key := value)*` (reserving `kind`, `name`, and `module` unless allowed). -/
def elabFields (kind : String) (fields : Array Syntax) (init : Fields := {}) (allowModule := false) :
    CoreM Fields := do
  let mut fs := init
  for f in fields do
    let key := fieldKey f[1]
    if key == "kind" || key == "name" || (key == "module" && !allowModule) then
      throwErrorAt f "silmaril {kind}: `{key}` is reserved"
    let (v, c) ← elabValue key f[3]
    -- an SZS status may be written as an identifier: `(expect := thm)` is `"THM"`
    let v := match key, v with | "expect", .str s => .str (normExpect s) | _, v => v
    fs ← fs.push kind key v c
  return fs

/-! ## Helpers for handlers -/

/-- The declared type of a constant. -/
def constType (n : Name) : MetaM Expr := return (← getConstInfo n).type

/-- Check that `ty` is `expected` up to definitional equality. -/
def expectType (kind : String) (what : MessageData) (ty expected : Expr) : MetaM Unit := do
  unless ← isDefEq ty expected do
    throwError "silmaril {kind}: {what} has type{indentExpr ty}\nbut should have type{indentExpr expected}"

/-- Pretty-print a type or term with full names, on one line. -/
def ppOneLine (e : Expr) : MetaM String :=
  withOptions (fun o => o.setBool `pp.fullNames true) do
    return (← ppExpr e).pretty 100000

/-- The problem `name`: its declaration and arity (a `predicate` record, else an arity-0
silmaril `@[problem]`). -/
def problemOf (kind name : String) : CoreM (Name × Nat) := do
  let env ← getEnv
  if let some r := findRecord? env "predicate" name then
    if let (some d, some (.num ⟨n, 0⟩)) := (r.str? "decl", r.get? "arity") then
      return (d.toName, n.toNat)
  if let some d := problemDecl? env name then return (d, 0)
  throwError "silmaril {kind}: no problem {name.quote} is declared or imported"

/-- A binder name as recorded: `none` for one Lean made inaccessible (`_`, `[Inst α]`). -/
def binderName? (n : Name) : Option String :=
  if n.hasMacroScopes || n.isAnonymous || n.isInternal then none else some n.toString


/-! ## Kind handlers -/

/-- How `silmaril <kind> …` reads and what Lean checks and fills for one record kind. -/
structure Handler where
  /-- The field that `silmaril <kind> [name] := v` fills. -/
  mainKey : String := "decl"
  /-- Whether `(module := …)` is accepted (it is a keyword field). -/
  allowModule : Bool := false
  /-- Whether a `format` field is a reference, resolved through the family defaults. -/
  formatRef : Bool := true
  /-- Check what only Lean can check, fill fields, and return the records `(name, fields)` of
  this kind to add (sugar kinds may add other records themselves and return none). `none`
  means the default: one record, which needs a name. -/
  run? : Option (String → Option String → Fields → CommandElabM (Array (String × Fields))) := none
  deriving Inhabited

/-- The record name, which this kind requires. -/
def needName (kind : String) (name? : Option String) : CoreM String := do
  let some n := name? | throwError "silmaril {kind}: a name is required: `silmaril {kind} <name> …`"
  return n

/-- Build the attribute `@[silmaril_kind k]`. -/
unsafe def mkHandlerAttrUnsafe : IO (KeyedDeclsAttribute Handler) :=
  KeyedDeclsAttribute.init (attrDeclName := `Silmaril.Project.handlerAttr) {
    name := `silmaril_kind
    descr := "the handler of a silmaril record kind: `@[silmaril_kind k] def h : Handler`"
    valueTypeName := ``Handler
    evalKey := fun _ stx => return (← Attribute.Builtin.getIdent stx).getId.eraseMacroScopes
  }

@[implemented_by mkHandlerAttrUnsafe]
opaque mkHandlerAttr : IO (KeyedDeclsAttribute Handler)

/-- `@[silmaril_kind k]`: this `Handler` handles the record kind `k`. The last one wins. -/
initialize handlerAttr : KeyedDeclsAttribute Handler ← mkHandlerAttr

/-- The handler of a kind: the registered one, else the default. -/
def handlerOf (env : Environment) (kind : String) : Handler :=
  (handlerAttr.getValues env (.mkSimple kind)).headD {}

/-- The kinds that have a registered handler. -/
def handledKinds (env : Environment) : Array String :=
  ((handlerAttr.ext.getState env).table.toList.map (·.1.toString)).toArray.qsort (· < ·)

/-- Run a kind's handler and add its records. -/
def runRecord (kind : String) (name? : Option String) (fs : Fields) : CommandElabM Unit := do
  let h := handlerOf (← getEnv) kind
  -- a `format` field is a reference: resolve it
  let fs ← match h.formatRef, fs.get? "format" with
    | true, some (.str f) => pure (fs.set "format" (.str (← liftCoreM (resolveFormat f))))
    | _, _ => pure fs
  let out ← match h.run? with
    | some run => run kind name? fs
    | none => pure #[(← liftCoreM (needName kind name?), fs)]
  let module := (← getEnv).mainModule
  for (name, out) in out do
    liftCoreM (addRecord { kind, name, module, fields := out.values })

/-! ## Package paths and generated declarations -/

/-- The package root and the `include_bytes` prefix that reaches it from the source file.
The module's source directory is the file's directory, one level up per module component after
the first; with a Lake `srcDir`, the package root is the nearest directory at or above it with
a `lakefile.toml` or `lakefile.lean` (else the source directory itself). -/
def packageRoot : CommandElabM (System.FilePath × String) := do
  let mod := (← getEnv).mainModule
  if mod.isAnonymous then throwError "silmaril: paths need a named module (run under Lake)"
  let n := mod.components.length
  let parent (d : System.FilePath) : Option System.FilePath :=
    d.parent.map fun p => if p.toString.isEmpty then "." else p
  let mut src : System.FilePath := ← getFileName
  for _ in [0:n] do src := (parent src).getD "."
  let isRoot (d : System.FilePath) : IO Bool := do
    return (← (d / "lakefile.toml").pathExists) || (← (d / "lakefile.lean").pathExists)
  let mut dir := src
  let mut up := n - 1
  let mut found := false
  for _ in [0:32] do
    if ← isRoot dir then found := true; break
    let some p := parent dir | break
    if p == dir then break
    dir := p; up := up + 1
  unless found do dir := src; up := n - 1
  return (dir, String.join (List.replicate up "../"))

/-- Elaborate a generated definition or theorem (public, and exposed, inside a module).
`attrs` are attribute instances such as `problem "N"`. -/
def elabDef (thm : Bool) (n : Name) (attrs : Array (TSyntax ``Lean.Parser.Term.attrInstance))
    (type? : Option Term) (body : Term) : CommandElabM Unit := do
  let id := mkIdent n
  let isMod := (← getEnv).header.isModule
  let expose ← `(Lean.Parser.Term.attrInstance| expose)
  let attrs := if isMod && !thm then #[expose] ++ attrs else attrs
  let attrs? ← if attrs.isEmpty then pure none
    else some <$> `(Lean.Parser.Term.attributes| @[$attrs,*])
  let vis? ← if isMod then some <$> `(Lean.Parser.Command.visibility| public) else pure none
  let cmd ← match thm, type? with
    | true, some ty => `($[$attrs?:attributes]? $[$vis?:visibility]? theorem $id : $ty := $body)
    | false, some ty => `($[$attrs?:attributes]? $[$vis?:visibility]? def $id : $ty := $body)
    | _, none => `($[$attrs?:attributes]? $[$vis?:visibility]? def $id := $body)
  elabCommand cmd

/-- `@[problem "N"]`. -/
def problemAttr (n : String) : CommandElabM (TSyntax ``Lean.Parser.Term.attrInstance) :=
  `(Lean.Parser.Term.attrInstance| problem $(quote n):str)

/-- The full name of a declaration made from a dotted name in the current namespace. -/
def fullName (n : String) : CommandElabM Name := return (← getCurrNamespace) ++ nameToLean n

/-! ## The commands -/

/-- `silmaril <kind> [<name>] [:= <value>] (<key> := <value>)*`: declare one project record. -/
syntax (name := silmarilCmd) "silmaril " ident (ppSpace silmarilName)? (" := " silmarilValue)?
  (ppSpace silmarilField)* : command

@[command_elab silmarilCmd]
def elabSilmaril : CommandElab := fun stx => do
  let kind := stx[1].getId.toString
  let name? := stx[2].getOptional?.map nameOf
  let h := handlerOf (← getEnv) kind
  let mut fs : Fields := {}
  if stx[3].getNumArgs == 2 then
    let (j, c) ← liftCoreM (elabValue h.mainKey stx[3][1])
    fs ← liftCoreM (fs.push kind h.mainKey j c)
  fs ← liftCoreM (elabFields kind stx[4].getArgs fs h.allowModule)
  runRecord kind name? fs

/-! ## Listing and the dump -/

/-- Records in canonical order: by `(kind, name, key, module)`. -/
def sortedRecords (env : Environment) : Array Record :=
  (records env).qsort fun a b =>
    let k (r : Record) := [r.kind, r.name, r.key, toString r.module]
    decide (k a < k b)

/-- `#silmaril` lists every record, then silmaril's problems and solutions;
`#silmaril <kind>` only that kind (`problem` and `solution` included). -/
elab "#silmaril" kind:(ppSpace ident)? : command => do
  let env ← getEnv
  let filter := kind.map (·.getId.toString)
  let keep (k : String) := filter.all (· == k)
  let mut lines : Array MessageData := #[]
  for r in sortedRecords env do
    if keep r.kind then
      lines := lines.push m!"{r.kind} {r.name} ({r.module}) {(Json.mkObj r.fields.toList).compress}"
  if keep "problem" then
    for p in (problems env).qsort (·.id < ·.id) do
      lines := lines.push m!"problem {p.id} ({moduleOf env p.decl}) {p.decl}"
  if keep "solution" then
    for s in (solutions env).qsort (fun a b => a.id < b.id || (a.id == b.id && a.decl.quickLt b.decl)) do
      lines := lines.push
        m!"solution {s.id} ({moduleOf env s.decl}) {if s.refutes then "refutes" else "solves"} {s.decl}"
  if lines.isEmpty then logInfo "no records" else
  logInfo (MessageData.joinSep lines.toList "\n")

/-- A JSON object on one line, keys in the given order (`Json.mkObj` would sort them). -/
def objLine (kvs : List (String × Json)) : String :=
  "{" ++ ", ".intercalate (kvs.map fun (k, v) => (Json.str k).compress ++ ": " ++ v.compress) ++ "}"

/-- A JSON array with one element per line. -/
def linesArray (items : Array String) : String :=
  if items.isEmpty then "[]" else "[\n    " ++ ",\n    ".intercalate items.toList ++ "\n  ]"

/-- The dump `silmaril.project-dump.v0.1`: every record, problem and solution in the
environment, in canonical order, with no timestamps or host paths; one per line. -/
def dumpText : MetaM String := do
  let env ← getEnv
  let modules := ((env.imports.map (·.module)).filter (· != `Init)).map toString
  let ps := (problems env).qsort (·.id < ·.id) |>.map fun p =>
    objLine [("name", .str p.id), ("decl", .str (toString p.decl)),
      ("module", .str (toString (moduleOf env p.decl)))]
  let ss := (solutions env).qsort fun a b =>
    a.id < b.id || (a.id == b.id && toString a.decl < toString b.decl)
  let ss ← ss.mapM fun s => do
    let axioms := ((← collectAxioms s.decl).map toString).qsort (· < ·)
    return objLine [("problem", .str s.id), ("decl", .str (toString s.decl)),
      ("module", .str (toString (moduleOf env s.decl))),
      ("kind", .str (if s.refutes then "refutes" else "solves")), ("axioms", toJson axioms)]
  -- an answer record carries the axioms of its proof
  let recs ← (sortedRecords env).mapM fun r => do
    if r.kind != "answer" then return objLine r.toPairs
    let some d := r.str? "decl" | return objLine r.toPairs
    let axioms := ((← collectAxioms d.toName).map toString).qsort (· < ·)
    return objLine { r with fields := r.fields.push ("axioms", toJson axioms) }.toPairs
  let top : List (String × String) := [
    ("schema", (Json.str dumpSchema).compress), ("toolchain", (Json.str Lean.versionString).compress),
    ("modules", (toJson (modules.qsort (· < ·))).compress),
    ("records", linesArray recs),
    ("problems", linesArray ps), ("solutions", linesArray ss)]
  return "{\n" ++ ",\n".intercalate (top.map fun (k, v) => "  " ++ (Json.str k).compress ++ ": " ++ v)
    ++ "\n}\n"

/-- `#silmaril_dump "PATH"`: write the dump to `PATH`. -/
elab "#silmaril_dump " path:str : command => do
  let text ← liftTermElabM (withoutExporting dumpText)
  IO.FS.writeFile path.getString text
  logInfo m!"wrote {path.getString}"

end Silmaril.Project
