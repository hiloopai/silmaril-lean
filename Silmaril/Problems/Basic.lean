module

public import Lean
public import Silmaril.Problems.Encode
public import Silmaril.Problems.Compose

/-!
# Problems and solutions

A **problem** is a named, `Prop`-valued definition: the statement to be
proved. A **solution** is an ordinary theorem whose type is that statement.
The full format (`problem.toml`, artifacts, interfaces, tiers, trust policy,
check records and the index) is in `docs/Problems.md`; this module is its
Lean core.

```
@[expose] public section
@[problem "examples/add-comm"]
def addComm : Prop := ∀ a b : Nat, a + b = b + a

@[solves "examples/add-comm"]
theorem addComm_solution : addComm := fun a b => Nat.add_comm a b
```

* `@[problem "ID"]` registers a closed `def … : Prop` under a problem ID. An
  ID is unique in an environment.
* `@[solves "ID"]` registers a theorem as a solution of problem `ID`, and
  checks **at elaboration** that its type is definitionally equal to the
  problem's statement and that it does not use `sorryAx`. `@[refutes "ID"]`
  does the same for a theorem of type `¬ statement` (a negative control).
  Any number of solutions may live in one module, and one problem may have
  any number of solutions. Solutions are ordinary theorems: import the module
  and use them by name.
* `#problems` and `#solutions ["ID"]` list what the environment knows.
* `#problems_dump "PATH" "ROOT"…` writes the JSON that
  `scripts/problems/check.py` reads: statements, their canonical encodings
  (the encoding `sil spec` hashes) and closure encodings, each solution's
  axioms, a re-check of definitional equality, and which other solutions a
  solution's proof uses (assume–guarantee composition, `Silmaril.Problems.compose`).

The attributes record names only. What a problem *means* is its statement;
`problem.toml` adds the artifacts, semantics pins and policy, and the checker
binds the two by statement hash.
-/

public meta section

namespace Silmaril.Problems

open Lean Meta Elab Command

/-- A problem ID: one or more `/`-separated segments, each starting with a
lower-case letter or a digit and continuing with lower-case letters, digits,
`.`, `_` and `-`. The first segment is the family by convention. -/
def validId (id : String) : Bool :=
  let seg (s : String) : Bool :=
    match s.toList with
    | [] => false
    | c :: cs => (c.isLower || c.isDigit) &&
        cs.all fun c => c.isLower || c.isDigit || c == '.' || c == '_' || c == '-'
  (id.splitOn "/").all seg

/-- A registered problem. -/
structure ProblemEntry where
  /-- The problem ID. -/
  id : String
  /-- The `Prop`-valued definition stating it. -/
  decl : Name
  deriving Inhabited, Repr

/-- A registered solution (or refutation). -/
structure SolutionEntry where
  /-- The problem ID. -/
  id : String
  /-- The theorem. -/
  decl : Name
  /-- `true` for `@[refutes]`: the theorem proves the negation. -/
  refutes : Bool
  /-- The theorem's type is syntactically the problem constant (or its
  negation), rather than merely definitionally equal to it. -/
  direct : Bool
  deriving Inhabited, Repr

/-- Problems, keyed by ID. -/
initialize problemExt : SimplePersistentEnvExtension ProblemEntry (Std.HashMap String Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map entry => map.insert entry.id entry.decl
    addImportedFn := fun mods =>
      mods.foldl (fun map entries => entries.foldl (fun map e => map.insert e.id e.decl) map) {}
  }

/-- Solutions and refutations. -/
initialize solutionExt : SimplePersistentEnvExtension SolutionEntry Unit ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ _ => ()
    addImportedFn := fun _ => ()
  }

/-- Every entry of a simple extension: imported modules in order, then the
current module. -/
def allEntries {α σ : Type} [Inhabited α] [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
    (env : Environment) : Array α := Id.run do
  let mut out := #[]
  for modIdx in [0:env.header.modules.size] do
    out := out ++ ext.getModuleEntries env modIdx
  return out ++ (ext.getEntries env).reverse.toArray

/-- Every registered problem. -/
def problems (env : Environment) : Array ProblemEntry := allEntries problemExt env

/-- Every registered solution and refutation. -/
def solutions (env : Environment) : Array SolutionEntry := allEntries solutionExt env

/-- The definition stating problem `id`. -/
def problemDecl? (env : Environment) (id : String) : Option Name :=
  (problemExt.getState env)[id]?

/-- The module that declares `decl`. -/
def moduleOf (env : Environment) (decl : Name) : Name :=
  match env.getModuleIdxFor? decl with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- The statement a solution must have: the problem constant, or its negation. -/
def target (decl : Name) (refutes : Bool) : Expr :=
  if refutes then mkNot (mkConst decl) else mkConst decl

/-- Problem `id`'s statement, as a solution or refutation must state it. -/
def targetOf (env : Environment) (id : String) (refutes : Bool) : CoreM Expr := do
  let some decl := problemDecl? env id
    | throwError "unknown problem {id}: no `@[problem \"{id}\"]` definition is imported"
  return target decl refutes

/-- Check a problem definition: public, closed, universe-monomorphic, `Prop`-valued. -/
def checkProblemDecl (decl : Name) : CoreM Unit := do
  let env ← getEnv
  if isPrivateName decl then
    throwError "@[problem]: {decl} is private; a problem must be importable"
  let some info := env.find? decl
    | throwError "@[problem]: unknown declaration {decl}"
  let privateView ← withoutExporting (return (← getEnv).find? decl)
  let .defnInfo d := info
    | if privateView matches some (.defnInfo _) then
        throwError "@[problem]: the value of {decl} is not exposed to importers; state problems \
          in an `@[expose] public section` (or mark the definition `@[expose]`)"
      else
        throwError "@[problem] goes on a `def … : Prop`; {decl} is not a definition"
  unless d.levelParams.isEmpty do
    throwError "@[problem]: {decl} has universe parameters; a problem statement is a closed \
      proposition"
  let isProp ← MetaM.run' (isDefEq d.type (.sort .zero))
  unless isProp do
    throwError "@[problem]: {decl} has type{indentExpr d.type}\nbut a problem is a `Prop`"

/-- Check that `decl` is a sorry-free theorem of problem `id`'s statement (or
its negation), returning whether its type is syntactically the target. -/
def checkSolutionDecl (id : String) (decl : Name) (refutes : Bool) : CoreM Bool :=
  -- Inside a `module`, a theorem is exported without its proof; check the
  -- private view, which has it.
  withoutExporting do
  let env ← getEnv
  let attr := if refutes then "refutes" else "solves"
  let some info := env.find? decl
    | throwError "@[{attr}]: unknown declaration {decl}"
  unless info matches .thmInfo _ do
    throwError "@[{attr}] goes on a theorem; {decl} is not one"
  let goal ← targetOf env id refutes
  let direct := info.type.consumeMData == goal
  let ok ← MetaM.run' (isDefEq info.type goal)
  unless ok do
    throwError "@[{attr} \"{id}\"]: the type of {decl}{indentExpr info.type}\nis not \
      definitionally equal to the problem statement{indentExpr goal}"
  let axioms ← collectAxioms decl
  if axioms.contains ``sorryAx then
    throwError "@[{attr} \"{id}\"]: {decl} depends on `sorryAx`; a solution must be complete"
  return direct

/-- `@[problem "ID"]`: this `Prop`-valued definition states problem `ID`. -/
syntax (name := problem) "problem " str : attr

/-- `@[solves "ID"]`: this theorem solves problem `ID`; its type must be
definitionally equal to the problem's statement. -/
syntax (name := solves) "solves " str : attr

/-- `@[refutes "ID"]`: this theorem proves the negation of problem `ID`'s
statement (a negative control, or a counterexample to a proposed problem). -/
syntax (name := refutes) "refutes " str : attr

initialize registerBuiltinAttribute {
  name := `problem
  descr := "state a problem: a closed `Prop`-valued definition, registered under an ID"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[problem] must be global"
    let `(attr| problem $id:str) := stx | throwError "expected `@[problem \"ID\"]`"
    let id := id.getString
    unless validId id do
      throwError "@[problem]: {id.quote} is not a problem ID: `/`-separated segments of \
        lower-case letters, digits, `.`, `_` and `-`"
    let env ← getEnv
    if let some previous := problemDecl? env id then
      throwError "@[problem]: {id} is already stated by {previous}"
    if let some other := (problems env).find? (·.decl == decl) then
      throwError "@[problem]: {decl} already states {other.id}"
    checkProblemDecl decl
    modifyEnv (problemExt.addEntry · { id, decl })
}

/-- Shared implementation of `@[solves]` and `@[refutes]`. -/
def addSolution (refutes : Bool) (decl : Name) (id : String) : AttrM Unit := do
  let direct ← checkSolutionDecl id decl refutes
  modifyEnv (solutionExt.addEntry · { id, decl, refutes, direct })

initialize registerBuiltinAttribute {
  name := `solves
  descr := "register a theorem as a solution of a problem; checks its statement"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[solves] must be global"
    let `(attr| solves $id:str) := stx | throwError "expected `@[solves \"ID\"]`"
    addSolution false decl id.getString
}

initialize registerBuiltinAttribute {
  name := `refutes
  descr := "register a theorem as a refutation of a problem; checks its statement"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[refutes] must be global"
    let `(attr| refutes $id:str) := stx | throwError "expected `@[refutes \"ID\"]`"
    addSolution true decl id.getString
}

/-! ## Listing -/

/-- `#problems`: every problem in the environment, with its solution count. -/
elab "#problems" : command => do
  let env ← getEnv
  let sols := solutions env
  let lines := (problems env).map fun p =>
    let s := (sols.filter fun s => s.id == p.id && !s.refutes).size
    let r := (sols.filter fun s => s.id == p.id && s.refutes).size
    m!"{p.id}: {p.decl} ({moduleOf env p.decl}); {s} solution(s){if r > 0 then m!", {r} refutation(s)" else m!""}"
  if lines.isEmpty then logInfo "no problems" else
  logInfo (MessageData.joinSep lines.toList "\n")

/-- `#solutions` lists every solution; `#solutions "ID"` those of one problem. -/
elab "#solutions" id:(ppSpace str)? : command => do
  let env ← getEnv
  let filter := id.map (·.getString)
  if let some id := filter then
    if (problemDecl? env id).isNone then throwError "unknown problem {id}"
  let sols := (solutions env).filter fun s => filter.all (· == s.id)
  let lines := sols.map fun s =>
    m!"{s.id}: {if s.refutes then "refuted" else "solved"} by {s.decl} ({moduleOf env s.decl})\
      {if s.direct then m!"" else m!" [up to defeq]"}"
  if lines.isEmpty then logInfo "no solutions" else
  logInfo (MessageData.joinSep lines.toList "\n")

/-! ## The checker's dump -/

/-- Whether `n` is declared in a module whose root is one of `roots` (or in
the current module). -/
def inRoots (env : Environment) (roots : List Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.contains (env.header.moduleNames[idx.toNat]!).getRoot
  | none => true

/-- The solutions reachable from `n` through in-scope constants (proofs included),
not looking inside a solution, memoised across calls (the dump asks this for every
solution, and their dependency graphs overlap almost entirely). A constant met again
while it is being expanded (only possible through `unsafe` recursion) contributes
nothing. -/
partial def reachSolutions (env : Environment) (roots : List Name) (isSolution : Name → Bool)
    (n : Name) : StateM (Std.HashMap Name NameSet) NameSet := do
  if let some found := (← get)[n]? then return found
  modify (·.insert n {})
  let found ← match env.find? n with
    | none => pure {}
    | some info => do
      let value := match info with
        | .thmInfo t => some t.value
        | _ => info.value?
      let consts := info.type.getUsedConstants ++ (value.map (·.getUsedConstants)).getD #[]
      let mut found : NameSet := {}
      for m in consts do
        if !inRoots env roots m || m == n then continue
        if isSolution m then found := found.insert m
        else
          for k in ← reachSolutions env roots isSolution m do
            found := found.insert k
      pure found
  modify (·.insert n found)
  return found

/-- The other solutions a proof uses: the solutions reachable from `decl`'s
value through in-scope constants (proofs included), not looking inside a
solution. This is how a composite solution's components are found. -/
def usedSolutions (env : Environment) (roots : List Name)
    (isSolution : Name → Bool) (decl : Name) : Array Name :=
  ((reachSolutions env roots isSolution decl).run' {}).toArray.qsort Name.quickLt

/-- The dump record of a problem. -/
def problemJson (env : Environment) (roots : List Name) (p : ProblemEntry) : MetaM Json := do
  let some info := env.find? p.decl
    | return Json.mkObj [("id", p.id), ("declaration", toString p.decl), ("error", "missing")]
  let some value := info.value?
    | return Json.mkObj [("id", p.id), ("declaration", toString p.decl),
        ("error", "the statement's value is not visible; use `@[expose]`")]
  return Json.mkObj [
    ("id", p.id), ("declaration", toString p.decl), ("module", toString (moduleOf env p.decl)),
    ("statement", toString (← ppExpr value)),
    ("encoding", (Encode.encodeValue? info).getD ""),
    ("closure", Encode.encodeClosure env (inRoots env roots) p.decl),
    ("closureSize", (Encode.closure env (inRoots env roots) p.decl).size)]

/-- The dump record of a solution, re-checking definitional equality. -/
def solutionJson (env : Environment) (used : Name → Array Name)
    (s : SolutionEntry) : MetaM Json := do
  let some info := env.find? s.decl
    | return Json.mkObj [("problem", s.id), ("declaration", toString s.decl), ("error", "missing")]
  let defeq ← match problemDecl? env s.id with
    | some p => isDefEq info.type (target p s.refutes)
    | none => pure false
  let axioms := ((← collectAxioms s.decl).map toString).qsort (· < ·)
  return Json.mkObj [
    ("problem", s.id), ("declaration", toString s.decl),
    ("module", toString (moduleOf env s.decl)),
    ("kind", if s.refutes then "refutes" else "solves"),
    ("direct", s.direct), ("defeq", defeq),
    ("statement", toString (← ppExpr info.type)),
    ("typeEncoding", Encode.encodeStatement info),
    ("axioms", toJson axioms),
    ("usesSolutions", toJson ((used s.decl).map toString))]

/-- The whole dump. -/
def dumpJson (roots : List Name) : MetaM Json := do
  let env ← getEnv
  let sols := solutions env
  let solNames : NameSet := sols.foldl (fun set s => set.insert s.decl) {}
  let ps ← (problems env).mapM (problemJson env roots)
  -- One memo table for every solution's traversal.
  let (usedBy, _) := (sols.mapM fun s =>
      return (s.decl, (← reachSolutions env roots solNames.contains s.decl).toArray.qsort
        Name.quickLt) : StateM (Std.HashMap Name NameSet) _).run {}
  let used := fun d => ((usedBy.find? (·.1 == d)).map (·.2)).getD #[]
  let ss ← sols.mapM (solutionJson env used)
  -- An ID declared in two imported modules is only detectable here.
  let ids := (problems env).map (·.id)
  let dups := ids.filter fun id => (ids.filter (· == id)).size > 1
  return Json.mkObj [
    ("schema", "silmaril.problems-dump.v1"), ("toolchain", Lean.versionString),
    ("roots", toJson (roots.map toString)), ("problems", toJson ps),
    ("solutions", toJson ss), ("duplicateIds", toJson dups.toList.eraseDups)]

/-- `#problems_dump "PATH" "ROOT"…`: write the checker's JSON to `PATH`. The
roots (default `Silmaril`) bound the closure: constants declared in modules
under another root (`Init`, `Lean`, Mathlib, …) are named but not expanded. -/
elab "#problems_dump " path:str roots:(ppSpace str)* : command => do
  let roots := if roots.isEmpty then [`Silmaril] else roots.toList.map (·.getString.toName)
  let json ← liftTermElabM (withoutExporting (dumpJson roots))
  IO.FS.writeFile path.getString (json.pretty ++ "\n")
  logInfo m!"wrote {path.getString}"

end Silmaril.Problems
