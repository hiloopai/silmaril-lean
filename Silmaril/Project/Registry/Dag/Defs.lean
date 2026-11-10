module

public import Silmaril.Project.Registry.Defs

/-!
# Silmaril projects: the DAG kinds (layer 0)

The handlers of the kinds every project uses:

* `judgement N (k := v)*`: metadata of an existing problem (its `values` must be registered);
* `decomposition := proof` (`c₁ → … → cₙ → p`) and `refutation_route := proof` (`¬c → ¬p`)
  between registered problems, or `(module := M)` for every such theorem of `M`;
* `group G (children := […])`: a group record and its `children` record;
* `tasks (module := M) (prefix := P)`: every `Task.x : Prop` of `M` as the open problem
  `P.x_in_snake_case`;
* `conjecture N (k := v)* : P`: the frozen open goal `def Task.N : Prop := P` as the problem `N`;
* the retired kind `task` (renamed `group` in v0.1).

`children`, `root` and `detached` need no handler.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- The problem a proposition states, up to `¬` and unfolding non-problem definitions:
`(name, number of negations)`. -/
partial def asProblem? (ids : Std.HashMap Name String) (fuel : Nat) (e : Expr) :
    MetaM (Option (String × Nat)) := do
  let e := e.consumeMData
  if let .const c _ := e then
    if let some id := ids[c]? then return some (id, 0)
  let neg (a : Expr) := return (← asProblem? ids fuel a).map fun (id, n) => (id, n + 1)
  if e.isAppOfArity ``Not 1 then return ← neg e.appArg!
  if let .forallE _ a b _ := e then
    if !b.hasLooseBVars && b.consumeMData.isConstOf ``False then return ← neg a
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => asProblem? ids fuel e'
    | none => return none

/-- The edge shape of a theorem type: `.inl (children, parent)` for `c₁ → … → cₙ → p`,
`.inr (child, parent)` for `¬c → ¬p`. -/
def edgeShape? (ids : Std.HashMap Name String) (ty : Expr) :
    MetaM (Option (Array String × String ⊕ String × String)) :=
  forallTelescope ty fun hs concl => do
    let some (p, pn) ← asProblem? ids 8 concl | return none
    let mut cs := #[]
    for h in hs do
      let some c ← asProblem? ids 8 (← inferType h) | return none
      cs := cs.push c
    if pn == 0 && !cs.isEmpty && cs.all (·.2 == 0) then return some (.inl (cs.map (·.1), p))
    if pn == 1 && cs.size == 1 && cs[0]!.2 == 1 then return some (.inr (cs[0]!.1, p))
    return none

/-- The record of an edge kind (`decomposition`, `refutation_route`) from one proof. -/
def edgeRecord? (kind : String) (ids : Std.HashMap Name String) (proof : Name) (fs : Fields) :
    MetaM (Option Fields) := do
  let some info := (← getEnv).find? proof | return none
  unless info matches .thmInfo _ do return none
  match kind, ← edgeShape? ids info.type with
  | "decomposition", some (.inl (cs, p)) =>
    let fs ← fs.push kind "parent" (.str p)
    some <$> fs.push kind "children" (.arr (cs.map Json.str))
  | "refutation_route", some (.inr (c, p)) =>
    let fs ← fs.push kind "parent" (.str p)
    some <$> fs.push kind "child" (.str c)
  | _, _ => return none

/-- The shape an edge kind requires, for messages. -/
def edgeShapeDoc (kind : String) : String :=
  if kind == "decomposition" then "c₁ → … → cₙ → p" else "¬c → ¬p"

/-- `judgement`: the problem exists and its `values` are registered values. -/
@[silmaril_kind judgement] def judgementHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    discard <| liftCoreM (problemOf kind name)
    if let some (.arr vs) := fs.get? "values" then
      let env ← getEnv
      for v in vs do
        let ok := match v with | .str s => (findRecord? env "value" s).isSome | _ => false
        unless ok do
          throwError "silmaril judgement: {v.compress} is not a registered value"
    return #[(name, fs)]

/-- An edge kind proved by a theorem: `:= proof`, or `(module := M)` for every theorem of the
right shape in `M`. -/
def edgeRun (kind : String) (name? : Option String) (fs : Fields) :
    CommandElabM (Array (String × Fields)) := liftTermElabM do
    let env ← getEnv
    let ids := (problems env).foldl (fun m p => m.insert p.decl p.id) {}
    match fs.consts.find? (·.1 == "proof"), fs.consts.find? (·.1 == "module") with
    | some (_, proof), none =>
      let some fs ← edgeRecord? kind ids proof fs
        | throwError "silmaril {kind}: {proof} is not a theorem of shape `{edgeShapeDoc kind}` \
            between registered problems"
      return #[(name?.getD proof.toString, fs)]
    | none, some (_, m) =>
      if name?.isSome then throwError "silmaril {kind}: a name cannot be given with `module :=`"
      let some idx := env.getModuleIdx? m | throwError "silmaril {kind}: module {m} is not imported"
      let names := env.header.moduleData[idx.toNat]!.constNames.qsort (toString · < toString ·)
      let base := fs.erase "module"
      let mut out := #[]
      for n in names do
        if let some fs ← edgeRecord? kind ids n { base with
            values := base.values.push ("proof", .str n.toString)
            consts := base.consts.push ("proof", n) } then
          out := out.push (n.toString, fs)
      if out.isEmpty then
        throwError "silmaril {kind}: {m} has no theorem of shape `{edgeShapeDoc kind}`"
      return out
    | _, _ => throwError "silmaril {kind}: give exactly one of `:= proof` and `(module := …)`"

/-- `decomposition := proof`, `proof : c₁ → … → cₙ → p`. -/
@[silmaril_kind decomposition] def decompositionHandler : Handler :=
  { mainKey := "proof", allowModule := true, run? := some edgeRun }

/-- `refutation_route := proof`, `proof : ¬c → ¬p`. -/
@[silmaril_kind refutation_route] def refutationRouteHandler : Handler :=
  { mainKey := "proof", allowModule := true, run? := some edgeRun }

/-- `children := […]`: declared, unproved sub edges. -/
@[silmaril_kind children] def childrenHandler : Handler := { mainKey := "children" }

/-- `group G (children := […])`: the group record, then its `children` record. -/
@[silmaril_kind group] def groupHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let module := (← getEnv).mainModule
    let fields := (fs.erase "children").values
    liftCoreM (addRecord { kind, name, module, fields })
    if let some cs := fs.get? "children" then
      runRecord "children" name? { values := #[("children", cs)] }
    return #[]

/-- The kind `task` is renamed `group`. -/
@[silmaril_kind task] def taskHandler : Handler where
  run? := some fun _ _ _ => throwError "silmaril task: the kind `task` is renamed `group` (v0.1)"

/-- Register every `….Task.x : Prop` of a module as the problem `prefix.x_in_snake_case`. -/
def importTasks (fs : Fields) : CommandElabM Unit := do
  let m ← liftCoreM (fs.const "tasks" "module")
  let pre ← liftCoreM (fs.str "tasks" "prefix")
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "silmaril tasks: module {m} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames.qsort (toString · < toString ·)
  let rest := (fs.erase "module").erase "prefix"
  let mut count := 0
  for c in names do
    let .str (.str _ "Task") x := c | continue
    let some (.defnInfo d) := env.find? c | continue
    unless ← liftTermElabM (isDefEq d.type (.sort .zero)) do continue
    let name := pre ++ "." ++ snakeCase x
    elabDef false (nameToLean name) #[← problemAttr name] (some (← `(Prop))) (mkCIdent c)
    runRecord "judgement" name (← liftCoreM (rest.push "tasks" "expect" (.str "OPN")))
    count := count + 1
  if count == 0 then throwError "silmaril tasks: {m} has no `Task.x : Prop` definition"


/-- `tasks (module := M) (prefix := P)`. -/
@[silmaril_kind tasks] def tasksHandler : Handler where
  allowModule := true
  run? := some fun _ _ fs => do importTasks fs; return #[]

/-- `silmaril conjecture N (k := v)* : P`: the frozen open goal `def Task.N : Prop := P` (in the
current namespace, so that `Task.*` tooling finds it), registered as the problem `N` with a
judgement `(expect := "OPN")` and the given fields. -/
syntax (name := silmarilConjectureCmd) "silmaril " &"conjecture" ppSpace silmarilName
  (ppSpace silmarilField)* " : " term : command

@[command_elab silmarilConjectureCmd]
def elabSilmarilConjecture : CommandElab := fun stx => do
  let name := nameOf stx[2]
  let fs ← liftCoreM (elabFields "conjecture" stx[3].getArgs)
  elabDef false (`Task ++ nameToLean name) #[← problemAttr name] (some (← `(Prop))) ⟨stx[5]⟩
  runRecord "judgement" name (← liftCoreM (fs.push "conjecture" "expect" (.str "OPN")))

end Silmaril.Project
