module

public import Silmaril.Project.Registry.Defs

/-!
# Silmaril projects: relational problems (layer 1)

**Problems over arguments**. A problem is a definition
`P : α₀ → … → αₙ₋₁ → Prop`; every binder is an argument with its position and, unless Lean
made it inaccessible, its name. Arity 0 is a closed problem (and also silmaril's `@[problem]`).

* `@[predicate "N"]` on a definition, or `silmaril problem N (k := v)* := P`;
* `@[answers "N" s]` on a theorem, `s ∈ {thm, sat, uns, csa}`, checked against its shape;
* `silmaril instance N (k := v)* := G (x := t) (2 := u)…`: fix arguments of `G`; a registered
  value for a binder of its value type makes the instance `X.Satisfies (fun v => G … v …)`,
  and for a binder of type `Value V` is the argument itself; implicit binders that the given
  arguments determine (`{α}` before `(S : FnSpec α)`) are fixed to their solutions.

Values (layer 3) are named, not imported: `Silmaril.Project.Value` and `Value.Satisfies` are
used only when an instance argument is a registered value.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command
open Silmaril.Problems (validId problems solutions problemDecl? moduleOf allEntries)

/-- The arguments of a predicate type `∀ x₀ … xₙ₋₁, Prop`: `{pos, name, type}` each. -/
def predicateArgs (kind : String) (ty : Expr) : MetaM (Array Json) :=
  forallTelescopeReducing ty fun xs body => do
    unless ← isDefEq body (.sort .zero) do
      throwError "silmaril {kind}: the type{indentExpr ty}\nis not `α₀ → … → αₙ₋₁ → Prop`"
    xs.mapIdxM fun i x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [("pos", toJson i), ("name", ((binderName? d.userName).map Json.str).getD .null),
        ("type", .str (← ppOneLine d.type))]

/-- Register `decl : ∀ x⃗, Prop` as the problem `name`: a `predicate` record (with its room, if
any); at arity 0 also silmaril's `@[problem "name"]`. -/
def registerPredicate (name : String) (decl : Name) (room? : Option String := none) : CoreM Unit := do
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError "silmaril problem: {decl} has universe parameters; a problem is universe-monomorphic"
  let args ← MetaM.run' (predicateArgs "problem" info.type)
  if args.isEmpty then Attribute.add decl `problem (← `(attr| problem $(quote name):str))
  let fields := #[("decl", .str decl.toString), ("arity", toJson args.size), ("args", .arr args)] ++
    (room?.map fun r => ("room", Json.str r)).toArray
  addRecord { kind := "predicate", name, module := (← getEnv).mainModule, fields }

/-- The statement of an answer of status `s` (`thm sat uns csa`) for the problem `P`:
`∀ x⃗, P x⃗`, `∃ x⃗, P x⃗`, `∀ x⃗, ¬ P x⃗`, `∃ x⃗, ¬ P x⃗`. -/
def answerShape (s : String) (P : Expr) : MetaM Expr := do
  forallTelescopeReducing (← inferType P) fun xs _ => do
    let body := if s == "uns" || s == "csa" then mkNot (mkAppN P xs) else mkAppN P xs
    if s == "thm" || s == "uns" then mkForallFVars xs body
    else xs.foldrM (init := body) fun x b => do mkAppM ``Exists #[← mkLambdaFVars #[x] b]

/-- The witnesses of a proof that is literally a chain of `n` `Exists.intro`s, when closed. -/
def witnesses? : Nat → Expr → Option (List Expr)
  | 0, _ => some []
  | n + 1, e =>
    let e := e.consumeMData
    if e.isAppOfArity ``Exists.intro 4 then
      let w := e.getArg! 2
      if w.hasLooseBVars || w.hasFVar || w.hasMVar then none
      else (witnesses? n (e.getArg! 3)).map (w :: ·)
    else none

/-- `@[answers "N" s]` on `decl`: check its type against the shape of `s` and record the answer
(with the witnesses of a SAT or CSA proof). At arity 0 the answer is silmaril's `@[solves]`
(`thm`, `sat`) or `@[refutes]` (`uns`, `csa`). -/
def addAnswer (decl : Name) (name s : String) : CoreM Unit := withoutExporting do
  unless ["thm", "sat", "uns", "csa"].contains s do
    throwError "@[answers \"{name}\" {s}]: the status is one of thm, sat, uns, csa"
  let (P, arity) ← problemOf "answers" name
  let some (.thmInfo info) := (← getEnv).find? decl
    | throwError "@[answers] goes on a theorem; {decl} is not one"
  -- the proof failed and Lean reported it: no follow-on error
  if info.value.hasSyntheticSorry then return
  if arity == 0 then
    let stx ← if s == "thm" || s == "sat" then `(attr| solves $(quote name):str)
      else `(attr| refutes $(quote name):str)
    return ← Attribute.add decl (if s == "thm" || s == "sat" then `solves else `refutes) stx
  let expected ← MetaM.run' (answerShape s (mkConst P))
  unless ← MetaM.run' (isDefEq info.type expected) do
    throwError "@[answers \"{name}\" {s}]: {decl} has type{indentExpr info.type}\nbut the {s.toUpper} \
      answer of {name} states{indentExpr expected}"
  if (← collectAxioms decl).contains ``sorryAx then
    throwError "@[answers \"{name}\" {s}]: {decl} depends on `sorryAx`"
  let mut fields := #[("decl", Json.str decl.toString), ("status", .str s.toUpper)]
  if s == "sat" || s == "csa" then
    if let some ws := witnesses? arity info.value then
      fields := fields.push ("witness", .arr (← MetaM.run' (ws.toArray.mapM fun w => return .str (← ppOneLine w))))
  addRecord { kind := "answer", name, module := (← getEnv).mainModule, fields }

/-- `@[predicate "N"]`: this definition `P : α₀ → … → αₙ₋₁ → Prop` states problem `N` over its
arguments (at arity 0 it is also `@[problem "N"]`). -/
syntax (name := predicate) "predicate " str : attr

/-- `@[answers "N" s]`: this theorem establishes the SZS status `s` of problem `N`:
`thm` (`∀ x⃗, P x⃗`), `sat` (`∃ x⃗, P x⃗`), `uns` (`∀ x⃗, ¬ P x⃗`) or `csa` (`∃ x⃗, ¬ P x⃗`). -/
syntax (name := answers) "answers " str ppSpace ident : attr

initialize registerBuiltinAttribute {
  name := `predicate
  descr := "state a problem over arguments: a `Prop`-valued definition, registered under a name"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[predicate] must be global"
    let `(attr| predicate $n:str) := stx | throwError "expected `@[predicate \"NAME\"]`"
    registerPredicate n.getString decl
}

initialize registerBuiltinAttribute {
  name := `answers
  descr := "register a theorem as an SZS answer (thm, sat, uns, csa) of a problem; checks its shape"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[answers] must be global"
    let `(attr| answers $n:str $s:ident) := stx
      | throwError "expected `@[answers \"NAME\" thm|sat|uns|csa]`"
    addAnswer decl n.getString s.getId.toString
}


/-- The value type of layer 3 (named, so that this layer does not import it). -/
def valueName : Name := `Silmaril.Project.Value

/-- `Value.Satisfies` of layer 3. -/
def valueSatisfies : Name := `Silmaril.Project.Value.Satisfies

/-- Add the public, exposed definition `n := value` (a closed problem statement). -/
def addPredicateDef (n : Name) (value : Expr) (ref : Syntax) : TermElabM Unit := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasFVar then
    throwError "silmaril: the statement of {n} is not closed:{indentExpr value}"
  let type ← instantiateMVars (← inferType value)
  unless (collectLevelParams {} value).params.isEmpty && !value.hasLevelMVar && !type.hasLevelMVar do
    throwError "silmaril: the statement of {n} has universe parameters; give them explicitly"
  addDecl (.defnDecl (← mkDefinitionValInferringUnsafe n [] type value
    (.regular (getMaxHeight (← getEnv) value + 1)))) (forceExpose := true)
  addDeclarationRangesFromSyntax n ref

/-- Elaborate a closed term (no postponed holes). -/
def elabClosed (stx : Syntax) (expected? : Option Expr) : TermElabM Expr := do
  let e ← Term.elabTermEnsuringType stx expected?
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- `silmaril problem N (k := v)* := t`: the problem `N`. `t` is an existing definition
`α₀ → … → αₙ₋₁ → Prop` (an identifier), or a term of that type, which becomes the definition
`N`. The fields go to the problem's judgement. (`silmaril problem N in R := φ`, over a room, is
in `Silmaril.Project.Registry.Room.Defs`.) -/
syntax (name := silmarilProblemCmd) "silmaril " "problem " silmarilName
  (ppSpace silmarilField)* " := " term : command

@[command_elab silmarilProblemCmd]
def elabSilmarilProblem : CommandElab := fun stx => do
  let name := nameOf stx[2]
  let fs ← liftCoreM (elabFields "problem" stx[3].getArgs)
  let t := stx[5]
  let existing? ← if t.isIdent then
      liftCoreM (try some <$> realizeGlobalConstNoOverloadWithInfo t catch _ => pure none)
    else pure none
  let decl ← match existing? with
    | some d => pure d
    | none =>
      let decl ← fullName name
      liftTermElabM do addPredicateDef decl (← elabClosed t none) stx
      pure decl
  liftCoreM (registerPredicate name decl)
  unless fs.values.isEmpty do runRecord "judgement" name fs


/-- An instance argument: `(binder := term)` or `(position := term)`. -/
syntax silmarilArg := "(" (ident <|> num) " := " term ")"

/-- Rename binders (generated with inaccessible names, so that user terms cannot capture them). -/
partial def renameBinders (m : Std.HashMap Name Name) : Expr → Expr
  | .lam n d b bi => .lam (m.getD n n) (renameBinders m d) (renameBinders m b) bi
  | .forallE n d b bi => .forallE (m.getD n n) (renameBinders m d) (renameBinders m b) bi
  | .app f a => .app (renameBinders m f) (renameBinders m a)
  | .mdata d e => .mdata d (renameBinders m e)
  | e => e

/-- A registered value `t` given for a binder of type `d`: the value's constant `X`, and whether
`X` itself is the argument (`d` is `Value W`, so the binder is the value) rather than its parsed
contents (`d` is `W`, so the instance is `X.Satisfies (fun v => …)`). -/
def valueArg? (i : Nat) (t : Syntax) (d : Expr) : TermElabM (Option (String × Expr × Bool)) := do
  unless t.isIdent do return none
  let some r := findRecord? (← getEnv) "value" (leanToName t.getId) | return none
  let some xdecl := r.str? "decl" | throwError "silmaril instance: value {r.name} has no `decl`"
  let X := mkConst xdecl.toName
  let xty ← whnfR (← inferType X)
  let d' ← whnfR (← instantiateMVars d)
  if d'.isAppOfArity valueName 1 && (← isDefEq xty d') then return some (r.name, X, true)
  unless xty.isAppOfArity valueName 1 && (← isDefEq xty.appArg! d) do
    throwErrorAt t "silmaril instance: value {r.name} has type{indentExpr xty}\nbut argument \
      {i} has type{indentExpr d}"
  return some (r.name, X, false)

/-- The implicit binders of `G` that the given arguments determine: elaborate them against
metavariables for the unfixed implicit binders (`{α : Type}` before `(S : FnSpec α)`) and keep
the closed solutions, by position. The elaboration state is restored afterwards. -/
partial def inferImplicits (G : Name) (n : Nat) (fixed : Std.HashMap Nat Syntax) :
    TermElabM (Std.HashMap Nat Expr) := do
  let saved ← saveState
  let rec go (i : Nat) (ty : Expr) (ms : Array (Nat × Expr)) : TermElabM (Array (Nat × Expr)) := do
    if i == n then return ms
    let .forallE nm d b bi ← whnf ty | return ms
    match fixed[i]? with
    | none =>
      if bi.isImplicit || bi.isStrictImplicit then
        let m ← mkFreshExprMVar d
        go (i + 1) (b.instantiate1 m) (ms.push (i, m))
      else withLocalDecl nm bi d fun x => go (i + 1) (b.instantiate1 x) ms
    | some t =>
      match ← valueArg? i t d with
      | some (_, X, true) => go (i + 1) (b.instantiate1 X) ms
      | some (_, _, false) => withLocalDeclD nm d fun v => go (i + 1) (b.instantiate1 v) ms
      | none => go (i + 1) (b.instantiate1 (← elabClosed t d)) ms
  let out ← try
      let ms ← go 0 (← constType G) #[]
      ms.foldlM (init := {}) fun acc (i, m) => do
        let e ← instantiateMVars m
        return if e.hasMVar || e.hasFVar then acc else acc.insert i e
    catch _ => pure {}
  saved.restore
  return out

/-- The statement of an instance of `G` (of arity `n`) with the arguments `fixed` (by position),
and its `args` field. A term argument is substituted. A registered value `X : Value V` given for
a binder of type `V` makes the instance `X.Satisfies (fun v => G … v …)`; given for a binder of
type `Value V`, it is the argument itself. An unfixed implicit binder that the other arguments
determine (`inferImplicits`) is fixed to its solution. The other binders stay arguments, in
order. -/
partial def instanceValue (G : Name) (n : Nat) (fixed : Std.HashMap Nat Syntax) :
    TermElabM (Expr × Array Json) := do
  let inferred ← inferImplicits G n fixed
  let rec go (i : Nat) (ty : Expr) (applied kept : Array Expr) (wraps : Array (Expr × Expr))
      (names : Std.HashMap Name Name) (out : Array Json) : TermElabM (Expr × Array Json) := do
    if i == n then
      let mut body := mkAppN (mkConst G) applied
      for (X, v) in wraps.reverse do
        body ← mkAppM valueSatisfies #[X, ← mkLambdaFVars #[v] body]
      let e ← mkLambdaFVars kept body
      if e.hasFVar then
        throwError "silmaril instance: a remaining argument's type depends on a value argument"
      return (renameBinders names e, out)
    let ty ← whnf ty
    let .forallE nm d b bi := ty | throwError "silmaril instance: {G} has fewer than {n} arguments"
    let fresh ← mkFreshUserName nm
    let names := names.insert fresh nm
    match fixed[i]?, inferred[i]? with
    | none, some e =>
      go (i + 1) (b.instantiate1 e) (applied.push e) kept wraps names
        (out.push (Json.mkObj [("pos", toJson i), ("term", .str (← ppOneLine e))]))
    | none, none =>
      withLocalDecl fresh bi d fun x =>
        go (i + 1) (b.instantiate1 x) (applied.push x) (kept.push x) wraps names out
    | some t, _ =>
      match ← valueArg? i t d with
      | some (vname, X, true) =>
        go (i + 1) (b.instantiate1 X) (applied.push X) kept wraps names
          (out.push (Json.mkObj [("pos", toJson i), ("value", .str vname)]))
      | some (vname, X, false) =>
        withLocalDeclD fresh d fun v =>
          go (i + 1) (b.instantiate1 v) (applied.push v) kept (wraps.push (X, v)) names
            (out.push (Json.mkObj [("pos", toJson i), ("value", .str vname)]))
      | none =>
        let e ← elabClosed t d
        if e.hasFVar then throwErrorAt t "silmaril instance: argument {i} must be closed"
        go (i + 1) (b.instantiate1 e) (applied.push e) kept wraps names
          (out.push (Json.mkObj [("pos", toJson i), ("term", .str (← ppOneLine e))]))
  go 0 (← constType G) #[] #[] #[] {} #[]

/-- `silmaril instance N (k := v)* := G (x := t)…`: the problem `N` obtained from problem `G`
by fixing arguments, by binder name or by position (`(0 := t)`). It is a definition `N` (a
`predicate` record, and `@[problem]` if no argument remains) plus an `instance` record, the
edge `G → N` along which statuses transfer (THM and UNS down, SAT and CSA up). The fields go to
`N`'s judgement. -/
syntax (name := silmarilInstanceCmd) "silmaril " "instance " silmarilName (ppSpace silmarilField)*
  " := " silmarilName (ppSpace silmarilArg)* : command

/-- Declare the instance `name` of the problem `gname`, fixing the arguments `args`: each is
`(binder name or position, term, ref)`, and errors about it are reported at its `ref`. The
fields `fs` go to the instance's judgement. Shared by `silmaril instance` and `silmaril load`. -/
def declareInstance (name : String) (fs : Fields) (gname : String)
    (args : Array ((String ⊕ Nat) × Syntax × Syntax)) : CommandElabM Unit := do
  let (G, n) ← liftCoreM (problemOf "instance" gname)
  let binders : Array (Option String) ← liftTermElabM do
    forallTelescopeReducing (← constType G) fun xs _ =>
      xs.mapM fun x => return binderName? (← x.fvarId!.getDecl).userName
  let mut fixed : Std.HashMap Nat Syntax := {}
  for (k, t, ref) in args do
    let pos ← withRef ref do
      let pos ← match k with
        | .inl b => match binders.findIdx? (· == some b) with
          | some p => pure p
          | none => throwError "silmaril instance: {gname} has no argument named {b}"
        | .inr p => pure p
      unless pos < n do throwError "silmaril instance: {gname} has {n} arguments (0 … {n - 1})"
      if fixed.contains pos then throwError "silmaril instance: argument {pos} is given twice"
      pure pos
    fixed := fixed.insert pos t
  if fixed.isEmpty then throwError "silmaril instance: fix at least one argument of {gname}"
  let decl ← fullName name
  let args ← liftTermElabM do
    let (value, args) ← instanceValue G n fixed
    addPredicateDef decl value (← getRef)
    return args
  liftCoreM (registerPredicate name decl)
  runRecord "instance" name
    { values := #[("of", .str gname), ("decl", .str decl.toString), ("args", .arr args)] }
  unless fs.values.isEmpty do runRecord "judgement" name fs

@[command_elab silmarilInstanceCmd]
def elabSilmarilInstance : CommandElab := fun stx => do
  let args := stx[6].getArgs.map fun a =>
    let k := a[1]
    let key : String ⊕ Nat := if k.isIdent then .inl (leanToName k.getId) else .inr (k.isNatLit?.getD 0)
    (key, a[3], k)
  declareInstance (nameOf stx[2]) (← liftCoreM (elabFields "instance" stx[3].getArgs))
    (nameOf stx[5]) args


end Silmaril.Project
