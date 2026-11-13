module

public import Silmaril.Prelude.Trust.Defs
public meta import Lean.Meta.Native

/-! # Trust commands and the `edge_decide` tactic

```
/-- Same bytes, by windows. Trusts the compiled `KBytes.read` (GMP shifts). -/
native_decider bytes.sameBytes := Silmaril.KBytes.sameBytes with_kernel_fallback

trust_set bytes := {bytes.sameBytes, bytes.eqByteArray}
trust_set default := {} includes bytes

trust_policy "policy.toml" pin "0123456789abcdef"

example : KBytes.sameBytes 65536 a b = true := by edge_decide
```

`edge_decide` closes a goal `f a₁ … aₙ = true` whose head `f` is a registered procedure's
function (or the procedure named after it). It asks the policy for the native procedures the
current module may run in the current profile (`Silmaril.Trust.allowed`). Then:

1. **allowed:** `Lean.Meta.nativeEqTrue` compiles and runs the whole closed term (the function
   *and* its arguments), and on `true` adds `axiom d._native.edge.<procedure>.ax_i_j`.
2. **not allowed, with a kernel fallback:** the kernel checks `Eq.refl true : f a₁ … aₙ = true`
   in an auxiliary lemma (as `decide +kernel` does). No axiom is added.
3. **not allowed, no fallback:** it fails and names the profile, scope and procedure.

Each use is recorded (`#trust_uses`). The proposition is the goal in every profile; only the
proof term differs. A native proof is not a kernel-only proof: it trusts the compiler, the
runtime and the code the term reaches.
-/

@[expose] public meta section

namespace Silmaril.Trust

open Lean Elab Command Term Meta

/-- `native_decider name := fn [with_kernel_fallback]` registers `fn` (a closed function
returning `Bool`) as the native procedure `name`. The docstring should say what it trusts. -/
syntax (name := nativeDecider) (docComment)? "native_decider " ident " := " ident
  (&" with_kernel_fallback")? : command

/-- `trust_set name := {a, b} [includes s t]`, or `trust_set name := all`. -/
syntax (name := trustSetCmd) (docComment)? "trust_set " ident " := " (&"all" <|> ("{" ident,* "}"
  (&" includes" (ppSpace ident)+)?)) : command

/-- `trust_policy "../policy.toml" pin "<fnv1a64 hex>"` loads the `[native]` scopes of the file
(relative to the directory of the current source file) and fails if its pin is stale. -/
syntax (name := trustPolicyCmd) "trust_policy " str &" pin " str : command

/-- Close `f a₁ … aₙ = true` with the registered procedure for `f`, as the policy allows. -/
syntax (name := edgeDecide) "edge_decide" (ppSpace ident)? : tactic

/-- Print every registered procedure and recorded use as JSON lines. -/
syntax (name := trustUses) "#trust_uses" : command

/-- Check the axioms of the named declarations against the policy (see `auditDecl`). -/
syntax (name := trustAudit) "trust_audit " (ppSpace ident)+ : command

/-- The head function of a closed `Bool` term. -/
def headConst? (e : Expr) : Option Name := e.getAppFn.constName?

def returnsBool (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ b => do
    return (← whnfR b).isConstOf ``Bool

@[command_elab nativeDecider] def elabNativeDecider : CommandElab := fun stx => do
  let doc ← match stx[0].getOptional? with
    | some d => pure (← getDocStringText ⟨d⟩).trimAscii.toString
    | none => pure ""
  let name := stx[2].getId
  let fn ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo stx[4]
  let kernel := !stx[5].isNone
  let env ← getEnv
  if (procExt.getState env).contains name then
    throwError "native procedure {name} is already registered"
  let some info := env.find? fn | throwError "unknown constant {fn}"
  unless ← liftTermElabM (returnsBool info.type) do
    throwError "native procedure {name}: {fn} does not return Bool"
  if info.isUnsafe || info.isPartial then
    throwError "native procedure {name}: {fn} is unsafe or partial"
  modifyEnv (procExt.addEntry · { name, fn, kernel, doc, module := env.mainModule })

@[command_elab trustSetCmd] def elabTrustSet : CommandElab := fun stx => do
  let name := stx[2].getId
  let body := stx[4]
  let set : TrustSet ←
    if body.isToken "all" then pure { name, all := true }
    else
      let members := body[1].getSepArgs.map (·.getId)
      let includes := if body[3].isNone then #[] else body[3][1].getArgs.map (·.getId)
      pure { name, members, includes }
  if (setExt.getState (← getEnv)).contains name then
    throwError "trust set {name} is already declared"
  modifyEnv (setExt.addEntry · set)

@[command_elab trustPolicyCmd] def elabTrustPolicy : CommandElab := fun stx => do
  let file := stx[1].isStrLit?.getD ""
  let pin := stx[3].isStrLit?.getD ""
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "trust_policy: cannot locate the current source file"
  let bytes ← IO.FS.readBinFile (dir / file)
  let p ← parsePolicy file bytes
  if hex64 p.hash != pin then
    throwError "trust_policy: {file} has pin {hex64 p.hash}, not {pin}; review the change and \
      update the pin"
  if !p.scopes.any (·.module == `Silmaril) then
    throwError "trust_policy: {file} has no root [[native.scope]] with module = \"Silmaril\""
  modifyEnv (policyExt.addEntry · p)
  -- Check every scope resolves and respects its parent's bound.
  for s in p.scopes do
    match effective (← getEnv) s.module with
    | .ok _ => pure ()
    | .error e => throwError "trust_policy: {e}"

/-- The profile in force. -/
def profile : CoreM String := do
  return (← getOptions).get `silmaril.trust.profile "default"

/-- The build's ceiling. -/
def ceiling : CoreM String := do
  return (← getOptions).get `silmaril.trust.ceiling "local"

/-- The profile and ceiling, as recorded (`default`, or `default≤paranoid` under a ceiling). -/
def profileTag : CoreM String := do
  let c ← ceiling
  let p ← profile
  return if c == "local" then p else s!"{p}≤{c}"

/-- The procedures for a goal's head function. -/
def procsFor (env : Environment) (fn : Name) : Array Procedure :=
  (procExt.getState env).foldl (init := #[]) fun acc _ p => if p.fn == fn then acc.push p else acc

def recordUse (u : Use) : CoreM Unit := modifyEnv (useExt.addEntry · u)

@[tactic edgeDecide] def evalEdgeDecide : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, e, rhs) := (← whnfR ty).eq?
    | throwError "edge_decide: the goal must be `f a₁ … aₙ = true`{indentExpr ty}"
  unless (← whnfR rhs).isConstOf ``Bool.true do
    throwError "edge_decide: the right-hand side must be `true`{indentExpr ty}"
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then
    throwError "edge_decide: the term must be closed{indentExpr e}"
  let env ← getEnv
  let some fn := headConst? e | throwError "edge_decide: no head function{indentExpr e}"
  let proc ← match stx[1].getOptional? with
    | some id =>
      let some p := (procExt.getState env).find? id.getId
        | throwError "edge_decide: unknown native procedure {id.getId}"
      unless p.fn == fn do
        throwError "edge_decide: procedure {p.name} runs {p.fn}, but the goal's head is {fn}"
      pure p
    | none =>
      match procsFor env fn with
      | #[p] => pure p
      | #[] => throwError "edge_decide: {fn} is not a registered native procedure (native_decider)"
      | ps => throwError "edge_decide: {fn} is registered as {ps.map (·.name)}; name one"
  let prof ← profileTag
  let mod := env.mainModule
  let allow ← match allowed env mod (← profile) (← ceiling) with
    | .ok a => pure a
    | .error msg => throwError "edge_decide: {msg}"
  let decl := (← Term.getDeclName?).getD .anonymous
  if allow.contains proc.name then
    match ← nativeEqTrue (`edge ++ proc.name) e (axiomDeclRange? := stx) with
    | .notTrue => throwError "edge_decide: {proc.name} evaluated to false{indentExpr e}"
    | .success prf =>
      recordUse { decl, module := mod, proc := proc.name, mode := .native, profile := prof,
                  ax := prf.constName? }
      goal.assign (← mkExpectedTypeHint prf ty)
  else if proc.kernel then
    let eq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
    let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let lemma ← try
        withOptions (Elab.async.set · false) do mkAuxLemma [] eq pf
      catch ex =>
        throwError "edge_decide: the kernel did not check {proc.name} (profile {prof}): \
          {ex.toMessageData}"
    recordUse { decl, module := mod, proc := proc.name, mode := .kernel, profile := prof }
    goal.assign (← mkExpectedTypeHint (mkConst lemma) ty)
  else
    throwError "edge_decide: {proc.name} may not run natively in {mod} under profile {prof}, \
      and it has no kernel fallback"
  Tactic.replaceMainGoal []

/-! ## Provenance and audit -/

def useJson (u : Use) : Json :=
  Json.mkObj [("kind", "use"), ("decl", toString u.decl), ("module", toString u.module),
    ("procedure", toString u.proc),
    ("mode", match u.mode with | .native => "native" | .kernel => "kernel"),
    ("profile", u.profile), ("axiom", match u.ax with | some a => toJson (toString a) | none => Json.null)]

def procJson (p : Procedure) : Json :=
  Json.mkObj [("kind", "procedure"), ("name", toString p.name), ("function", toString p.fn),
    ("kernel_fallback", p.kernel), ("module", toString p.module), ("doc", p.doc)]

@[command_elab trustUses] def elabTrustUses : CommandElab := fun _ => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for p in allEntries procExt env do lines := lines.push (procJson p).compress
  for u in allEntries useExt env do lines := lines.push (useJson u).compress
  logInfo (String.intercalate "\n" lines.toList)

/-- The axioms of `decl`, split into standard, own native, inherited native and other. -/
structure AxiomReport where
  decl : Name
  ownNative : Array Name := #[]
  depNative : Array Name := #[]
  plainNative : Array Name := #[]
  other : Array Name := #[]
  /-- Every native axiom, by name. -/
  nativeAxioms : Array Name := #[]

def axiomReport (decl : Name) : CoreM AxiomReport := do
  let axs ← collectAxioms decl
  let mut r : AxiomReport := { decl }
  for a in axs do
    if (nativeAxiom? a).isSome then r := { r with nativeAxioms := r.nativeAxioms.push a }
    match nativeAxiom? a with
    | some (owner, proc, true) =>
      if decl.isPrefixOf owner || owner.isPrefixOf decl || owner == decl then
        r := { r with ownNative := r.ownNative.push proc }
      else r := { r with depNative := r.depNative.push proc }
    | some (_, tac, false) => r := { r with plainNative := r.plainNative.push tac }
    | none => r := { r with other := r.other.push a }
  return r

/-- Audit `decl`: own native procedures in the module's allowed set for the current profile,
inherited ones in `deps`, other axioms in `axioms`, and no unregistered native runs. -/
def auditDecl (decl : Name) : CommandElabM Json := do
  let env ← getEnv
  let r ← liftCoreM (axiomReport decl)
  let mod := (env.getModuleIdxFor? decl).map (env.header.moduleNames[·.toNat]!) |>.getD env.mainModule
  let eff ← match effective env mod with
    | .ok e => pure e
    | .error m => throwError "trust_audit: {m}"
  let allow ← match allowed env mod (← liftCoreM profile) (← liftCoreM ceiling) with
    | .ok a => pure a
    | .error m => throwError "trust_audit: {m}"
  let mut bad : Array String := #[]
  for p in r.ownNative do
    unless allow.contains p do bad := bad.push s!"own native {p} is not allowed"
  for p in r.depNative do
    unless eff.deps.contains p do bad := bad.push s!"inherited native {p} is outside deps"
  for t in r.plainNative do bad := bad.push s!"unregistered native run ({t})"
  for a in r.other do
    unless eff.axiomSet.contains a do bad := bad.push s!"axiom {a} is outside the axiom set"
  unless bad.isEmpty do
    throwError "trust_audit {decl}: {String.intercalate "; " bad.toList}"
  let names (xs : Array Name) : Json := toJson (xs.map toString)
  return Json.mkObj [("kind", "audit"), ("decl", toString decl), ("module", toString mod),
    ("own_native", names r.ownNative), ("dep_native", names r.depNative),
    ("axioms", names r.other), ("native_axioms", names r.nativeAxioms)]

@[command_elab trustAudit] def elabTrustAudit : CommandElab := fun stx => do
  let mut lines : Array String := #[]
  for id in stx[1].getArgs do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    lines := lines.push (← auditDecl decl).compress
  logInfo (String.intercalate "\n" lines.toList)

end Silmaril.Trust
