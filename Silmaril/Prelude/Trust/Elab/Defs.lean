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
  (&" with_kernel_fallback")? (&" native " ident &" via " ident)? (&" format " ident)?
  (&" sound " ident)? : command

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
  let native ← if stx[6].isNone then pure none else do
    let nfn ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo stx[6][1])
    let thm ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo stx[6][3])
    let some info := (← getEnv).find? thm | throwError "unknown theorem {thm}"
    match info.type.eq? with
    | some (_, l, r) =>
      unless l.getAppFn.isConstOf nfn && r.getAppFn.isConstOf fn && l.getAppNumArgs == 0 do
        throwError "native_decider {name}: {thm} must state `@{nfn} = @{fn}`"
    | none => throwError "native_decider {name}: {thm} must state `@{nfn} = @{fn}`"
    pure (some (nfn, thm))
  let format := if stx[7].isNone then none else some stx[7][1].getId
  let sound ← if stx[8].isNone then pure none else
    some <$> liftTermElabM (realizeGlobalConstNoOverloadWithInfo stx[8][1])
  let env ← getEnv
  if (procExt.getState env).contains name then
    throwError "native procedure {name} is already registered"
  let some info := env.find? fn | throwError "unknown constant {fn}"
  unless ← liftTermElabM (returnsBool info.type) do
    throwError "native procedure {name}: {fn} does not return Bool"
  if info.isUnsafe || info.isPartial then
    throwError "native procedure {name}: {fn} is unsafe or partial"
  if let some thm := sound then
    let some info := env.find? thm | throwError "unknown theorem {thm}"
    unless info.type.find? (fun e => e.isConstOf fn) |>.isSome do
      throwError "native procedure {name}: the soundness theorem {thm} does not mention {fn}"
  modifyEnv (procExt.addEntry · { name, fn, kernel, doc, module := env.mainModule, format, sound, native })

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

/-- A checker used through a structure (`C.check b a`, as with `KBytes.FormatChecker`) is
exposed as the registered function the structure stores, without evaluating the arguments. -/
def exposeHead (env : Environment) (e : Expr) : MetaM Expr := do
  let some h := headConst? e | return e
  unless (procsFor env h).isEmpty do return e
  let args := e.getAppArgs
  -- Try each prefix `h a₁ … aₖ`, unfolding one definition or projection at a time and stopping
  -- at the first registered head, so the registered function itself is never unfolded.
  for k in [1:args.size] do
    let mut f := mkAppN e.getAppFn (args.extract 0 k)
    for _ in [0:16] do
      if let some h' := f.getAppFn.constName? then
        unless (procsFor env h').isEmpty do
          return mkAppN f (args.extract k args.size)
      let f' ← whnfCore f
      if f' != f then f := f'; continue
      let next ← match f with
        | .proj n i s => pure ((← unfoldDefinition? s).map (Expr.proj n i ·))
        | _ => unfoldDefinition? f
      match next with
      | some f' => f := f'
      | none => break
  return e

/-- **The backend hook.** A proof of `e = true` for a closed `Bool` term `e` whose head is a
registered procedure (or the procedure `proc?`), as the policy allows in the current module,
profile and ceiling: a native run (of the paired native implementation, if registered, with its
result transferred by the pairing theorem), the kernel fallback, or an error. Records the use.
Tactics and adapters for other formats call this instead of the registry internals. -/
def decideEdge (e : Expr) (proc? : Option Name := none) (ref : Syntax := .missing) :
    TermElabM Expr := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then
    throwError "edge_decide: the term must be closed{indentExpr e}"
  let env ← getEnv
  let e ← exposeHead env e
  let some fn := headConst? e | throwError "edge_decide: no head function{indentExpr e}"
  let proc ← match proc? with
    | some n =>
      let some p := (procExt.getState env).find? n
        | throwError "edge_decide: unknown native procedure {n}"
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
  let eqTrue (x : Expr) := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) x (mkConst ``Bool.true)
  if allow.contains proc.name then
    let us := e.getAppFn.constLevels!
    let args := e.getAppArgs
    let (run, transfer) := match proc.native with
      | some (nfn, thm) => (mkAppN (.const nfn us) args, some thm)
      | none => (e, none)
    match ← nativeEqTrue (`edge ++ proc.name) run (axiomDeclRange? := ref) with
    | .notTrue => throwError "edge_decide: {proc.name} evaluated to false{indentExpr run}"
    | .success ax =>
      recordUse { decl, module := mod, proc := proc.name, mode := .native, profile := prof,
                  ax := ax.constName? }
      match transfer with
      | none => mkExpectedTypeHint ax (eqTrue e)
      | some thm =>
        -- `thm : @nfn = @fn` turns `nfn args = true` into `fn args = true`.
        let fty ← inferType (.const fn us)
        let motive := Expr.lam `g fty (eqTrue (mkAppN (.bvar 0) args)) .default
        let p ← mkCongrArg motive (.const thm us)
        mkExpectedTypeHint (← mkEqMP p ax) (eqTrue e)
  else if proc.kernel then
    let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let lemma ← try
        withOptions (Elab.async.set · false) do mkAuxLemma [] (eqTrue e) pf
      catch ex =>
        throwError "edge_decide: the kernel did not check {proc.name} (profile {prof}): \
          {ex.toMessageData}"
    recordUse { decl, module := mod, proc := proc.name, mode := .kernel, profile := prof }
    return mkConst lemma
  else
    throwError "edge_decide: {proc.name} may not run natively in {mod} under profile {prof}, \
      and it has no kernel fallback"

@[tactic edgeDecide] def evalEdgeDecide : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, e, rhs) := (← whnfR ty).eq?
    | throwError "edge_decide: the goal must be `f a₁ … aₙ = true`{indentExpr ty}"
  unless (← whnfR rhs).isConstOf ``Bool.true do
    throwError "edge_decide: the right-hand side must be `true`{indentExpr ty}"
  let prf ← decideEdge e (stx[1].getOptional?.map (·.getId)) stx
  goal.assign (← mkExpectedTypeHint prf ty)
  Tactic.replaceMainGoal []

/-! ## Provenance and audit -/

def nameJson : Option Name → Json
  | some n => toJson (toString n)
  | none => Json.null

def useJson (u : Use) : Json :=
  Json.mkObj [("schema", schemaVersion), ("kind", "use"), ("decl", toString u.decl), ("module", toString u.module),
    ("procedure", toString u.proc),
    ("mode", match u.mode with | .native => "native" | .kernel => "kernel"),
    ("profile", u.profile), ("axiom", match u.ax with | some a => toJson (toString a) | none => Json.null)]

def procJson (p : Procedure) : Json :=
  Json.mkObj [("schema", schemaVersion), ("kind", "procedure"), ("name", toString p.name),
    ("function", toString p.fn), ("kernel_fallback", p.kernel), ("module", toString p.module),
    ("format", nameJson p.format), ("sound", nameJson p.sound),
    ("native_function", nameJson (p.native.map (·.1))), ("native_eq", nameJson (p.native.map (·.2))),
    ("doc", p.doc)]

def setJson (env : Environment) (s : TrustSet) : Json :=
  let resolved : Json := match resolve env s.name with
    | .ok .all => toJson "all"
    | .ok (.some ns) => toJson (ns.toList.map toString)
    | .error e => toJson s!"error: {e}"
  Json.mkObj [("schema", schemaVersion), ("kind", "set"), ("name", toString s.name),
    ("all", s.all), ("members", toJson (s.members.map toString)),
    ("includes", toJson (s.includes.map toString)), ("resolved", resolved)]

def scopeJson (p : Policy) (s : Scope) : Json :=
  Json.mkObj [("schema", schemaVersion), ("kind", "scope"), ("module", toString s.module),
    ("max", nameJson s.max), ("default", nameJson s.dflt), ("deps", nameJson s.deps),
    ("axioms", nameJson s.axiomSet), ("policy_file", p.file), ("policy_pin", hex64 p.hash)]

@[command_elab trustUses] def elabTrustUses : CommandElab := fun _ => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for p in allEntries procExt env do lines := lines.push (procJson p).compress
  for u in allEntries useExt env do lines := lines.push (useJson u).compress
  logInfo (String.intercalate "\n" lines.toList)

/-- Print the trust sets and the policy scopes as JSON lines. -/
syntax (name := trustRegistry) "#trust_registry" : command

@[command_elab trustRegistry] def elabTrustRegistry : CommandElab := fun _ => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for s in allEntries setExt env do lines := lines.push (setJson env s).compress
  if let some p := policyExt.getState env then
    for s in p.scopes do lines := lines.push (scopeJson p s).compress
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
  return Json.mkObj [("schema", schemaVersion), ("kind", "audit"), ("profile", ← liftCoreM profileTag), ("decl", toString decl), ("module", toString mod),
    ("own_native", names r.ownNative), ("dep_native", names r.depNative),
    ("axioms", names r.other), ("native_axioms", names r.nativeAxioms)]

@[command_elab trustAudit] def elabTrustAudit : CommandElab := fun stx => do
  let mut lines : Array String := #[]
  for id in stx[1].getArgs do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    lines := lines.push (← auditDecl decl).compress
  logInfo (String.intercalate "\n" lines.toList)

end Silmaril.Trust

namespace Silmaril.Trust

open Lean Elab Command

/-! ## Reading the dump back

`ofJson?` inverts the emitters; `#trust_roundtrip` checks it on everything in the
environment, and `#trust_dump "path"` writes the dump that the project database ingests. -/

def nameOfJson? (j : Json) : Option (Option Name) :=
  match j with
  | .null => some none
  | .str s => some (some s.toName)
  | _ => none

def procOfJson? (j : Json) : Except String Procedure := do
  let str (k : String) : Except String String := j.getObjValAs? String k
  let opt (k : String) : Except String (Option Name) := do
    match nameOfJson? (← j.getObjVal? k) with
    | some v => pure v
    | none => throw s!"{k}: expected a string or null"
  unless (← str "schema") == schemaVersion && (← str "kind") == "procedure" do
    throw "not a v1 procedure"
  let native ← match ← opt "native_function", ← opt "native_eq" with
    | some f, some t => pure (some (f, t))
    | none, none => pure none
    | _, _ => throw "native_function and native_eq go together"
  return { name := (← str "name").toName, fn := (← str "function").toName,
           kernel := ← j.getObjValAs? Bool "kernel_fallback", doc := ← str "doc",
           module := (← str "module").toName, format := ← opt "format", sound := ← opt "sound",
           native }

def useOfJson? (j : Json) : Except String Use := do
  let str (k : String) : Except String String := j.getObjValAs? String k
  unless (← str "schema") == schemaVersion && (← str "kind") == "use" do throw "not a v1 use"
  let mode ← match ← str "mode" with
    | "native" => pure Mode.native
    | "kernel" => pure Mode.kernel
    | m => throw s!"mode {m}"
  let ax ← match nameOfJson? (← j.getObjVal? "axiom") with
    | some a => pure a
    | none => throw "axiom: expected a string or null"
  return { decl := (← str "decl").toName, module := (← str "module").toName,
           proc := (← str "procedure").toName, mode, profile := ← str "profile", ax }

def procBEq (a b : Procedure) : Bool :=
  a.name == b.name && a.fn == b.fn && a.kernel == b.kernel && a.doc == b.doc &&
    a.module == b.module && a.format == b.format && a.sound == b.sound && a.native == b.native

/-- Every line of the dump: procedures, uses, sets and scopes. -/
def dumpLines (env : Environment) : Array Json := Id.run do
  let mut out := #[]
  for p in allEntries procExt env do out := out.push (procJson p)
  for u in allEntries useExt env do out := out.push (useJson u)
  for s in allEntries setExt env do out := out.push (setJson env s)
  if let some p := policyExt.getState env then
    for s in p.scopes do out := out.push (scopeJson p s)
  return out

/-- Re-read every procedure and use from its printed line and compare. -/
syntax (name := trustRoundtrip) "#trust_roundtrip" : command

@[command_elab trustRoundtrip] def elabTrustRoundtrip : CommandElab := fun _ => do
  let env ← getEnv
  let procs := allEntries procExt env
  let uses := allEntries useExt env
  for p in procs do
    let line := (procJson p).compress
    match Json.parse line >>= procOfJson? with
    | .ok q => unless procBEq p q do throwError "roundtrip changed procedure {p.name}"
    | .error e => throwError "roundtrip of procedure {p.name}: {e}"
  for u in uses do
    let line := (useJson u).compress
    match Json.parse line >>= useOfJson? with
    | .ok v => unless u == v do throwError "roundtrip changed the use of {u.proc} in {u.decl}"
    | .error e => throwError "roundtrip of a use of {u.proc}: {e}"
  logInfo m!"roundtrip ok: {procs.size} procedures, {uses.size} uses"

/-- `#trust_dump "path"` writes the dump (JSON lines) to `path`, relative to the working
directory. Used by tools; nothing in the library calls it. -/
syntax (name := trustDump) "#trust_dump " str : command

@[command_elab trustDump] def elabTrustDump : CommandElab := fun stx => do
  let lines := (dumpLines (← getEnv)).map (·.compress)
  IO.FS.writeFile (stx[1].isStrLit?.getD "trust.jsonl") (String.intercalate "\n" lines.toList ++ "\n")

end Silmaril.Trust

/-! ## Same-target pairs

When the native and kernel checkers take different arguments (a `ByteArray` read at run time
against kernel bytes, say), a function equality cannot pair them. Instead each checker proves
the same proposition through its own soundness theorem:

```
example : Parses F A :=
  by edge_pair (native := fun h => fastSound bytes A h) (kernel := fun h => kernelSound kb A h)
```

`native` and `kernel` have types `f a₁ … aₙ = true → P` and `g b₁ … bₘ = true → P` for the
goal `P`, with `f` and `g` registered procedures. If the policy lets `f` run natively here,
`f a₁ … aₙ` runs natively. Otherwise `g b₁ … bₘ` goes through `decideEdge`: the kernel if `g`
has a fallback, natively if `g` itself is allowed, or failure. The proposition is `P` either
way.
-/

namespace Silmaril.Trust

open Lean Elab Tactic Meta

syntax (name := edgePair) "edge_pair " "(" &"native" " := " term ")" "(" &"kernel" " := " term ")" :
  tactic

/-- Whether procedure `name` may run natively here. -/
def nativeAllowed (name : Name) : CoreM Bool := do
  let env ← getEnv
  match allowed env env.mainModule (← profile) (← ceiling) with
  | .ok a => return a.contains name
  | .error _ => return false

@[tactic edgePair] def evalEdgePair : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let side (t : Syntax) : TacticM (Expr × Expr) := do
    let h ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let h ← instantiateMVars h
    let ty ← whnfR (← inferType h)
    let .forallE _ hyp body _ := ty
      | throwError "edge_pair: {t} must have type `f … = true → P`"
    unless ← isDefEq body target do
      throwError "edge_pair: {t} proves{indentExpr body}\nnot the goal{indentExpr target}"
    let some (_, e, _) := hyp.eq? | throwError "edge_pair: {t}'s hypothesis is not `f … = true`"
    return (h, e)
  let (hn, en) ← side stx[4]
  let (hk, ek) ← side stx[9]
  let env ← getEnv
  let nativeOk ← do
    let e' ← exposeHead env en
    match headConst? e' with
    | some f =>
      match procsFor env f with
      | #[p] => nativeAllowed p.name
      | _ => pure false
    | none => pure false
  let prf ← if nativeOk then
      pure (mkApp hn (← decideEdge en none stx))
    else
      pure (mkApp hk (← decideEdge ek none stx))
  goal.assign prf
  replaceMainGoal []

end Silmaril.Trust
