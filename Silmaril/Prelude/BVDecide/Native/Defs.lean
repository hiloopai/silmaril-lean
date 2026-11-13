module

public import Silmaril.Prelude.BVDecide.Defs
public import Silmaril.Prelude.Trust.Policy.Defs
public meta import Silmaril.Prelude.BVDecide.Defs
public meta import Silmaril.Prelude.Trust.Elab.Defs

/-!
# `bv_decide_policy`: `bv_decide` under the trust policy

This is the only module allowed to invoke `bv_decide` (`scripts/check-layout.sh`).
It registers the native procedure `lean.std.bv_decide.verifyBVExpr` and defines
`bv_decide_policy`, which proves a goal as follows.

1. **Kernel first.** `kernelFallback` (`bv_normalize`, standard axioms only). If it
   closes the goal, the use is recorded with `mode := .kernel` and nothing native runs.
2. **Native only if allowed.** Otherwise the goal needs SAT. Native `bv_decide` runs
   only if `Silmaril.Trust.nativeAllowed` admits the procedure in this module,
   profile and ceiling, the registration matches `nativeEvaluatedConst` and the
   pinned toolchain (`registeredToolchain`, `registeredGithash`), and the running
   Lean is that toolchain. Otherwise the tactic fails: there is **no kernel route for
   goals that need SAT**, so paranoid mode and the default profile (the procedure is
   not in the `default` set) fail on them.
3. **Provenance.** After a native run, every axiom of the proof outside the standard
   three must be new (absent before this invocation), have the `bv_decide` native name
   shape, and state exactly one closed `verifyBVExpr e cert = true`
   (`isBvDecideNativeStatement`). Each one is recorded with `mode := .native`.
   Anything else fails the tactic.

The registration is a description for audits; it authorizes nothing by itself.
-/

/-- `bv_decide` outside `edge_decide`. Lean's native evaluator runs, in compiled code,
`Std.Tactic.BVDecide.Reflect.verifyBVExpr e cert`, which is
`verifyCert (AIG.toCNF e.bitblast.relabelNat) cert`, and asserts the result as
`<decl>._native.bv_decide.ax_<n>`. Trusted beyond the kernel: the compiler and runtime
running bitblasting (hash-consed through the opaque `mixHash`), AIG to CNF, relabeling, the
`partial` LRAT parser and the LRAT checker. Untrusted: the external SAT solver. Kernel-checked:
`bv_normalize`, reification and `unsat_of_verifyBVExpr_eq_true`. Kernel fallback: partial
(`bv_decide_kernel`, normalization only); goals that need SAT have none. -/
native_tactic lean.std.bv_decide.verifyBVExpr
  evaluates Std.Tactic.BVDecide.Reflect.verifyBVExpr
  axiom_tag bv_decide
  components ["bitblasting (AIG, hash-consed through mixHash)", "AIG to CNF", "relabeling",
    "LRAT parser (partial)", "LRAT checker", "runtime externs (GMP, ByteArray, String)"]
  toolchain "leanprover/lean4:nightly-2026-11-05"
  fallback "partial: bv_normalize only (bv_decide_kernel); goals that need SAT have no kernel route"

public meta section

namespace Silmaril.Prelude.BVDecide

open Lean Elab Tactic Meta Silmaril.Trust

/-- The registered procedure. -/
def procName : Name := `lean.std.bv_decide.verifyBVExpr

/-- The toolchain the native surface above was reviewed against. -/
def registeredToolchain : String := "leanprover/lean4:nightly-2026-11-05"

/-- The commit of `registeredToolchain`; a different running Lean fails closed. -/
def registeredGithash : String := "67dafde474fbaf278d6d7f822068549bf6e532fa"

/-- Checks that the registered procedure is the one reviewed here: the evaluated constant
exists and is `nativeEvaluatedConst`, the axiom tag is `bv_decide`, no complete kernel
fallback is claimed, and the toolchain matches both the registration and the running Lean.
Returns the reason it does not, if any. -/
def registrationProblem : CoreM (Option String) := do
  let env ← getEnv
  let some p := (procExt.getState env).find? procName
    | return some s!"{procName} is not registered"
  unless env.contains p.fn do return some s!"evaluated constant {p.fn} does not exist"
  unless p.fn == nativeEvaluatedConst do
    return some s!"evaluated constant is {p.fn}, expected {nativeEvaluatedConst}"
  unless p.axiomTag == some `bv_decide do return some s!"axiom tag is {p.axiomTag}"
  if p.kernel then return some "registration claims a complete kernel fallback"
  unless p.fallbackCoverage.startsWith "partial:" do
    return some s!"fallback coverage {p.fallbackCoverage.quote} does not say it is partial"
  unless p.toolchain == registeredToolchain do
    return some s!"registered toolchain {p.toolchain}, reviewed {registeredToolchain}"
  unless Lean.githash == registeredGithash do
    return some s!"running Lean {Lean.githash}, reviewed {registeredGithash}"
  return none

/--
`bv_decide_policy` proves a goal by `bv_normalize` alone when it can (recorded as a kernel
use), and otherwise by native `bv_decide` only where the trust policy allows
`lean.std.bv_decide.verifyBVExpr`, binding each native axiom to this invocation. Goals that
need SAT fail when the procedure is not allowed: there is no kernel route for them.
-/
syntax (name := bvDecidePolicy) "bv_decide_policy" Lean.Parser.Tactic.optConfig : tactic

@[tactic bvDecidePolicy] def evalBvDecidePolicy : Tactic := fun stx => do
  let cfg : TSyntax ``Lean.Parser.Tactic.optConfig := ⟨stx[1]⟩
  let goal ← getMainGoal
  let decl := (← Term.getDeclName?).getD .anonymous
  let use (mode : Mode) (ax : Option Name) : TacticM Unit := do
    recordUse { decl, module := (← getEnv).mainModule, proc := procName, mode,
                profile := ← profileTag, ax }
  if let some why ← registrationProblem then
    throwError "bv_decide_policy: {why}"
  match ← kernelFallback goal cfg with
  | .proved =>
    use .kernel none
    replaceMainGoal []
  | .needsSat =>
    unless ← nativeAllowed procName do
      throwError "bv_decide_policy: the goal needs SAT, which has no kernel-checked route, and \
        {procName} is not allowed natively here (profile {← profileTag})"
    let before ← getEnv
    let rest ← Term.withoutErrToSorry <| Tactic.run goal do
      evalTactic (← `(tactic| bv_decide $cfg:optConfig))
    unless rest.isEmpty do throwError "bv_decide_policy: bv_decide left goals"
    let proof ← instantiateMVars (mkMVar goal)
    if proof.hasSorry then throwError "bv_decide_policy: the proof contains `sorry`"
    let axs ← nonstandardAxioms proof
    if axs.isEmpty then throwError "bv_decide_policy: expected a native axiom, found none"
    for ax in axs do
      unless isBvDecideNativeAxiom ax && !before.contains ax && (← isBvDecideNativeStatement ax) do
        throwError "bv_decide_policy: axiom {ax} is not a native evaluation of \
          {nativeEvaluatedConst} added by this invocation"
    for ax in axs do use .native (some ax)
    replaceMainGoal []

end Silmaril.Prelude.BVDecide
