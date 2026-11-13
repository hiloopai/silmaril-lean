module

public import Silmaril.Prelude.BVDecide.Defs
public import Silmaril.Prelude.Trust.Elab.Defs

/-! # `bv_decide` under the trust policy (`sil_bv_decide`)

The one framework module that invokes `bv_decide`. It registers the native procedure
`lean.std.bv_decide.verifyBVExpr` and provides `sil_bv_decide`:

1. If the policy allows `lean.std.bv_decide.verifyBVExpr` natively in this module, profile and
   ceiling (`Silmaril.Trust.nativeAllowed`), it runs `bv_decide`. It then checks the proof's
   axioms:
   * every new native axiom must be a `bv_decide` axiom whose statement is exactly one closed
     `verifyBVExpr e cert = true` (`isBvDecideNativeStatement`);
   * no other non-standard axiom may appear.

   It records one use per such axiom (`recordUse`). Otherwise it fails and leaves the goal as it
   was.
2. If native use is not allowed, it runs the kernel-only fallback (`kernelFallback`:
   `bv_normalize` with an axiom check) and records a kernel use. If the goal needs SAT, it fails
   closed: there is no kernel route for the SAT stage on this toolchain.

The native run trusts Lean's compiler and runtime for all of `verifyBVExpr`: bit-blasting,
AIG to CNF, relabeling, and the LRAT parser and checker (`docs/bv-decide-trust.md`). The
external SAT solver is untrusted. Normalization, reification and the soundness lemma are
kernel-checked.
-/

/-- Everything `bv_decide` evaluates natively when the SAT stage runs. -/
native_tactic lean.std.bv_decide.verifyBVExpr
  evaluates Std.Tactic.BVDecide.Reflect.verifyBVExpr
  axiom_tag bv_decide
  components ["bit-blasting (hash-consed through mixHash)", "AIG to CNF", "relabeling",
    "LRAT parser (partial)", "LRAT checker", "runtime: GMP, ByteArray, String"]
  toolchain "leanprover/lean4:nightly-2026-11-05"
  fallback "bv_normalize only (Silmaril.Prelude.BVDecide.kernelFallback): goals that need SAT fail"

public meta section

namespace Silmaril.Prelude.BVDecide

open Lean Elab Tactic Meta Silmaril.Trust

/-- The registry name of the native procedure. -/
def procName : Name := `lean.std.bv_decide.verifyBVExpr

/-- Prove a `BitVec`/`Bool` goal with `bv_decide` if the trust policy allows its native stage,
else with `bv_normalize` alone (see the module docstring). -/
syntax (name := silBvDecide) "sil_bv_decide" : tactic

@[tactic silBvDecide] def evalSilBvDecide : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let env ← getEnv
  let decl := (← Term.getDeclName?).getD .anonymous
  let prof ← profileTag
  let mod := env.mainModule
  if ← nativeAllowed procName then
    let saved ← saveState
    let rest ← Term.withoutErrToSorry <| Tactic.run goal (evalTactic (← `(tactic| bv_decide)))
    unless rest.isEmpty do
      saved.restore
      throwError "sil_bv_decide: bv_decide left goals"
    let proof ← instantiateMVars (mkMVar goal)
    let mut natives : Array Name := #[]
    for ax in ← nonstandardAxioms proof do
      if isBvDecideNativeAxiom ax && (← isBvDecideNativeStatement ax) then
        natives := natives.push ax
      else
        saved.restore
        throwError "sil_bv_decide: the proof depends on {ax}, which is not one verified \
          `verifyBVExpr … = true` evaluation"
    for ax in natives do
      recordUse { decl, module := mod, proc := procName, mode := .native, profile := prof,
                  ax := some ax }
    replaceMainGoal []
  else
    match ← kernelFallback goal with
    | .proved =>
      recordUse { decl, module := mod, proc := procName, mode := .kernel, profile := prof }
      replaceMainGoal []
    | .needsSat =>
      throwError "sil_bv_decide: {procName} may not run natively in {mod} under profile {prof}, \
        and bv_normalize alone does not close the goal (it needs the SAT stage)"

end Silmaril.Prelude.BVDecide
