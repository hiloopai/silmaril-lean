import Lean
/-! `kernel_rfl`, as in `Silmaril.Wasm.Verify.Kernel` (copied so that the benchmark needs no
Mathlib closure): close `lhs = rhs` by the kernel's definitional check only. -/
open Lean Elab Tactic Meta in
elab "kernel_rfl" : tactic => do
  liftMetaTactic1 fun g => do
    let g ← g.cleanup
    let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
    return g
  closeMainGoalUsing `kernel_rfl fun ty _ => do
    let ty ← instantiateMVars ty
    let pf ← forallTelescope ty fun xs body => do
      let some (_, l, _) := body.eq? | throwError "kernel_rfl: the goal is not an equation"
      mkLambdaFVars xs (← mkEqRefl l)
    let lvls := (collectLevelParams {} ty).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter lvls.contains
    let n ← withOptions (Elab.async.set · false) do mkAuxLemma lemmaLevels ty pf
    return mkConst n (lemmaLevels.map .param)
