module

public import Silmaril.Wasm.Logic.VC.Thms
public import Silmaril.Proofs.Wasm.Logic.VCCalls.Lemmas

/-!
# `wat_vc_calls`: `wat_vc` with call, `br_table` and block pre-rewrites

**`wat_vc_calls [lemmas]`** is `wat_vc` for code with calls: its first pass uses `wat_vc_core`
(no `callVC` unfolding), rewrites `labelQ`/`loopQ` only at known outcomes (`labelQ_normal`, …), selects the entry of a
`br_table` at a known index (`tableVC_cons_self`, …)
and pre-rewrites with `forall_inv_eq`, so the caller passes one call
lemma per callee as a pre-rewrite (`↓callVC_fn hx hΓ hpost`, `Silmaril.Proofs.Wasm.Logic.VCCalls.Lemmas`).
Its second pass is `wat_vc`'s (calls without a lemma are unfolded there). Same goals, far less
`simp` work for bodies with calls under loops.

The lemmas (`callVC_at`, `callVC_fn`, `labelQ_*`, `loopQ_*`, `tableVC_*`, `forall_inv_eq`) are
proved in `Silmaril.Proofs.Wasm.Logic.VCCalls.Lemmas`. A separate header so that runtime closures
importing `Silmaril.Wasm.Logic.VC.Thms` do not pull in these proofs. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

/-- `wat_vc` with call lemmas as pre-rewrites (see the module docstring). -/
syntax "wat_vc_calls" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| wat_vc_calls [$ls,*]) => `(tactic| (
      simp [↓Silmaril.Wasm.Logic.VC.forall_inv_eq, ↓Silmaril.Wasm.Logic.VC.tableVC_cons_self,
        ↓Silmaril.Wasm.Logic.VC.tableVC_cons_of_ne, ↓Silmaril.Wasm.Logic.VC.tableVC_nil_of_le,
        Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl,
        Silmaril.Wasm.Logic.VC.loops,
        Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ_normal,
        Silmaril.Wasm.Logic.VC.labelQ_br_zero, Silmaril.Wasm.Logic.VC.labelQ_br_succ,
        Silmaril.Wasm.Logic.VC.labelQ_ret, Silmaril.Wasm.Logic.VC.labelQ_trap,
        Silmaril.Wasm.Logic.VC.labelQ_throw, Silmaril.Wasm.Logic.VC.labelQ_tail,
        Silmaril.Wasm.Logic.VC.loopQ_normal, Silmaril.Wasm.Logic.VC.loopQ_br_zero,
        Silmaril.Wasm.Logic.VC.loopQ_br_succ, Silmaril.Wasm.Logic.VC.loopQ_ret,
        Silmaril.Wasm.Logic.VC.loopQ_trap, Silmaril.Wasm.Logic.VC.loopQ_throw,
        Silmaril.Wasm.Logic.VC.loopQ_tail,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.VC.popSelect,
        Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
        Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Logic.VC.defaultVal_int32,
        Silmaril.Wasm.Logic.VC.defaultVal_int64, Silmaril.Wasm.Logic.VC.defaultVal_i32,
        Silmaril.Wasm.Logic.VC.defaultVal_i64, wat_vc_core, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
        $ls,*] <;>
      (try intros) <;> (try subst_vars) <;>
      (try simp_all [wat_vc_simp, Silmaril.Wasm.Logic.Core.intRelOp_i32_eq,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_ne, Silmaril.Wasm.Logic.Core.intRelOp_i32_ltU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_leU, Silmaril.Wasm.Logic.Core.intRelOp_i32_gtU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_geU, -Silmaril.Wasm.Logic.Core.intTestOp_eqz, $ls,*]) <;>
      (try and_intros) <;> (try intros) <;> (try split_ifs at *) <;> (try simp_all) <;> (try omega) <;>
      (try (exfalso; omega)) <;> (try bv_omega)))

end Silmaril.Wasm.Logic.VC
