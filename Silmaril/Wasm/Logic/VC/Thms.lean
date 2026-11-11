module

public import Silmaril.Proofs.Wasm.Logic.VC.Sound
public import Silmaril.Proofs.Wasm.Logic.VC.Simp
public import Silmaril.Proofs.Wasm.Logic.VC.Exec

/-!
# A verification-condition generator for structured Wasm code: results

Proofs in `Silmaril.Proofs.Wasm.Logic.VC.{Rules,Sound,Simp}`, at every profile and for every host
relation, for every family of loop invariants:

* **`wpc_sound`**: `wpc inv k is Q s f vs → HWP P host s f (vals vs ++ expression is) Q`;
* **`FSpecValid.of_wpc`**: a function specification (`Silmaril.Wasm.Logic.Hoare.FSpecValid`) from
  the generator's condition for the body in the callee's initial frame;
* the per-construct rules `hwp_block`, `hwp_loop` and inversions (`ctl_block`, …,
  `popI32_eq`, `popSelect_eq`).

The tactic **`wat_vc`** (optionally `wat_vc [lemmas]`, e.g. the definition of the program)
evaluates the condition with `simp` (the generator, `exec1`, the frame's locals, integer
arithmetic and comparisons), introduces the loop-invariant hypotheses, splits conditionals and
tries `omega` and `bv_omega` on what remains. Whatever it cannot close is left as an ordinary
goal about `BitVec`s; it adds no axiom (no SAT solving, no compiled evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

/-- Evaluate and discharge verification conditions of `wpc` (see the module docstring). -/
syntax "wat_vc" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wat_vc) => `(tactic| wat_vc [])
  | `(tactic| wat_vc [$ls,*]) => `(tactic| (
      simp [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.VC.loops,
        Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ, Silmaril.Wasm.Logic.VC.loopQ,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.VC.popSelect, Silmaril.Wasm.Logic.VC.vc_exec1_nop, Silmaril.Wasm.Logic.VC.vc_exec1_drop,
        Silmaril.Wasm.Logic.VC.vc_exec1_intConst,
        Silmaril.Wasm.Logic.VC.vc_exec1_i32Const, Silmaril.Wasm.Logic.VC.vc_exec1_i64Const, Silmaril.Wasm.Logic.VC.vc_exec1_localGet,
        Silmaril.Wasm.Logic.VC.vc_exec1_localSet, Silmaril.Wasm.Logic.VC.vc_exec1_localTee,
        Silmaril.Wasm.Logic.VC.vc_exec1_intUnOp, Silmaril.Wasm.Logic.VC.vc_exec1_intBinOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intTestOp, Silmaril.Wasm.Logic.VC.vc_exec1_intRelOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intLoad, Silmaril.Wasm.Logic.VC.vc_exec1_intLoadPack,
        Silmaril.Wasm.Logic.VC.vc_exec1_intStore, Silmaril.Wasm.Logic.VC.vc_exec1_intStorePack,
        Silmaril.Wasm.Logic.VC.exec1_globalGet_idx, Silmaril.Wasm.Logic.VC.exec1_globalSet_if,
        Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_self, Silmaril.Wasm.Logic.VC.cvt1,
        Silmaril.Wasm.Logic.VC.tableVC, Silmaril.Wasm.Logic.VC.callVC, Silmaril.Wasm.Logic.VC.callK,
        Silmaril.Wasm.Logic.VC.and_ones64, Silmaril.Wasm.Logic.VC.and_ones32, Silmaril.Wasm.Logic.VC.wrap64_eq,
        Silmaril.Wasm.Logic.VC.extendU32_eq, Silmaril.Wasm.Logic.VC.extendS32_eq,
        Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
        Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
        Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
        Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Idx.toNat,
        Silmaril.Wasm.Numerics.bool32, Silmaril.Wasm.Execution.Core.Val.i32,
        Silmaril.Wasm.Execution.Core.Val.i64,
        Silmaril.Wasm.Logic.VC.defaultVal_int32, Silmaril.Wasm.Logic.VC.defaultVal_int64,
        Silmaril.Wasm.Logic.VC.defaultVal_i32,
        Silmaril.Wasm.Logic.VC.defaultVal_i64, Silmaril.Wasm.Logic.VC.numVal_i32_eq,
        Silmaril.Wasm.Logic.VC.numVal_i64_eq, Silmaril.Wasm.Logic.VC.intRelOp_i32_ltS,
        Silmaril.Wasm.Logic.VC.intRelOp_i32_leS, Silmaril.Wasm.Logic.VC.intRelOp_i32_gtS,
        Silmaril.Wasm.Logic.VC.intRelOp_i32_geS, Silmaril.Wasm.Logic.VC.intRelOp_i64_eq,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_ne, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltU,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_leU, Silmaril.Wasm.Logic.VC.intRelOp_i64_gtU,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geU, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_leS, Silmaril.Wasm.Logic.VC.intRelOp_i64_gtS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geS, Silmaril.Wasm.Logic.VC.intTestOp_i32,
        Silmaril.Wasm.Logic.VC.intTestOp_i64, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
        Silmaril.Wasm.Logic.Core.ofNat_i32_width,
        Silmaril.Wasm.Logic.Core.ofNat_i64_width, Silmaril.Wasm.Logic.Core.setWidth_i32_width,
        Silmaril.Wasm.Logic.Core.setWidth_i64_width, $ls,*] <;>
      (try intros) <;> (try subst_vars) <;>
      (try simp_all [Silmaril.Wasm.Logic.Core.localVal?, Silmaril.Wasm.Execution.Core.Frame.local?,
        Silmaril.Wasm.Execution.Core.Frame.setLocal, Silmaril.Wasm.Logic.Core.popInt,
        Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.VC.vc_exec1_nop, Silmaril.Wasm.Logic.VC.vc_exec1_drop,
        Silmaril.Wasm.Logic.VC.vc_exec1_intConst,
        Silmaril.Wasm.Logic.VC.vc_exec1_i32Const, Silmaril.Wasm.Logic.VC.vc_exec1_i64Const, Silmaril.Wasm.Logic.VC.vc_exec1_localGet,
        Silmaril.Wasm.Logic.VC.vc_exec1_localSet, Silmaril.Wasm.Logic.VC.vc_exec1_localTee,
        Silmaril.Wasm.Logic.VC.vc_exec1_intUnOp, Silmaril.Wasm.Logic.VC.vc_exec1_intBinOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intTestOp, Silmaril.Wasm.Logic.VC.vc_exec1_intRelOp,
        Silmaril.Wasm.Logic.VC.vc_exec1_intLoad, Silmaril.Wasm.Logic.VC.vc_exec1_intLoadPack,
        Silmaril.Wasm.Logic.VC.vc_exec1_intStore, Silmaril.Wasm.Logic.VC.vc_exec1_intStorePack,
        Silmaril.Wasm.Logic.VC.exec1_globalGet_idx, Silmaril.Wasm.Logic.VC.exec1_globalSet_if,
        Silmaril.Wasm.Logic.VC.globalVal_setGlobalIdx_self, Silmaril.Wasm.Logic.VC.cvt1,
        Silmaril.Wasm.Logic.VC.tableVC, Silmaril.Wasm.Logic.VC.callVC, Silmaril.Wasm.Logic.VC.callK,
        Silmaril.Wasm.Logic.VC.and_ones64, Silmaril.Wasm.Logic.VC.and_ones32, Silmaril.Wasm.Logic.VC.wrap64_eq,
        Silmaril.Wasm.Logic.VC.extendU32_eq, Silmaril.Wasm.Logic.VC.extendS32_eq,
        Silmaril.Wasm.Numerics.bool32,
        Silmaril.Wasm.Logic.VC.numVal_i32_eq, Silmaril.Wasm.Logic.VC.numVal_i64_eq,
        Silmaril.Wasm.Idx.toNat, Silmaril.Wasm.Execution.Core.Val.i32,
        Silmaril.Wasm.Execution.Core.Val.i64, Silmaril.Wasm.Logic.Core.intRelOp_i32_eq,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_ne, Silmaril.Wasm.Logic.Core.intRelOp_i32_ltU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_leU, Silmaril.Wasm.Logic.Core.intRelOp_i32_gtU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_geU, Silmaril.Wasm.Logic.VC.intRelOp_i32_ltS,
        Silmaril.Wasm.Logic.VC.intRelOp_i32_leS, Silmaril.Wasm.Logic.VC.intRelOp_i32_gtS,
        Silmaril.Wasm.Logic.VC.intRelOp_i32_geS, Silmaril.Wasm.Logic.VC.intRelOp_i64_eq,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_ne, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltU,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_leU, Silmaril.Wasm.Logic.VC.intRelOp_i64_gtU,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geU, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_leS, Silmaril.Wasm.Logic.VC.intRelOp_i64_gtS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geS, Silmaril.Wasm.Logic.VC.intTestOp_i32,
        Silmaril.Wasm.Logic.VC.intTestOp_i64, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
        Silmaril.Wasm.Logic.Core.ofNat_i32_width,
        Silmaril.Wasm.Logic.Core.ofNat_i64_width, Silmaril.Wasm.Logic.Core.setWidth_i32_width,
        Silmaril.Wasm.Logic.Core.setWidth_i64_width, $ls,*]) <;>
      (try and_intros) <;> (try intros) <;> (try split_ifs at *) <;> (try simp_all) <;> (try omega) <;>
      (try (exfalso; omega)) <;> (try bv_omega)))

end Silmaril.Wasm.Logic.VC
