module

public import Silmaril.Proofs.Wasm.Logic.VC.Sound
public import Silmaril.Proofs.Wasm.Logic.VC.Simp
public import Silmaril.Proofs.Wasm.Logic.VC.Exec
public import Silmaril.Wasm.Logic.VC.Simp.Defs

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
evaluates the condition with `simp`: it unfolds the generator's definitions by name and uses the
simp set **`wat_vc_simp`** (`Silmaril.Wasm.Logic.VC.Simp.Defs`: `cvt1`, `tableVC`, `callVC`, `callK`,
`exec1` by instruction form, frame helpers, integer arithmetic and comparisons). It introduces the loop-invariant hypotheses, splits conditionals and
tries `omega` and `bv_omega` on what remains. Whatever it cannot close is left as an ordinary
goal about `BitVec`s; it adds no axiom (no SAT solving, no compiled evaluation).

`wat_vc_calls`, the variant for code with calls, is in `Silmaril.Wasm.Logic.VCCalls.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

/-! The members of the `wat_vc` simp sets: `wat_vc_simp`, and `wat_vc_core` (the same without
`callVC` and `tableVC`), registered in `Silmaril.Wasm.Logic.VC.Simp.Defs` (an attribute cannot be
used in the module that declares it). -/

attribute [wat_vc_simp] callVC tableVC

attribute [wat_vc_simp, wat_vc_core]
  -- the instructions `wpc` handles itself
  cvt1 callK
  -- `exec1`, one equation per instruction form (a symbolic store stays symbolic)
  vc_exec1_nop vc_exec1_drop vc_exec1_intConst vc_exec1_i32Const vc_exec1_i64Const
  vc_exec1_localGet vc_exec1_localSet vc_exec1_localTee vc_exec1_intUnOp vc_exec1_intBinOp
  vc_exec1_intTestOp vc_exec1_intRelOp vc_exec1_intLoad vc_exec1_intLoadPack vc_exec1_intStore
  vc_exec1_intStorePack exec1_globalGet_idx exec1_globalSet_if globalVal_setGlobalIdx_self
  -- frames, stacks and values
  Silmaril.Wasm.Logic.Core.popInt Silmaril.Wasm.Logic.Core.popV Silmaril.Wasm.Logic.Core.localVal?
  Silmaril.Wasm.Execution.Core.Frame.local? Silmaril.Wasm.Execution.Core.Frame.setLocal
  Silmaril.Wasm.Idx.toNat Silmaril.Wasm.Numerics.bool32
  Silmaril.Wasm.Execution.Core.Val.i32 Silmaril.Wasm.Execution.Core.Val.i64
  numVal_i32_eq numVal_i64_eq
  -- integer normal forms
  and_ones64 and_ones32 wrap64_eq extendU32_eq extendS32_eq
  intRelOp_i32_ltS intRelOp_i32_leS intRelOp_i32_gtS intRelOp_i32_geS
  intRelOp_i64_eq intRelOp_i64_ne intRelOp_i64_ltU intRelOp_i64_leU intRelOp_i64_gtU
  intRelOp_i64_geU intRelOp_i64_ltS intRelOp_i64_leS intRelOp_i64_gtS intRelOp_i64_geS
  intTestOp_i32 intTestOp_i64
  Silmaril.Wasm.Logic.Core.ofNat_i32_width Silmaril.Wasm.Logic.Core.ofNat_i64_width
  Silmaril.Wasm.Logic.Core.setWidth_i32_width Silmaril.Wasm.Logic.Core.setWidth_i64_width


/-- `globalVal` under the `?` name of the `Option`-valued accessors (`Silmaril.Wasm.Logic.Core.localVal?`). -/
abbrev globalVal? {H : Type} (s : Silmaril.Wasm.Execution.Core.Store H)
    (m : Silmaril.Wasm.Execution.Core.ModuleInst) (x : Nat) : Option Silmaril.Wasm.Execution.Core.Val :=
  globalVal s m x

/-- Evaluate and discharge verification conditions of `wpc` (see the module docstring). -/
syntax "wat_vc" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wat_vc) => `(tactic| wat_vc [])
  | `(tactic| wat_vc [$ls,*]) => `(tactic| (
      simp [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.VC.loops,
        Silmaril.Wasm.Logic.VC.enterVC, Silmaril.Wasm.Logic.VC.labelQ, Silmaril.Wasm.Logic.VC.loopQ,
        Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.VC.popSelect,
        Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Examples.Common.bodyPost,
        Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, Silmaril.Wasm.Logic.VC.defaultVal_int32,
        Silmaril.Wasm.Logic.VC.defaultVal_int64, Silmaril.Wasm.Logic.VC.defaultVal_i32,
        Silmaril.Wasm.Logic.VC.defaultVal_i64, wat_vc_simp, -Silmaril.Wasm.Logic.Core.intTestOp_eqz,
        $ls,*] <;>
      (try intros) <;> (try subst_vars) <;>
      (try simp_all [wat_vc_simp, Silmaril.Wasm.Logic.Core.intRelOp_i32_eq,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_ne, Silmaril.Wasm.Logic.Core.intRelOp_i32_ltU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_leU, Silmaril.Wasm.Logic.Core.intRelOp_i32_gtU,
        Silmaril.Wasm.Logic.Core.intRelOp_i32_geU, -Silmaril.Wasm.Logic.Core.intTestOp_eqz, $ls,*]) <;>
      (try and_intros) <;> (try intros) <;> (try split_ifs at *) <;> (try simp_all) <;> (try omega) <;>
      (try (exfalso; omega)) <;> (try bv_omega)))

end Silmaril.Wasm.Logic.VC
