module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Dispatch
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.DivRem

/-!
# Integer numerics: each dispatcher, for every opcode at once

`applies_binop_int`, `applies_unop_int`, `applies_testop_int`, `applies_relop_int`: at an integer
type, `$binop_`, `$unop_`, `$testop_` and `$relop_` denote `IntegerN`'s `ibinop_` (as a list:
empty exactly on a trap), `iunop_`, `itestop_` and `irelop_`, which `ibinop_agree` & co. equate
with Core's `intBinOp`, `intUnOp`, `intTestOp`, `intRelOp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV optUNV NumEnv)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- `$idiv_` at any divisor. -/
theorem callDef_idiv (hB : IntB B) (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {ρ : VarEnv} {args : List Arg} (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "idiv_" args (optUNV (idiv_ t.width s x y)) := by
  by_cases hy : y = 0
  · subst hy
    exact Equiv.callDef_idiv_zero (numEnv_simEnv B) hρ ha
  · cases s with
    | unsigned => exact callDef_idiv_u hB x y hy hρ ha
    | signed => exact callDef_idiv_s hB (by cases t <;> decide) x y hy hρ ha

/-- `$irem_` at any divisor. -/
theorem callDef_irem (hB : IntB B) (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {ρ : VarEnv} {args : List Arg} (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs (simEnv B) ρ args
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)]) :
    CallDef (simEnv B) ρ "irem_" args (optUNV (irem_ t.width s x y)) := by
  by_cases hy : y = 0
  · subst hy
    exact Equiv.callDef_irem_zero (numEnv_simEnv B) hρ ha
  · cases s with
    | unsigned => exact callDef_irem_u hB x y hy hρ ha
    | signed => exact callDef_irem_s hB x y hy hρ ha

/-- The list a lifted `iN(N)?` becomes. -/
theorem optUNV_toList {N : Nat} (o : Option (BitVec N)) :
    (o.map bvV).toList = o.toList.map bvV := by
  cases o <;> rfl

set_option maxRecDepth 100000 in
/-- `div_sx`, through `$idiv_`. -/
theorem applies_binop_div (hB : IntB B) (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "binop_"
      [.val (ntV t), .val (ibinopV (.div s)), .val (bvV x), .val (bvV y)]
      (.list ((idiv_ t.width s x y).toList.map bvV)) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  rw [← optUNV_toList]
  exact tryClauses_hit matchArgs_sx2 premsHold_nil
    (evalExp_liftCall (callDef_idiv hB t s x y rfl (evalArgs_prim2s t s x y)))

set_option maxRecDepth 100000 in
/-- `rem_sx`, through `$irem_`. -/
theorem applies_binop_rem (hB : IntB B) (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "binop_"
      [.val (ntV t), .val (ibinopV (.rem s)), .val (bvV x), .val (bvV y)]
      (.list ((irem_ t.width s x y).toList.map bvV)) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  rw [← optUNV_toList]
  exact tryClauses_hit matchArgs_sx2 premsHold_nil
    (evalExp_liftCall (callDef_irem hB t s x y rfl (evalArgs_prim2s t s x y)))

/-- **`$binop_` at an integer type is `IntegerN.ibinop_`**, as a list (empty on a trap). -/
theorem applies_binop_int (hB : IntB B) (t : Silmaril.Wasm.IntType)
    (op : Silmaril.Wasm.IntBinOp) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV op), .val (bvV x), .val (bvV y)]
      (.list ((ibinop_ t.width op x y).toList.map bvV)) := by
  cases op with
  | add => exact applies_binop_add t x y
  | sub => exact applies_binop_sub t x y
  | mul => exact applies_binop_mul t x y
  | div s => exact applies_binop_div hB t s x y
  | rem s => exact applies_binop_rem hB t s x y
  | «and» => exact applies_binop_and hB t x y
  | «or» => exact applies_binop_or hB t x y
  | xor => exact applies_binop_xor hB t x y
  | shl => exact applies_binop_shl hB t x y
  | shr s => exact applies_binop_shr hB t s x y
  | rotl => exact applies_binop_rotl hB t x y
  | rotr => exact applies_binop_rotr hB t x y

/-- **`$unop_` at an integer type is `IntegerN.iunop_`**, for every operator valid at `t`. -/
theorem applies_unop_int (hB : IntB B) (t : Silmaril.Wasm.IntType)
    (op : Silmaril.Wasm.IntUnOp) (hv : op.valid t = true) (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV op), .val (bvV x)]
      (.list [bvV (iunop_ t.width op x)]) := by
  cases op with
  | clz => exact applies_unop_clz hB t x
  | ctz => exact applies_unop_ctz hB t x
  | popcnt => exact applies_unop_popcnt hB t x
  | extend p =>
      exact applies_unop_extend t p (by simpa [Silmaril.Wasm.IntUnOp.valid] using hv) x

/-- **`$testop_` at an integer type is `IntegerN.itestop_`**. -/
theorem applies_testop_int (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntTestOp)
    (x : BitVec t.width) :
    Applies (simEnv B) "testop_" [.val (ntV t), .val (itestopV op), .val (bvV x)]
      (bvV (itestop_ t.width op x)) := by
  cases op
  exact applies_testop_eqz t x

/-- **`$relop_` at an integer type is `IntegerN.irelop_`**. -/
theorem applies_relop_int (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntRelOp)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_" [.val (ntV t), .val (irelopV op), .val (bvV x), .val (bvV y)]
      (bvV (irelop_ t.width op x y)) := by
  cases op with
  | eq => exact applies_relop_eq t x y
  | ne => exact applies_relop_ne t x y
  | lt s => exact applies_relop_lt t s x y
  | gt s => exact applies_relop_gt t s x y
  | le s => exact applies_relop_le t s x y
  | ge s => exact applies_relop_ge t s x y

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
