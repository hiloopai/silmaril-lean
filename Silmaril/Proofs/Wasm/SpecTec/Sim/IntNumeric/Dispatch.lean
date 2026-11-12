module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Calls

/-!
# Integer numerics: the four dispatchers, opcode by opcode
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV NumEnv)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

theorem intCall_iand (N : Nat) (x y : BitVec N) :
    intCall "iand_" [.val (natV N), .val (bvV x), .val (bvV y)] = some (bvV (iand_ N x y)) := by
  simp [intCall, natV]

theorem intCall_ishl (N : Nat) (x y : BitVec N) :
    intCall "ishl_" [.val (natV N), .val (bvV x), .val (bvV y)] =
      some (bvV (ishl_ N x y.toNat)) := by
  simp [intCall, natV, shiftBits, asPctNat?_bvV]

theorem intCall_ishr (N : Nat) (s : Silmaril.Wasm.Signedness) (x y : BitVec N) :
    intCall "ishr_" [.val (natV N), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] =
      some (bvV (ishr_ N s x y.toNat)) := by
  cases s <;> simp [intCall, natV, shiftBits, asPctNat?_bvV, asSx?, Equiv.sxV]

theorem intCall_ior (N : Nat) (x y : BitVec N) :
    intCall "ior_" [.val (natV N), .val (bvV x), .val (bvV y)] = some (bvV (ior_ N x y)) := by
  simp [intCall, natV]

theorem intCall_ixor (N : Nat) (x y : BitVec N) :
    intCall "ixor_" [.val (natV N), .val (bvV x), .val (bvV y)] = some (bvV (ixor_ N x y)) := by
  simp [intCall, natV]

theorem intCall_irotl (N : Nat) (x y : BitVec N) :
    intCall "irotl_" [.val (natV N), .val (bvV x), .val (bvV y)] = some (bvV (irotl_ N x y)) := by
  simp [intCall, natV]

theorem intCall_irotr (N : Nat) (x y : BitVec N) :
    intCall "irotr_" [.val (natV N), .val (bvV x), .val (bvV y)] = some (bvV (irotr_ N x y)) := by
  simp [intCall, natV]

theorem intCall_iclz (N : Nat) (x : BitVec N) :
    intCall "iclz_" [.val (natV N), .val (bvV x)] = some (bvV (iclz_ N x)) := by
  simp [intCall, natV]

theorem intCall_ictz (N : Nat) (x : BitVec N) :
    intCall "ictz_" [.val (natV N), .val (bvV x)] = some (bvV (ictz_ N x)) := by
  simp [intCall, natV]

theorem intCall_ipopcnt (N : Nat) (x : BitVec N) :
    intCall "ipopcnt_" [.val (natV N), .val (bvV x)] = some (bvV (ipopcnt_ N x)) := by
  simp [intCall, natV]

/-- The shift count `%(i_2!%.0)`: the second operand re-read as a `u32`. -/
theorem evalExp_shiftCount {ρ : VarEnv} {N : Nat} {y : BitVec N}
    (h : ρ.findVal? "i_2" = some (bvV y)) :
    EvalExp (simEnv B) ρ (.caseE "%" (.tupE [.projE (.uncaseE (.varE "i_2") "%") 0])) (bvV y) :=
  Equiv.evalExp_case_tup_one (Equiv.evalExp_uNV_payload h)

/-- The arguments of `$ishl_`. -/
theorem evalArgs_shl (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv B) (scope2 (ntV t) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "i_2") "%") 0]))]
      [.val (natV t.width), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scope2]))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2]))
      (Equiv.evalArgs_cons (evalExp_shiftCount (by simp [scope2])) Equiv.evalArgs_nil))

/-- The arguments of `$ishr_`. -/
theorem evalArgs_shr (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) {t₁ t₂ : Typ} :
    EvalArgs (simEnv B) (scope2s (ntV t) (Equiv.sxV s) (bvV x) (bvV y))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") t₁ t₂)]), .expA (.varE "sx"),
        .expA (.varE "i_1"), .expA (.caseE "%" (.tupE [.projE (.uncaseE (.varE "i_2") "%") 0]))]
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)] :=
  Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scope2s]))
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s]))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scope2s]))
        (Equiv.evalArgs_cons (evalExp_shiftCount (by simp [scope2s])) Equiv.evalArgs_nil)))

/-! ## `$binop_` -/

set_option maxRecDepth 100000 in
/-- `add`. -/
theorem applies_binop_add (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .add), .val (bvV x), .val (bvV y)]
      (.list [bvV (iadd_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (Equiv.callDef_iadd (numEnv_simEnv B) rfl (evalArgs_prim2 t x y)))

set_option maxRecDepth 100000 in
/-- `sub`. -/
theorem applies_binop_sub (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .sub), .val (bvV x), .val (bvV y)]
      (.list [bvV (isub_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (Equiv.callDef_isub (numEnv_simEnv B) rfl (evalArgs_prim2 t x y)))

set_option maxRecDepth 100000 in
/-- `mul`. -/
theorem applies_binop_mul (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .mul), .val (bvV x), .val (bvV y)]
      (.list [bvV (imul_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (Equiv.callDef_imul (numEnv_simEnv B) rfl (evalArgs_prim2 t x y)))

set_option maxRecDepth 100000 in
/-- `and`, a primitive of `B`. -/
theorem applies_binop_and (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .and), .val (bvV x), .val (bvV y)]
      (.list [bvV (iand_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_iand B) rfl
      (evalArgs_prim2 t x y) (intCall_iand _ x y)))

set_option maxRecDepth 100000 in
/-- `or`, a primitive of `B`. -/
theorem applies_binop_or (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .or), .val (bvV x), .val (bvV y)]
      (.list [bvV (ior_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ior B) rfl
      (evalArgs_prim2 t x y) (intCall_ior _ x y)))

set_option maxRecDepth 100000 in
/-- `xor`, a primitive of `B`. -/
theorem applies_binop_xor (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .xor), .val (bvV x), .val (bvV y)]
      (.list [bvV (ixor_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ixor B) rfl
      (evalArgs_prim2 t x y) (intCall_ixor _ x y)))

set_option maxRecDepth 100000 in
/-- `rotl`, a primitive of `B`. -/
theorem applies_binop_rotl (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .rotl), .val (bvV x), .val (bvV y)]
      (.list [bvV (irotl_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_irotl B) rfl
      (evalArgs_prim2 t x y) (intCall_irotl _ x y)))

set_option maxRecDepth 100000 in
/-- `rotr`, a primitive of `B`. -/
theorem applies_binop_rotr (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .rotr), .val (bvV x), .val (bvV y)]
      (.list [bvV (irotr_ t.width x y)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_irotr B) rfl
      (evalArgs_prim2 t x y) (intCall_irotr _ x y)))

set_option maxRecDepth 100000 in
/-- `shl`, a primitive of `B`; the shift count is the `u32` reading of the second operand. -/
theorem applies_binop_shl (hB : IntB B) (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "binop_" [.val (ntV t), .val (ibinopV .shl), .val (bvV x), .val (bvV y)]
      (.list [bvV (ishl_ t.width x y.toNat)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ishl B) rfl
      (evalArgs_shl t x y) (intCall_ishl _ x y)))

set_option maxRecDepth 100000 in
/-- `shr_sx`, a primitive of `B`. -/
theorem applies_binop_shr (hB : IntB B) (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "binop_"
      [.val (ntV t), .val (ibinopV (.shr s)), .val (bvV x), .val (bvV y)]
      (.list [bvV (ishr_ t.width s x y.toNat)]) := by
  refine ⟨_, _, _, findDef_binop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_sx2 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ishr B) rfl
      (evalArgs_shr t s x y) (intCall_ishr _ s x y)))

/-! ## `$unop_` -/

set_option maxRecDepth 100000 in
/-- `clz`, a primitive of `B`. -/
theorem applies_unop_clz (hB : IntB B) (t : Silmaril.Wasm.IntType) (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV .clz), .val (bvV x)]
      (.list [bvV (iclz_ t.width x)]) := by
  refine ⟨_, _, _, findDef_unop B, Or.inl ?_⟩
  exact tryClauses_hit matchArgs_nullary1 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_iclz B) rfl (evalArgs_prim1 t x) (intCall_iclz _ x)))

set_option maxRecDepth 100000 in
/-- `ctz`, a primitive of `B`. -/
theorem applies_unop_ctz (hB : IntB B) (t : Silmaril.Wasm.IntType) (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV .ctz), .val (bvV x)]
      (.list [bvV (ictz_ t.width x)]) := by
  refine ⟨_, _, _, findDef_unop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary1 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ictz B) rfl (evalArgs_prim1 t x) (intCall_ictz _ x)))

set_option maxRecDepth 100000 in
/-- `popcnt`, a primitive of `B`. -/
theorem applies_unop_popcnt (hB : IntB B) (t : Silmaril.Wasm.IntType) (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV .popcnt), .val (bvV x)]
      (.list [bvV (ipopcnt_ t.width x)]) := by
  refine ⟨_, _, _, findDef_unop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary1 premsHold_nil (evalExp_list1Call
    (callDef_prim hB (noClauses_ipopcnt B) rfl (evalArgs_prim1 t x) (intCall_ipopcnt _ x)))

/-- The scope the `EXTEND` clause binds (`Inn`, `N'`, `i`). -/
def scopeExt (nt k c : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Inn" nt).bindVal "N'" k).bindVal "i" c

set_option maxRecDepth 100000 in
/-- `extendN_s`, through the script's own `$iextend_`. -/
theorem applies_unop_extend (t : Silmaril.Wasm.IntType) (p : Silmaril.Wasm.PackSize)
    (hp : p.width < t.width) (x : BitVec t.width) :
    Applies (simEnv B) "unop_" [.val (ntV t), .val (iunopV (.extend p)), .val (bvV x)]
      (.list [bvV (iextend_ t.width p.width .signed x)]) := by
  refine ⟨_, _, _, findDef_unop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])),
        .expA (.caseE "EXTEND" (.tupE [.caseE "%" (.tupE [.varE "N'"])])), .expA (.varE "i")]
      [.val (ntV t), .val (iunopV (.extend p)), .val (bvV x)]
      (scopeExt (ntV t) (natV p.width) (bvV x)) :=
    matchArgs_cons (matchArg_InnPat (by simp) (argSubOk_innPat_ntV _))
      (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE_one (matchExp_caseE
        (matchExp_tupE_one (matchExp_varE (by simp)))))))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))
  have ha : EvalArgs (simEnv B) (scopeExt (ntV t) (natV p.width) (bvV x))
      [.expA (.callE "sizenn" [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []))]),
        .expA (.varE "N'"), .expA (.caseE "S" (.tupE [])), .expA (.varE "i")]
      [.val (natV t.width), .val (natV p.width), .val (Equiv.sxV .signed), .val (bvV x)] :=
    Equiv.evalArgs_cons (evalExp_sizennInn t rfl (by simp [scopeExt]))
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scopeExt]))
        (Equiv.evalArgs_cons (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩,
          rfl⟩)
          (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp [scopeExt])) Equiv.evalArgs_nil)))
  have hK : 0 < p.width := by cases p <;> decide
  exact tryClauses_hit hm premsHold_nil (evalExp_list1Call
    (Equiv.callDef_iextend (numEnv_simEnv B) rfl ha hK hp.le))

/-! ## `$testop_` and `$relop_` -/

set_option maxRecDepth 100000 in
/-- `eqz`. -/
theorem applies_testop_eqz (t : Silmaril.Wasm.IntType) (x : BitVec t.width) :
    Applies (simEnv B) "testop_" [.val (ntV t), .val (itestopV .eqz), .val (bvV x)]
      (bvV (ieqz_ t.width x)) := by
  refine ⟨_, _, _, findDef_testop B, Or.inl ?_⟩
  exact tryClauses_hit matchArgs_nullary1 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ieqz (numEnv_simEnv B) rfl (evalArgs_prim1 t x)))

set_option maxRecDepth 100000 in
/-- `eq`. -/
theorem applies_relop_eq (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "relop_" [.val (ntV t), .val (irelopV .eq), .val (bvV x), .val (bvV y)]
      (bvV (ieq_ t.width x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ieq (numEnv_simEnv B) rfl (evalArgs_prim2 t x y)))

set_option maxRecDepth 100000 in
/-- `ne`. -/
theorem applies_relop_ne (t : Silmaril.Wasm.IntType) (x y : BitVec t.width) :
    Applies (simEnv B) "relop_" [.val (ntV t), .val (irelopV .ne), .val (bvV x), .val (bvV y)]
      (bvV (ine_ t.width x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_nullary2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ine (numEnv_simEnv B) rfl (evalArgs_prim2 t x y)))

set_option maxRecDepth 100000 in
/-- `lt_sx`. -/
theorem applies_relop_lt (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_"
      [.val (ntV t), .val (irelopV (.lt s)), .val (bvV x), .val (bvV y)]
      (bvV (ilt_ t.width s x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_sx2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ilt (numEnv_simEnv B) rfl (evalArgs_prim2s t s x y) (by cases t <;> decide)))

set_option maxRecDepth 100000 in
/-- `gt_sx`. -/
theorem applies_relop_gt (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_"
      [.val (ntV t), .val (irelopV (.gt s)), .val (bvV x), .val (bvV y)]
      (bvV (igt_ t.width s x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_sx2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_igt (numEnv_simEnv B) rfl (evalArgs_prim2s t s x y) (by cases t <;> decide)))

set_option maxRecDepth 100000 in
/-- `le_sx`. -/
theorem applies_relop_le (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_"
      [.val (ntV t), .val (irelopV (.le s)), .val (bvV x), .val (bvV y)]
      (bvV (ile_ t.width s x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_sx2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ile (numEnv_simEnv B) rfl (evalArgs_prim2s t s x y) (by cases t <;> decide)))

set_option maxRecDepth 100000 in
/-- `ge_sx`. -/
theorem applies_relop_ge (t : Silmaril.Wasm.IntType) (s : Silmaril.Wasm.Signedness)
    (x y : BitVec t.width) :
    Applies (simEnv B) "relop_"
      [.val (ntV t), .val (irelopV (.ge s)), .val (bvV x), .val (bvV y)]
      (bvV (ige_ t.width s x y)) := by
  refine ⟨_, _, _, findDef_relop B, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  refine tryClauses_skip_match (skipOp (by decide)) ?_
  exact tryClauses_hit matchArgs_sx2 premsHold_nil (evalExp_callE_iff.2
    (Equiv.callDef_ige (numEnv_simEnv B) rfl (evalArgs_prim2s t s x y) (by cases t <;> decide)))

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
