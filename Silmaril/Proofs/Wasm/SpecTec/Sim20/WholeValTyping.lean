module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestStoreTrap

/-!
# Every V2 value is an IL `val` of the wasm-2.0 script

The wasm-2.0 `val` (`Scripts.Wasm20.Original.d282`) has five cases:
`CONST numtype num_(numtype)`, `VCONST vectype vec_(vectype)`, `REF.NULL reftype`,
`REF.FUNC_ADDR funcaddr` and `REF.HOST_ADDR hostaddr`. The image of every V2 value is typed, with
no hypothesis on the builtins:

* numbers: `numtype` by `typedV_numtype20`, the dependent `num_(numtype)` by
  `NumTyped.num` of `numTyped_simEnv20` (integers and every float shape);
* vectors: `vec_(V128) = vN($size(V128)) = iN(128) = uN(128)` (`hasTyp_vec20`);
* references: the payload types of `val`'s reference cases are `ref`'s (`typedV_val_ref20`).

`typedV_val20 : ∀ v, TypedV (simEnv20 B) valT (valV v)` is what the earlier tracks took as a
hypothesis (`State.localSet_iff`, `State.globalSet_iff`, `Pure.drop_fires`, the `select` and
concatenation rules). It is the converse of `Pure.valHead_of_typed`. Ported from round 5's
`Sim.Typing.typedV_val` (3.0).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (instCases findCase hasTypCase_of_findCase)


attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## The vector types -/

theorem findTyp_vectype20 : (simEnv20 B).findTyp? "vectype" = some ([], [.instD [] []
    (.variantT [.mk "V128" (.tupT []) [] []])]) := rfl

theorem findTyp_vec20 : ∃ ps qs, (simEnv20 B).findTyp? "vec_" = some (ps, [.instD qs
    [.expA (.varE "Vnn")] (.aliasT (.varT "vN" [.expA (.callE "size"
      [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])]))]) :=
  ⟨_, _, rfl⟩

theorem findTyp_vN20 : ∃ ps qs, (simEnv20 B).findTyp? "vN" = some (ps, [.instD qs
    [.expA (.varE "N")] (.aliasT (.varT "iN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

/-- `$size(V128) = 128`, at any argument evaluating to `V128`. -/
theorem callDef_sizeV128_20 {ρ : VarEnv} {args : List Arg} (hρ : ρ.findDef? "size" = none)
    (ha : EvalArgs (simEnv20 B) ρ args [.val (caseNilV "V128")]) :
    CallDef (simEnv20 B) ρ "size" args (natV 128) := by
  refine callDef_of_tryClauses hρ (Pure.findDef_size20 B) ha ?_
  repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
    (matchExp_caseE_undef (by decide)))) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil (evalExp_numE_iff.2 rfl)

/-- `iN(N)` is `uN(N)`. -/
theorem hasTyp_iN_of_uN20 {ρ : VarEnv} {e : Exp} {N n : Nat}
    (he : EvalExp (simEnv20 B) ρ e (natV N)) (hn : n < 2 ^ N) :
    HasTyp (simEnv20 B) ρ (.varT "iN" [.expA e]) (pctV n) := by
  obtain ⟨ps, qs, htd⟩ := Pure.findTyp_iN20 (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (Pure.hasTyp_uN20 (evalExp_var (by simp)) hn)))

/-- **`vec_(V128)` holds every 128-bit pattern**: `vec_(V128) = vN($size(V128)) = iN(128)`. -/
theorem hasTyp_vec20 {ρ : VarEnv} {e : Exp} (b : BitVec 128)
    (he : EvalExp (simEnv20 B) ρ e (caseNilV "V128")) :
    HasTyp (simEnv20 B) ρ (.varT "vec_" [.expA e]) (pctV b.toNat) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_vec20 (B := B)
  obtain ⟨ps', qs', htd'⟩ := findTyp_vN20 (B := B)
  have hsz : EvalExp (simEnv20 B) (VarEnv.empty.bindVal "Vnn" (caseNilV "V128"))
      (.callE "size" [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])
      (natV 128) :=
    evalExp_callE_iff.2 (callDef_sizeV128_20 rfl (Equiv.evalArgs_cons
      (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp))) Equiv.evalArgs_nil))
  have hvN : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "Vnn" (caseNilV "V128"))
      (.varT "vN" [.expA (.callE "size"
        [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])])
      (pctV b.toNat) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd' (Equiv.evalArgs_cons hsz Equiv.evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (hasTyp_iN_of_uN20 (evalExp_var (by simp)) b.isLt)))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hvN))

/-- Every 128-bit pattern is a `vec_(V128)`, with the argument written as the rules write it. -/
theorem typedV_vecV128_20 (b : BitVec 128) :
    TypedV (simEnv20 B) (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV b.toNat) :=
  fun _ _ => hasTyp_vec20 b (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩,
    rfl⟩)

/-! ## `val` -/

/-- A case of `val` whose payload is typed. -/
theorem typedV_valCase20 {op : MixopS} {t : Typ} {w : Value}
    (hf : findCase (instCases Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d282 0) op =
      some (t, []))
    (hw : HasTyp (simEnv20 B) VarEnv.empty t w) : TypedV (simEnv20 B) Pure.valT (.case op w) :=
  Pure.typedV_closedCase20 Pure.findTyp_val20 hf hw

/-- **Every number is a typed `val`**, integers and every float shape. -/
theorem typedV_val_num20 (n : NumVal) : TypedV (simEnv20 B) Pure.valT (valV (.num n)) := by
  obtain ⟨t, x⟩ := n
  have hnt : HasTyp (simEnv20 B) VarEnv.empty (.varT "numtype" []) (numTypeV t) :=
    Pure.typedV_numtype20 B t _ ⟨rfl, rfl, rfl⟩
  have hn : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "numtype" (numTypeV t))
      (.varT "num_" [.expA (.varE "numtype")]) (numV ⟨t, x⟩) :=
    (Pure.numTyped_simEnv20 B).num t x "numtype" _ ⟨rfl, rfl, rfl⟩ (by simp)
  exact typedV_valCase20 rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hnt,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hn, hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-- **Every vector is a typed `val`.** -/
theorem typedV_val_vec20 (b : BitVec 128) : TypedV (simEnv20 B) Pure.valT (valV (.vec b)) := by
  have hvt : HasTyp (simEnv20 B) VarEnv.empty (.varT "vectype" []) (caseNilV "V128") :=
    Pure.typedV_closedCase20 findTyp_vectype20 rfl hasTyp_tupT_nil _ ⟨rfl, rfl, rfl⟩
  have hv : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "vectype" (caseNilV "V128"))
      (.varT "vec_" [.expA (.varE "vectype")]) (pctV b.toNat) :=
    hasTyp_vec20 b (evalExp_var (by simp))
  exact typedV_valCase20 rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hvt,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hv, hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-- **Every reference is a typed `val`**: `val`'s reference cases are `ref`'s. -/
theorem typedV_val_ref20 (r : Ref) : TypedV (simEnv20 B) Pure.valT (valV (.ref r)) := by
  cases r with
  | null t => exact typedV_valCase20 rfl (typedV_refType20 t _ ⟨rfl, rfl, rfl⟩)
  | funcAddr a =>
    exact typedV_valCase20 rfl
      (typedV_aliasG findTyp_funcaddr20 (typedV_addr20 a _ ⟨rfl, rfl, rfl⟩) _ ⟨rfl, rfl, rfl⟩)
  | hostAddr a =>
    exact typedV_valCase20 rfl
      (typedV_aliasG findTyp_hostaddr20 (typedV_addr20 a _ ⟨rfl, rfl, rfl⟩) _ ⟨rfl, rfl, rfl⟩)

/-- **Every V2 value is an IL `val` of the wasm-2.0 script**, at every builtins. -/
theorem typedV_val20 : ∀ v : Val, TypedV (simEnv20 B) Pure.valT (valV v)
  | .num n => typedV_val_num20 n
  | .vec b => typedV_val_vec20 b
  | .ref r => typedV_val_ref20 r

/-- Every V2 value sequence is a `val*`. -/
theorem typedV_vals20 (vs : List Val) :
    TypedV (simEnv20 B) (.iterT Pure.valT .list) (.list (vs.map valV)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_val20 v

end Silmaril.Wasm.SpecTec.Sim20.Whole
