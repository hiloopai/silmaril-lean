module

public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Defs
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# Track `fwd-simd-agg`: evaluating the bitwise vector dispatchers

The evaluation half of `Bitwise.lean` (split for elaboration time).

# Track `fwd-simd-agg`: the bitwise vector instructions, forward, at every `B` with `VVB`

`v128.not`, `v128.and`, `v128.andnot`, `v128.or`, `v128.xor`, `v128.bitselect` and
`v128.any_true` (Core's `VectorStep.vecUnOp`, `vecBinOp`, `vecTernOp`, `vecTestOp`) go through the
`Step_pure` rules 54–57. Family V proved them forward under the `VecTyping`/`VecAgree`
interfaces; here the fields those four rules use are **evaluated** instead:

* `$vvunop_`, `$vvbinop_`, `$vvternop_` (`Original.d531`–`d533`): the clause for the opcode is
  reached (the others fail on their opcode), `$vsizenn(V128) = 128` (`Typing.callDef_vsizenn`),
  and the primitive is answered by `B`: `$iand_`, `$ior_`, `$ixor_` by family N's `intCall`
  (`IntB`), `$inot_`, `$iandnot_`, `$ibitselect_` by `vvCall` (`VVB`);
* `$vsize(V128) = 128` and `$inez_` by its clause (`Equiv.callDef_inez`);
* the typing of the operator values `NOT`, `AND`, … as `vvunop`, `vvbinop`, `vvternop` (closed
  nullary variants), and of `vec_(V128)`/`num_(I32)` (typing track).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d531 Original.d532 Original.d533 Original.d443
  Original.d446 Original.d453)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The script's definitions -/

set_option maxRecDepth 100000 in
theorem findDef_vvunop (B : Builtins) :
    (simEnv B).findDef? "vvunop_" = IntNumeric.defOf Original.d531 := rfl
set_option maxRecDepth 100000 in
theorem findDef_vvbinop (B : Builtins) :
    (simEnv B).findDef? "vvbinop_" = IntNumeric.defOf Original.d532 := rfl
set_option maxRecDepth 100000 in
theorem findDef_vvternop (B : Builtins) :
    (simEnv B).findDef? "vvternop_" = IntNumeric.defOf Original.d533 := rfl
set_option maxRecDepth 100000 in
theorem findDef_inot (B : Builtins) : ∃ ps t, (simEnv B).findDef? "inot_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_iandnot (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "iandnot_" = some (ps, t, []) := ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_ibitselect (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "ibitselect_" = some (ps, t, []) := ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_iand (B : Builtins) : ∃ ps t, (simEnv B).findDef? "iand_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_ior (B : Builtins) : ∃ ps t, (simEnv B).findDef? "ior_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_ixor (B : Builtins) : ∃ ps t, (simEnv B).findDef? "ixor_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- A 128-bit pattern is the `bvV` encoding. -/
theorem vecV_eq_bvV (a : V128) : Vec.vecV a = bvV a := rfl

/-! ## Calls of the primitives -/

/-- A primitive without clauses, answered by `B`. -/
theorem callDef_prim {x : IL.Id} (hd : ∃ ps t, (simEnv B).findDef? x = some (ps, t, []))
    {ρ : VarEnv} {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv B) ρ args ws) (hb : B.call x ws = some v) :
    CallDef (simEnv B) ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hd
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha hb

/-- The argument list `$vsizenn(Vnn), v_1, …` of a bitwise clause, in its clause scope. -/
theorem evalArgs_vsizenn {ρ : VarEnv} (hd : ρ.findDef? "vsizenn" = none)
    (hV : ρ.findVal? "Vnn" = some Vec.vecTypeV) {xs : List IL.Id} {vs : List Value}
    (hxs : EvalArgs (simEnv B) ρ (xs.map fun x => .expA (.varE x)) (vs.map .val)) :
    EvalArgs (simEnv B) ρ (.expA (.callE "vsizenn" [.expA (.varE "Vnn")]) ::
      xs.map fun x => .expA (.varE x)) (.val (natV 128) :: vs.map .val) :=
  Equiv.evalArgs_cons (evalExp_callE_iff.2 (Typing.callDef_vsizenn hd
    (Vec.evalArgs_var hV Equiv.evalArgs_nil))) hxs

/-! ## The dispatchers -/

/-- The scope of a one-operand bitwise clause. -/
abbrev scope1 (a : Value) : VarEnv :=
  (VarEnv.empty.bindVal "Vnn" Vec.vecTypeV).bindVal "v" a

/-- The scope of a two-operand bitwise clause. -/
abbrev scope2 (a b : Value) : VarEnv :=
  ((VarEnv.empty.bindVal "Vnn" Vec.vecTypeV).bindVal "v_1" a).bindVal "v_2" b

/-- The scope of a three-operand bitwise clause. -/
abbrev scope3 (a b c : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "Vnn" Vec.vecTypeV).bindVal "v_1" a).bindVal "v_2" b).bindVal "v_3" c

/-- The two-operand clause patterns `Vnn, OP, v_1, v_2` match at `V128`, `OP`. -/
theorem matchArgs2 {o : MixopS} (a b : Value) :
    MatchArgs (simEnv B) VarEnv.empty
      [.expA (.varE "Vnn"), .expA (.caseE o (.tupE [])), .expA (.varE "v_1"), .expA (.varE "v_2")]
      [.val Vec.vecTypeV, .val (caseNilV o), .val a, .val b] (scope2 a b) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))

/-- A two-operand clause for another opcode is skipped. -/
theorem skip2 {o o' : MixopS} (h : o ≠ o') (a b : Value) :
    MatchArgsUndef (simEnv B) VarEnv.empty
      [.expA (.varE "Vnn"), .expA (.caseE o' (.tupE [])), .expA (.varE "v_1"), .expA (.varE "v_2")]
      [.val Vec.vecTypeV, .val (caseNilV o), .val a, .val b] :=
  matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef h)))

/-- The two-operand clause for the opcode `o` fires and calls its primitive. -/
theorem hit2 {x : IL.Id} (hd : ∃ ps t, (simEnv B).findDef? x = some (ps, t, [])) {o : MixopS}
    {q : List Param} {cs : List Clause} {a b v : Value}
    (hb : B.call x [.val (natV 128), .val a, .val b] = some v) :
    TryClauses (simEnv B) (.defD q
      [.expA (.varE "Vnn"), .expA (.caseE o (.tupE [])), .expA (.varE "v_1"), .expA (.varE "v_2")]
      (.listE [.callE x [.expA (.callE "vsizenn" [.expA (.varE "Vnn")]), .expA (.varE "v_1"),
        .expA (.varE "v_2")]]) [] :: cs)
      [.val Vec.vecTypeV, .val (caseNilV o), .val a, .val b] (.list [v]) :=
  tryClauses_hit (matchArgs2 a b) premsHold_nil (evalExp_list1 (evalExp_callE_iff.2
    (callDef_prim hd rfl (evalArgs_vsizenn (xs := ["v_1", "v_2"]) (vs := [a, b]) rfl (by simp)
      (Vec.evalArgs_var (by simp) (Vec.evalArgs_var (by simp) Equiv.evalArgs_nil))) hb)))

/-- **`$vvunop_(V128, NOT, v)`** is Core's `vvunop`. -/
theorem applies_vvunop (hV : VVB B) (op : VecUnOp) (a : V128) :
    Applies (simEnv B) "vvunop_" [.val Vec.vecTypeV, .val (Vec.vvunopV op), .val (Vec.vecV a)]
      (.list [Vec.vecV (vvunop op a)]) := by
  cases op
  refine ⟨_, _, _, findDef_vvunop B, Or.inl ?_⟩
  have hb : B.call "inot_" [.val (natV 128), .val (Vec.vecV a)] =
      some (Vec.vecV (vvunop .not a)) :=
    hV _ _ _ (by simp [vvCall, Equiv.ExecBuiltins.unBits, vecV_eq_bvV, vvunop, inot_, natV])
  refine tryClauses_hit (ρ₀ := scope1 (Vec.vecV a))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil))) premsHold_nil ?_
  exact evalExp_list1 (evalExp_callE_iff.2 (callDef_prim (findDef_inot B) rfl
    (evalArgs_vsizenn (xs := ["v"]) (vs := [Vec.vecV a]) rfl (by simp)
      (Vec.evalArgs_var (by simp) Equiv.evalArgs_nil)) hb))

set_option maxRecDepth 100000 in
/-- **`$vvbinop_(V128, op, v_1, v_2)`** is Core's `vvbinop`. -/
theorem applies_vvbinop (hI : IntNumeric.IntB B) (hV : VVB B) (op : VecBinOp) (a b : V128) :
    Applies (simEnv B) "vvbinop_"
      [.val Vec.vecTypeV, .val (Vec.vvbinopV op), .val (Vec.vecV a), .val (Vec.vecV b)]
      (.list [Vec.vecV (vvbinop op a b)]) := by
  refine ⟨_, _, _, findDef_vvbinop B, Or.inl ?_⟩
  cases op
  · exact hit2 (findDef_iand B) (hI _ _ _ (by
      simp [IntNumeric.intCall, Equiv.ExecBuiltins.binBits, vecV_eq_bvV, vvbinop, iand_, natV]))
  · exact tryClauses_skip_match (skip2 (by decide) _ _) (hit2 (findDef_iandnot B) (hV _ _ _ (by
      simp [vvCall, Equiv.ExecBuiltins.binBits, vecV_eq_bvV, vvbinop, iandnot_, VecLane.iandnot,
        natV])))
  · exact tryClauses_skip_match (skip2 (by decide) _ _) (tryClauses_skip_match
      (skip2 (by decide) _ _) (hit2 (findDef_ior B) (hI _ _ _ (by
        simp [IntNumeric.intCall, Equiv.ExecBuiltins.binBits, vecV_eq_bvV, vvbinop, ior_,
          natV]))))
  · exact tryClauses_skip_match (skip2 (by decide) _ _) (tryClauses_skip_match
      (skip2 (by decide) _ _) (tryClauses_skip_match (skip2 (by decide) _ _)
        (hit2 (findDef_ixor B) (hI _ _ _ (by
          simp [IntNumeric.intCall, Equiv.ExecBuiltins.binBits, vecV_eq_bvV, vvbinop, ixor_,
            natV])))))

/-- **`$vvternop_(V128, BITSELECT, v_1, v_2, v_3)`** is Core's `vvternop`. -/
theorem applies_vvternop (hV : VVB B) (op : VecTernOp) (a b c : V128) :
    Applies (simEnv B) "vvternop_" [.val Vec.vecTypeV, .val (Vec.vvternopV op), .val (Vec.vecV a),
      .val (Vec.vecV b), .val (Vec.vecV c)] (.list [Vec.vecV (vvternop op a b c)]) := by
  cases op
  refine ⟨_, _, _, findDef_vvternop B, Or.inl ?_⟩
  have hb : B.call "ibitselect_" [.val (natV 128), .val (Vec.vecV a), .val (Vec.vecV b),
      .val (Vec.vecV c)] = some (Vec.vecV (vvternop .bitselect a b c)) :=
    hV _ _ _ (by simp [vvCall, ternBits, vecV_eq_bvV, vvternop, ibitselect_, VecLane.ibitselect, natV])
  refine tryClauses_hit (ρ₀ := scope3 (Vec.vecV a) (Vec.vecV b) (Vec.vecV c))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
          (matchArgs_cons (matchArg_expA (matchExp_varE (by simp)))
            (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)))))
    premsHold_nil ?_
  exact evalExp_list1 (evalExp_callE_iff.2 (callDef_prim (findDef_ibitselect B) rfl
    (evalArgs_vsizenn (xs := ["v_1", "v_2", "v_3"]) (vs := [Vec.vecV a, Vec.vecV b, Vec.vecV c])
      rfl (by simp) (Vec.evalArgs_var (by simp) (Vec.evalArgs_var (by simp)
        (Vec.evalArgs_var (by simp) Equiv.evalArgs_nil)))) hb))

set_option maxRecDepth 100000 in
/-- `$vsize(V128) = 128`. -/
theorem applies_vsize : Applies (simEnv B) "vsize" [.val Vec.vecTypeV] (natV 128) :=
  ⟨_, _, _, Typing.findDef_vsize, Or.inl (tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil evalExp_num)⟩

/-- `$inez_(128, v)`, the premise of `vvtestop`, is Core's `any_true`. -/
theorem applies_inez (a : V128) :
    Applies (simEnv B) "inez_" [.val (natV 128), .val (Vec.vecV a)]
      (Vec.i32NV (vvtestop .anyTrue a)) := by
  have hc := Equiv.callDef_inez (env := simEnv B) (ρ := VarEnv.empty) (IntNumeric.numEnv_simEnv B)
    rfl (args := [.expA (.numE (.natN 128)), .expA (.caseE "%" (.tupE [.numE (.natN a.toNat)]))])
    (i := a) (Equiv.evalArgs_cons evalExp_num (Equiv.evalArgs_cons
      (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[_], evalExps_cons evalExp_num evalExps_nil, rfl⟩, rfl⟩) Equiv.evalArgs_nil))
  have he : bvV (Silmaril.Wasm.Numerics.inez_ 128 a) = Vec.i32NV (vvtestop .anyTrue a) := by
    simp only [bvV, Vec.i32NV, pctV, natV, vvtestop, Silmaril.Wasm.Numerics.inez_, u32OfBool,
      bool32]
    congr 4
    by_cases h : a = 0
    · subst h; simp [bool_]
    · have h' : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      have h0 : (a = 0#128) = False := propext ⟨h, False.elim⟩
      simp [h', h0, bool_]
  rw [he] at hc
  exact (Equiv.ExecNumeric.applies_iff_callDef rfl (Equiv.evalArgs_cons evalExp_num
    (Equiv.evalArgs_cons (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[_],
      evalExps_cons evalExp_num evalExps_nil, rfl⟩, rfl⟩)
      Equiv.evalArgs_nil))).2 hc

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
