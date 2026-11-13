module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLane
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkA
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkC
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixLkD

/-!
# The vector errata: the quantifier types of `vextract_lane-num` in `simEnv20V B`

The 2.0 typing proofs  (`Pure.hasTyp_iN20`, `Pure.hasTyp_num_int20`,
`Whole.hasTyp_vec20`, `Whole.typedV_N20`, with `Pure.callDef_size20` and `Pure.callDef_sizenn20`)
read their environment only through the lookups of `VecFixLk{A,B,C,D}`, which are the same in
`simEnv20V B`. They are restated here at `simEnv20V B`:

* `callDef_size20V`, `callDef_sizenn20V`: `$size` and `$sizenn` at every number type;
* `hasTyp_iN_of_uN20V`, **`hasTyp_vec20V`**: `vec_(V128)` holds every 128-bit pattern;
* **`hasTyp_num_int20V`**: `num_(Inn)` holds every bit pattern of the width;
* `typedV_N20V`: `N` holds every natural.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `$size`, `$sizenn` -/

/-- `$size` at every number type. -/
theorem callDef_size20V (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none) (ha : EvalArgs (simEnv20V B) ρ args [.val (numTypeV t)]) :
    CallDef (simEnv20V B) ρ "size" args (natV t.width) := by
  refine callDef_of_tryClauses hρ findDef_size20V ha ?_
  rcases t with (_ | _) | (_ | _) <;>
  · repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) ?_)
    exact tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
      premsHold_nil evalExp_num

/-- `$size(V128) = 128`. -/
theorem callDef_sizeV128_20V {ρ : VarEnv} {args : List Arg} (hρ : ρ.findDef? "size" = none)
    (ha : EvalArgs (simEnv20V B) ρ args [.val (caseNilV "V128")]) :
    CallDef (simEnv20V B) ρ "size" args (natV 128) := by
  refine callDef_of_tryClauses hρ findDef_size20V ha ?_
  repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
    (matchExp_caseE_undef (by decide)))) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil (evalExp_numE_iff.2 rfl)

/-- `$sizenn(nt)` is the width. -/
theorem callDef_sizenn20V (t : Silmaril.Wasm.NumType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "sizenn" = none) (ha : EvalArgs (simEnv20V B) ρ args [.val (numTypeV t)]) :
    CallDef (simEnv20V B) ρ "sizenn" args (natV t.width) := by
  refine callDef_of_tryClauses hρ findDef_sizenn20V ha ?_
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" (numTypeV t))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_size20V t rfl
      (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp)))
        Equiv.evalArgs_nil)))

/-! ## `iN`, `vec_`, `num_`, `N` -/

/-- `iN(N)` is `uN(N)`. -/
theorem hasTyp_iN_of_uN20V {ρ : VarEnv} {e : Exp} {N n : Nat}
    (he : EvalExp (simEnv20V B) ρ e (natV N)) (hn : n < 2 ^ N) :
    HasTyp (simEnv20V B) ρ (.varT "iN" [.expA e]) (pctV n) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_iN20V (B := B)
  obtain ⟨ps', qs', htd'⟩ := findTyp_uN20V (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (hasTyp_uN_of htd' (Sim.evalExp_var (by simp)) hn)))

/-- **`vec_(V128)` holds every 128-bit pattern** in `simEnv20V B`. -/
theorem hasTyp_vec20V {ρ : VarEnv} {e : Exp} (b : BitVec 128)
    (he : EvalExp (simEnv20V B) ρ e (caseNilV "V128")) :
    HasTyp (simEnv20V B) ρ (.varT "vec_" [.expA e]) (pctV b.toNat) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_vec20V (B := B)
  obtain ⟨ps', qs', htd'⟩ := findTyp_vN20V (B := B)
  have hsz : EvalExp (simEnv20V B) (VarEnv.empty.bindVal "Vnn" (caseNilV "V128"))
      (.callE "size" [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])
      (natV 128) :=
    evalExp_callE_iff.2 (callDef_sizeV128_20V rfl (Equiv.evalArgs_cons
      (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp))) Equiv.evalArgs_nil))
  have hvN : HasTyp (simEnv20V B) (VarEnv.empty.bindVal "Vnn" (caseNilV "V128"))
      (.varT "vN" [.expA (.callE "size"
        [.expA (.subE (.varE "Vnn") (.varT "Vnn" []) (.varT "valtype" []))])])
      (pctV b.toNat) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd' (Equiv.evalArgs_cons hsz Equiv.evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (hasTyp_iN_of_uN20V (Sim.evalExp_var (by simp)) b.isLt)))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hvN))

/-- `vec_(V128)`, with the argument written as the rules write it. -/
theorem typedV_vecV128_20V (b : BitVec 128) :
    TypedV (simEnv20V B) (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV b.toNat) :=
  fun _ _ => hasTyp_vec20V b (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩,
    rfl⟩)

/-- `iN($sizenn(Inn))` holds every bit pattern of the width. -/
theorem hasTyp_iN20V (t : Silmaril.Wasm.IntType) (b : BitVec t.width) :
    HasTyp (simEnv20V B) (VarEnv.empty.bindVal "Inn" (numTypeV (.int t)))
      (.varT "iN" [.expA (.callE "sizenn" [.expA Pure.innPat20])]) (bvV b) :=
  hasTyp_iN_of_uN20V (evalExp_callE_iff.2 (callDef_sizenn20V (.int t) rfl
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp))) Equiv.evalArgs_nil)))
    b.isLt

/-- **`num_(Inn)` holds every bit pattern of the width** in `simEnv20V B`. -/
theorem hasTyp_num_int20V {ρ : VarEnv} {e : Exp} {t : Silmaril.Wasm.IntType} (b : BitVec t.width)
    (he : EvalExp (simEnv20V B) ρ e (numTypeV (.int t))) :
    HasTyp (simEnv20V B) ρ (.varT "num_" [.expA e]) (bvV b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_num20V (B := B)
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (Pure.matchArg_subVar20 (by simp) (argSubOk_inn_int20V _))
      matchArgs_nil) (hasTypDef_aliasT_iff.2 (hasTyp_iN20V t b)))

/-- `N` holds every natural. -/
theorem typedV_N20V (k : Nat) : TypedV (simEnv20V B) (.varT "N" []) (.num (.natN k)) :=
  Whole.typedV_aliasG findTyp_N20V (Whole.hasTyp_nat _ _ k)

end Silmaril.Wasm.SpecTec.Sim20.VecFix
