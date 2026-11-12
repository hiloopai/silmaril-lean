module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.Default
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms

/-!
# Track `fwd-simd-agg`: `$default_($unpack(zt))` on images of closed storage types

`struct.new_default` and `array.new_default` (`Step_read` rules 69, 72) read the default value of
each field through `$default_($unpack(zt)) = ?(val)`. Since the typing track's fix (`Sem.argSubOk`)
both definitions are evaluated clause by clause:

* `$unpack(zt)`: the first clause `$unpack(valtype <: storagetype) = valtype` admits exactly the
  images of unpacked storage types (`Aggregates.argSubOk_valtypePat`);
* `$default_(t)`: the five clauses at the image of a **closed** value type (`tyV t`), which is
  the image of the source type for numeric and vector types and `REF NULL? ht` for reference
  types; `Integrate.applies_default_*` did the source types, `applies_default_closed` lifts it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Integrate (applies_default_of vkPat skip_vk match_refNull)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- No kind pattern of `$default_` admits the image of a reference type. -/
theorem argSubOk_vk_refC (X : IL.Id) (hX : X = "Inn" ∨ X = "Fnn" ∨ X = "Vnn") (w : Value) :
    argSubOk (simEnv B) VarEnv.empty (vkPat X) (.case "REF" w) = false := by
  rw [argSubOk, Aggregates.subCaseOk_case]
  rcases hX with rfl | rfl | rfl <;> rfl

/-- `$default_(REF NULL ht) = REF.NULL_ADDR`, at any heap-type value `ht`. -/
theorem applies_default_refNull (hv : Value) :
    Applies (simEnv B) "default_" [.val (.case "REF" (.tuple [.opt (some (.case "NULL" (.tuple []))),
      hv]))] (.opt (some (.case "REF.NULL_ADDR" (.tuple [])))) :=
  applies_default_of (skip_vk (argSubOk_vk_refC "Inn" (.inl rfl) _)
    (skip_vk (argSubOk_vk_refC "Fnn" (.inr (.inl rfl)) _)
      (skip_vk (argSubOk_vk_refC "Vnn" (.inr (.inr rfl)) _)
        (tryClauses_hit (matchArgs_cons (matchArg_expA (match_refNull _)) matchArgs_nil)
          premsHold_nil (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2
            ⟨[], evalExps_nil, rfl⟩), rfl⟩)))))

/-- **`$default_(t)` at the image of a closed value type** with a default `v` is `?(v)`. -/
theorem applies_default_closed : ∀ (t : CValType) {v : Val}, defaultVal? t = some v →
    Applies (simEnv B) "default_" [.val (tyV t)] (.opt (some (valV v)))
  | .num (.int t), v, h => by
    obtain rfl : Val.num ⟨.int t, 0⟩ = v := Option.some.inj h
    cases t
    · exact Integrate.applies_default_int .i32
    · exact Integrate.applies_default_int .i64
  | .num (.float t), v, h => by
    obtain rfl : Val.num ⟨.float t, 0⟩ = v := Option.some.inj h
    cases t
    · exact Integrate.applies_default_float .f32
    · exact Integrate.applies_default_float .f64
  | .vec t, v, h => by
    obtain rfl : Val.vec 0 = v := Option.some.inj h
    cases t
    exact Integrate.applies_default_vec .v128
  | .refv (.ref true hv), v, h => by
    obtain rfl : Val.ref .null = v := Option.some.inj h
    exact applies_default_refNull _
  | .refv (.ref false _), _, h => nomatch h
  | .botv, _, h => nomatch h

set_option maxRecDepth 100000 in
/-- The two clauses of `$unpack`. -/
theorem findDef_unpack (B : Builtins) :
    ∃ ps t rest, (simEnv B).findDef? "unpack" = some (ps, t,
      .defD [.expP "valtype" (.varT "valtype" [])] [.expA Aggregates.valtypePat]
        (.varE "valtype") [] :: rest) := ⟨_, _, _, rfl⟩

/-- **`$unpack(zt) = t`** at the image of an unpacked storage type `zt = t`. -/
theorem applies_unpack_val (t : CValType) :
    Applies (simEnv B) "unpack" [.val (tyV (Ty.val t : CStorageType))] (tyV t) := by
  obtain ⟨ps, ty, rest, hd⟩ := findDef_unpack B
  exact ⟨ps, ty, _, hd, Or.inl (tryClauses_hit
    (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
      (Aggregates.argSubOk_valtypePat B rfl t)) matchArgs_nil) premsHold_nil
    (evalExp_var (by simp; rfl)))⟩

/-- `$default_($unpack(zt)) = ?(val)`, in any term scope binding `zt` and `val`. -/
theorem evalExp_defaultUnpack {ρ : VarEnv} (hρ : ValsOnly ρ) {t : CValType} {v : Val}
    (hz : ρ.findVal? "zt" = some (tyV (Ty.val t : CStorageType)))
    (hv : ρ.findVal? "val" = some (valV v)) (hdef : defaultVal? t = some v) :
    EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.callE "default_" [.expA (.callE "unpack" [.expA (.varE "zt")])])
      (.optE (some (.varE "val")))) (.bool true) :=
  RefsGC.evalExp_eq_true
    (Vec.evalExp_call (Aggregates.findDef_none hρ _)
      (Equiv.evalArgs_cons (Vec.evalExp_call (Aggregates.findDef_none hρ _)
        (Vec.evalArgs_var hz Equiv.evalArgs_nil) (applies_unpack_val t)) Equiv.evalArgs_nil)
      (applies_default_closed t hdef))
    (evalExp_optE_some_iff.2 ⟨_, evalExp_var hv, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
