module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Eval

/-!
# Aggregates: reading fields (`struct.get-struct`, `array.get-array`), forward

`Step_read` rules 71 and 79 read a field of an aggregate through `$unpackfield_`. For an unpacked
storage type (`zt = valtype`, `sx? = ε`, field `val`), the first clause of `$unpackfield_`
returns the value; this file evaluates it (`unpackDef_simEnv`, by computation) and so proves both
rules forward for unpacked fields, under `AggTypes` (`Expand` on images, typing of the encoded
storage types and mutability flags).

**Packed fields are not covered.** For a packed storage type the second clause applies, which
calls `$extend__(psize(pt), 32, sx, i)`; that needs the numeric primitive `$extend__` at widths 8
and 16 (family N's `B`), not yet stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC

/-- The first clause of `$unpackfield_`: `$unpackfield_(valtype, ε, val) = val`. -/
abbrev unpackPats : List Arg :=
  [.expA (.subE (.varE "valtype") (.varT "valtype" []) (.varT "storagetype" [])),
   .expA (.optE none), .expA (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" []))]

/-! ### The subtype tests of `SubE` argument patterns

Since the typing track's fix to the ported evaluator (`Sem.argSubOk`), a top-level `SubE`
argument pattern only matches a value among its subtype's cases. The images of unpacked storage
types and of values pass the tests of `$unpackfield_`'s and `$packfield_`'s first clauses. -/

/-- `subCaseOk` reads only the head of a case value. -/
theorem subCaseOk_case (env : Env) (ρ : VarEnv) (t : IL.Typ) (op : IL.MixopS) (w : Value) :
    subCaseOk env ρ t (.case op w) = subCaseOk env ρ t (.case op (.tuple [])) := by
  cases t with
  | varT x xs => cases xs <;> rfl
  | _ => rfl

/-- `subCaseOk` depends on the scope only through its type variables. -/
theorem subCaseOk_typs_nil {env : Env} {ρ : VarEnv} (hρ : ρ.typs = []) (t : IL.Typ) (v : Value) :
    subCaseOk env ρ t v = subCaseOk env VarEnv.empty t v := by
  cases t with
  | varT x xs =>
    cases xs with
    | nil => cases v <;> simp [subCaseOk, VarEnv.findTyp?, VarEnv.empty, hρ]
    | cons => rfl
  | _ => rfl

/-- The pattern `valtype <: storagetype`. -/
abbrev valtypePat : Exp := .subE (.varE "valtype") (.varT "valtype" []) (.varT "storagetype" [])

/-- The pattern `val <: fieldval`. -/
abbrev valPat : Exp := .subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])

set_option maxRecDepth 100000 in
/-- The image of an unpacked storage type passes `valtype`'s subtype test. -/
theorem argSubOk_valtypePat (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) (t : CValType) :
    argSubOk (simEnv B) ρ valtypePat (tyV (Ty.val t : CStorageType)) = true := by
  simp only [argSubOk]
  rw [subCaseOk_typs_nil hρ]
  cases t with
  | num t => rcases t with t | t <;> cases t <;> rfl
  | vec t => cases t; rfl
  | refv r => cases r; rfl
  | botv => rfl

set_option maxRecDepth 100000 in
theorem subCaseOk_val_extern (B : Builtins) :
    subCaseOk (simEnv B) VarEnv.empty (.varT "val" []) (.case "REF.EXTERN" (.tuple [])) = true :=
  rfl

set_option maxRecDepth 100000 in
/-- The image of a value passes `val`'s subtype test. -/
theorem argSubOk_valPat (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) (v : Val) :
    argSubOk (simEnv B) ρ valPat (valV v) = true := by
  simp only [argSubOk]
  rw [subCaseOk_typs_nil hρ]
  cases v with
  | num n => simp only [valV]; rw [subCaseOk_case]; rfl
  | vec b => rfl
  | ref r =>
    cases r with
    | extern r =>
      rw [show valV (.ref (.extern r)) = .case "REF.EXTERN"
          (Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue r) from rfl, subCaseOk_case]
      exact subCaseOk_val_extern B
    | _ => simp only [valV, Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue]; rw [subCaseOk_case]; rfl

/-- `$unpackfield_`'s first clause, with the rest of its clauses, and the subtype tests of its
patterns on images (unpacked storage types, values). -/
def UnpackDef (env : Env) : Prop :=
  (∃ ps t q rest, env.findDef? "unpackfield_" = some (ps, t, .defD q unpackPats (.varE "val") [] :: rest)) ∧
  (∀ ρ : VarEnv, ρ.typs = [] → ∀ t : CValType,
    argSubOk env ρ valtypePat (tyV (Ty.val t : CStorageType)) = true) ∧
  (∀ ρ : VarEnv, ρ.typs = [] → ∀ v : Val, argSubOk env ρ valPat (valV v) = true)

set_option maxRecDepth 100000 in
theorem unpackDef_baseEnv : ∃ ps t q rest, baseEnv.findDef? "unpackfield_" =
    some (ps, t, .defD q unpackPats (.varE "val") [] :: rest) := ⟨_, _, _, _, rfl⟩

theorem unpackDef_simEnv (B : Builtins) : UnpackDef (simEnv B) := by
  obtain ⟨ps, t, q, rest, h⟩ := unpackDef_baseEnv
  exact ⟨⟨ps, t, q, rest, by rw [simEnv, Env.findDef?_withBuiltins, h]⟩,
    fun _ hρ => argSubOk_valtypePat B hρ, fun _ hρ => argSubOk_valPat B hρ⟩

/-- A subsumption pattern matches as its body (the evaluator does not test the subtype). -/
theorem matchExp_subE {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : MatchExp env ρ e v ρ') : MatchExp env ρ (.subE e t₁ t₂) v ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simpa [matchExp] using h⟩

/-- `ε` matches `ε`. -/
theorem matchExp_optNone {env : Env} {ρ : VarEnv} : MatchExp env ρ (.optE none) (.opt none) ρ :=
  ⟨1, by simp [matchExp, Res.assert]⟩

/-- `$unpackfield_(zt, ε, val) = val`, for an unpacked storage type `zt` and a value `val`. -/
theorem evalExp_unpackfield {env : Env} (U : UnpackDef env) {ρ : VarEnv} (hρ : ρ.findDef? "unpackfield_" = none)
    {e₁ e₂ e₃ : Exp} {t : CValType} {v : Val} (h₁ : EvalExp env ρ e₁ (tyV (Ty.val t : CStorageType)))
    (h₂ : EvalExp env ρ e₂ (.opt none)) (h₃ : EvalExp env ρ e₃ (valV v)) :
    EvalExp env ρ (.callE "unpackfield_" [.expA e₁, .expA e₂, .expA e₃]) (valV v) := by
  obtain ⟨⟨ps, t', q, rest, hd⟩, hzt, hv⟩ := U
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd
    (evalArgs_cons h₁ (evalArgs_cons h₂ (evalArgs_cons h₃ evalArgs_nil)))
    (tryClauses_hit (ρ₀ := ((VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))).bindVal
        "val" (valV v)))
      (matchArgs_cons (matchArg_expA (matchExp_subE (matchExp_varE rfl)) (hzt _ rfl t))
        (matchArgs_cons (matchArg_expA matchExp_optNone)
          (matchArgs_cons (matchArg_expA (matchExp_subE (matchExp_varE rfl)) (hv _ rfl v))
            matchArgs_nil)))
      premsHold_nil (evalExp_var rfl)))

variable {env : Env} {H : Type} {hn : H → String}

/-- The fields of `$arrayinst(z)[a]` (in a term-variable scope). -/
theorem evalExp_arrayFieldsAt (D : AggDefs env) {ρ : VarEnv} (hvo : ValsOnly ρ) {s : Store H}
    {f : Frame} {a : Nat} {ai : ArrayInst} (hz : EvalExp env ρ (.varE "z") (stateV hn s f))
    (ha : EvalExp env ρ (.varE "a") (.num (.natN a))) (hai : s.arrays[a]? = some ai) :
    EvalExp env ρ (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
      (.list (ai.fields.map fieldValV)) :=
  evalExp_dot (evalExp_idx (v := arrayInstV ai) (evalExp_arrayinst D (findDef_none hvo _) hz) ha
    (by simp [hai])) rfl

/-- The fields of `$structinst(z)[a]` (in a term-variable scope). -/
theorem evalExp_structFieldsAt (D : AggDefs env) {ρ : VarEnv} (hvo : ValsOnly ρ) {s : Store H}
    {f : Frame} {a : Nat} {si : StructInst} (hz : EvalExp env ρ (.varE "z") (stateV hn s f))
    (ha : EvalExp env ρ (.varE "a") (.num (.natN a))) (hsi : s.structs[a]? = some si) :
    EvalExp env ρ (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
      (.list (si.fields.map fieldValV)) :=
  evalExp_dot (evalExp_idx (v := structInstV si) (evalExp_structinst D (findDef_none hvo _) hz) ha
    (by simp [hsi])) rfl

/-- `i!%.0`. -/
theorem evalExp_unpctVar {ρ : VarEnv} {x : IL.Id} {n : Nat}
    (h : EvalExp env ρ (.varE x) (pctV n)) :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) (.num (.natN n)) :=
  evalExp_unpct h

/-- **`array.get-array` (rule 79), forward, for an unpacked field.** -/
theorem sread_arrayGetArrayVal (h₀ : HasRuleAt env "Step_read" "%~>%" 79 arrayGetArrayRule)
    (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env) (A : AggTypes env)
    (U : UnpackDef env) {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {a : Nat}
    {ai : ArrayInst} {v : Val} {d : DefType} {m : Mutability} {t : CValType}
    (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some (.val v))
    (hd : f.type? x = some d) (he : Expand d (.array (.field m (.val t))))
    (hz : TypedV env stateT (stateV hn s f)) :
    SRead env (configV hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet none x)]⟩)
      (adminsToV [v.toAdmin]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("sx?", .opt none), ("x", Encode.toValue x),
    ("zt", tyV (Ty.val t : CStorageType)), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hfv : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) (valV v) :=
    evalExp_idx (evalExp_arrayFieldsAt D hρ (by eval_tac) (by eval_tac) ha)
      (evalExp_unpct (by eval_tac)) (by simp [hf, fieldValV])
  have hun : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "unpackfield_" [.expA (.varE "zt"),
        .expA (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])),
        .expA (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
          (.projE (.uncaseE (.varE "i") "%") 0))]) (valV v) :=
    evalExp_unpackfield U (findDef_none hρ _) (by eval_tac) (by eval_tac) hfv
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (by eval_tac) (by eval_tac)
  have hex : EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  refine dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.sxOpt none _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_sub_of ?_)))
    (prems_one (.rulePr evalArgs_nil hex (A.expand _ _ he)))
  rw [adminToV_toAdmin]
  exact hun

end Silmaril.Wasm.SpecTec.Sim.Aggregates
