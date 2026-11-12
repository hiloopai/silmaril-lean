module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Read

/-!
# Aggregates: writing fields (`array.set-array`, `struct.set-struct`), forward

`Step` rules 31 and 35 write a field through `$with_struct` / `$with_array` (evaluated by their
clauses: `evalExp_withArray`, `evalExp_withStruct`) of `$packfield_(zt, val)`. For an unpacked
storage type the first clause of `$packfield_` returns the value (`packDef_simEnv`), which is
Core's `packField (.val t) v = .val v`.

**Finding (packed fields).** `$packfield_`'s first clause has the pattern `valtype <: storagetype`,
and the evaluator's `matchExp` of a subsumption pattern does not test the subtype (gap 1 of
`docs/projects/spectec/README.md`: `Sem.matchExp`, `.subE e _ _`). So `$packfield_(I8, CONST I32 i)`
takes the first clause too and returns `CONST I32 i`, not `PACK I8 (wrap i)`: under the current
evaluator SpecTec stores an unpacked `i32` in a packed field, and the forward obligation for
packed fields is false until the IL's subsumption matching is fixed. Only unpacked fields are
proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecStepRules
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open RefsGC

/-- The first clause of `$packfield_`: `$packfield_(valtype, val) = val`. -/
abbrev packPats : List Arg :=
  [.expA (.subE (.varE "valtype") (.varT "valtype" []) (.varT "storagetype" [])),
   .expA (.varE "val")]

/-- `$packfield_`'s first clause, with the rest of its clauses, and the subtype test of its first
pattern on the images of unpacked storage types. -/
def PackDef (env : Env) : Prop :=
  (∃ ps t q rest, env.findDef? "packfield_" = some (ps, t,
    .defD q packPats (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])) [] :: rest)) ∧
  ∀ ρ : VarEnv, ρ.typs = [] → ∀ t : CValType,
    argSubOk env ρ valtypePat (tyV (Ty.val t : CStorageType)) = true

set_option maxRecDepth 100000 in
theorem packDef_baseEnv : ∃ ps t q rest, baseEnv.findDef? "packfield_" = some (ps, t,
    .defD q packPats (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])) [] :: rest) :=
  ⟨_, _, _, _, rfl⟩

theorem packDef_simEnv (B : Builtins) : PackDef (simEnv B) := by
  obtain ⟨ps, t, q, rest, h⟩ := packDef_baseEnv
  exact ⟨⟨ps, t, q, rest, by rw [simEnv, Env.findDef?_withBuiltins, h]⟩,
    fun _ hρ => argSubOk_valtypePat B hρ⟩

/-- `$packfield_(zt, val) = val`, for an unpacked storage type `zt`. -/
theorem evalExp_packfield {env : Env} (P : PackDef env) {ρ : VarEnv}
    (hρ : ρ.findDef? "packfield_" = none) {e₁ e₂ : Exp} {t : CValType} {v : Value}
    (h₁ : EvalExp env ρ e₁ (tyV (Ty.val t : CStorageType))) (h₂ : EvalExp env ρ e₂ v) :
    EvalExp env ρ (.callE "packfield_" [.expA e₁, .expA e₂]) v := by
  obtain ⟨⟨ps, t', q, rest, hd⟩, hzt⟩ := P
  exact evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd
    (evalArgs_cons h₁ (evalArgs_cons h₂ evalArgs_nil))
    (tryClauses_hit (ρ₀ := ((VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))).bindVal
        "val" v))
      (matchArgs_cons (matchArg_expA (matchExp_subE (matchExp_varE rfl)) (hzt _ rfl t))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
      premsHold_nil (evalExp_sub_of (evalExp_var rfl))))

variable {H : Type} {hn : H → String}

/-- Writing a field of an encoded array encodes `Store.setArrayField`. -/
theorem storeV_setArrayField (s : Store H) {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (i : Nat) (fv : FieldVal) :
    (storeV hn s).setField "ARRAYS" (.list ((s.arrays.map arrayInstV).set a
      (arrayInstV { ai with fields := ai.fields.set i fv }))) =
      some (storeV hn (s.setArrayField a i fv)) := by
  simp [storeV, Store.setArrayField, State.List.modify_eq_set_of_getElem? ha, List.map_set]

/-- Writing a field of an encoded struct encodes `Store.setStructField`. -/
theorem storeV_setStructField (s : Store H) {a : Nat} {si : StructInst}
    (hs : s.structs[a]? = some si) (i : Nat) (fv : FieldVal) :
    (storeV hn s).setField "STRUCTS" (.list ((s.structs.map structInstV).set a
      (structInstV { si with fields := si.fields.set i fv }))) =
      some (storeV hn (s.setStructField a i fv)) := by
  simp [storeV, Store.setStructField, State.List.modify_eq_set_of_getElem? hs, List.map_set]

section Eval

variable {env : Env} (D : AggDefs env) (SD : State.StateDefs env) {ρ : VarEnv}
  {ez ea ei ev : Exp}
include D SD

/-- The scope of `$with_struct` / `$with_array`'s clause. -/
abbrev withScope (Z A I V : Value) : VarEnv :=
  (((VarEnv.empty.bindVal "z" Z).bindVal "a" A).bindVal "i" I).bindVal "fv" V

/-- `$with_array(z, a, i, fv)` writes field `i` of array `a`. -/
theorem evalExp_withArray (hρ : ρ.findDef? "with_array" = none) {s : Store H} {f : Frame}
    {a i : Nat} {ai : ArrayInst} {fv : FieldVal} (hai : s.arrays[a]? = some ai)
    (hi : i < ai.fields.length) (hz : EvalExp env ρ ez (stateV hn s f))
    (ha : EvalExp env ρ ea (.num (.natN a))) (hie : EvalExp env ρ ei (.num (.natN i)))
    (hv : EvalExp env ρ ev (fieldValV fv)) :
    EvalExp env ρ (.callE "with_array" [.expA ez, .expA ea, .expA ei, .expA ev])
      (stateV hn (s.setArrayField a i fv) f) := by
  refine State.evalExp_call1 D.withArray hρ
    (evalArgs_cons hz (evalArgs_cons ha (evalArgs_cons hie (evalArgs_cons hv evalArgs_nil))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof SD rfl (evalExp_var rfl)))
  let ρ₁ := withScope (stateV hn s f) (.num (.natN a)) (.num (.natN i)) (fieldValV fv)
  have ha' : a < s.arrays.length := (List.getElem?_eq_some_iff.1 hai).1
  have hS : (storeV hn s).field? "ARRAYS" = some (.list (s.arrays.map arrayInstV)) := rfl
  have hg : PathGet env ρ₁ (storeV hn s) (.idxP (.dotP .rootP "ARRAYS") (.varE "a"))
      (arrayInstV ai) :=
    State.pathGet_idx (State.pathGet_dot State.pathGet_root hS) (evalExp_var rfl) (by simp [hai])
  refine evalExp_updE_iff.2 ⟨storeV hn s, fieldValV fv,
    State.evalExp_sof SD rfl (evalExp_var rfl), evalExp_var rfl, ?_⟩
  have h₁ : (Value.list (ai.fields.map fieldValV)).setIdx i (fieldValV fv) =
      some (.list ((ai.fields.map fieldValV).set i (fieldValV fv))) := by
    simp [Value.setIdx, hi]
  have h₂ : (arrayInstV ai).setField "FIELDS" (.list ((ai.fields.map fieldValV).set i (fieldValV fv))) =
      some (arrayInstV { ai with fields := ai.fields.set i fv }) := by
    simp [arrayInstV, List.map_set]
  have h₃ : (Value.list (s.arrays.map arrayInstV)).setIdx a (arrayInstV { ai with fields := ai.fields.set i fv }) =
      some (.list ((s.arrays.map arrayInstV).set a (arrayInstV { ai with fields := ai.fields.set i fv }))) := by
    simp [Value.setIdx, ha']
  exact State.pathSet_idx (State.pathGet_dot hg rfl) (evalExp_var rfl) h₁
    (State.pathSet_dot hg h₂
      (State.pathSet_idx (State.pathGet_dot State.pathGet_root hS) (evalExp_var rfl) h₃
        (State.pathSet_dot State.pathGet_root (storeV_setArrayField s hai i fv) State.pathSet_root)))

/-- `$with_struct(z, a, i, fv)` writes field `i` of struct `a`. -/
theorem evalExp_withStruct (hρ : ρ.findDef? "with_struct" = none) {s : Store H} {f : Frame}
    {a i : Nat} {si : StructInst} {fv : FieldVal} (hsi : s.structs[a]? = some si)
    (hi : i < si.fields.length) (hz : EvalExp env ρ ez (stateV hn s f))
    (ha : EvalExp env ρ ea (.num (.natN a))) (hie : EvalExp env ρ ei (.num (.natN i)))
    (hv : EvalExp env ρ ev (fieldValV fv)) :
    EvalExp env ρ (.callE "with_struct" [.expA ez, .expA ea, .expA ei, .expA ev])
      (stateV hn (s.setStructField a i fv) f) := by
  refine State.evalExp_call1 D.withStruct hρ
    (evalArgs_cons hz (evalArgs_cons ha (evalArgs_cons hie (evalArgs_cons hv evalArgs_nil))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (State.evalExp_fof SD rfl (evalExp_var rfl)))
  let ρ₁ := withScope (stateV hn s f) (.num (.natN a)) (.num (.natN i)) (fieldValV fv)
  have ha' : a < s.structs.length := (List.getElem?_eq_some_iff.1 hsi).1
  have hS : (storeV hn s).field? "STRUCTS" = some (.list (s.structs.map structInstV)) := rfl
  have hg : PathGet env ρ₁ (storeV hn s) (.idxP (.dotP .rootP "STRUCTS") (.varE "a"))
      (structInstV si) :=
    State.pathGet_idx (State.pathGet_dot State.pathGet_root hS) (evalExp_var rfl) (by simp [hsi])
  refine evalExp_updE_iff.2 ⟨storeV hn s, fieldValV fv,
    State.evalExp_sof SD rfl (evalExp_var rfl), evalExp_var rfl, ?_⟩
  have h₁ : (Value.list (si.fields.map fieldValV)).setIdx i (fieldValV fv) =
      some (.list ((si.fields.map fieldValV).set i (fieldValV fv))) := by
    simp [Value.setIdx, hi]
  have h₂ : (structInstV si).setField "FIELDS" (.list ((si.fields.map fieldValV).set i (fieldValV fv))) =
      some (structInstV { si with fields := si.fields.set i fv }) := by
    simp [structInstV, List.map_set]
  have h₃ : (Value.list (s.structs.map structInstV)).setIdx a (structInstV { si with fields := si.fields.set i fv }) =
      some (.list ((s.structs.map structInstV).set a (structInstV { si with fields := si.fields.set i fv }))) := by
    simp [Value.setIdx, ha']
  exact State.pathSet_idx (State.pathGet_dot hg rfl) (evalExp_var rfl) h₁
    (State.pathSet_dot hg h₂
      (State.pathSet_idx (State.pathGet_dot State.pathGet_root hS) (evalExp_var rfl) h₃
        (State.pathSet_dot State.pathGet_root (storeV_setStructField s hsi i fv) State.pathSet_root)))

end Eval

/-- **`array.set-array` (`Step` rule 35), forward, for an unpacked field.** -/
theorem fwd_arraySetArrayVal {env : Env} (h₀ : HasRuleAt env "Step" "%~>%" 35 arraySetArrayRule)
    (T : TypingFacts env hn) (R : RTyping env) (D : AggDefs env) (SD : State.StateDefs env)
    (A : AggTypes env) (P : PackDef env) {s : Store H} {f : Frame} {x : TypeIdx}
    {i : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst} {d : DefType} {m : Mutability}
    {t : CValType} (ha : s.arrays[a]? = some ai) (h : i.toNat < ai.fields.length)
    (hd : f.type? x = some d) (he : Expand d (.array (.field m (.val t)))) :
    FwdP env hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s.setArrayField a i.toNat (packField (.val t) v), f, []⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("x", Encode.toValue x),
    ("zt", tyV (Ty.val t : CStorageType)), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV env valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hcode)))
  have hpk : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
      (fieldValV (packField (.val t) v)) := by
    have := evalExp_packfield P (findDef_none hρ _) (e₁ := .varE "zt") (e₂ := .varE "val")
      (by eval_tac) (by eval_tac)
    simpa [packField, fieldValV, adminToV_toAdmin] using this
  have hw := evalExp_withArray D SD (findDef_none hρ _) (ez := .varE "z") (ea := .varE "a")
    (ei := .projE (.uncaseE (.varE "i") "%") 0) ha h (by eval_tac) (by eval_tac)
    (evalExp_unpct (by eval_tac)) hpk
  have hty := evalExp_type D SD (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x")
    (by eval_tac) (by eval_tac)
  have hex : EvalExp env (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.val t)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  exact dderives_of_ruleAt h₀ σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_case (evalExp_tup2 hw (by eval_tac))))
    (prems_one (.rulePr evalArgs_nil hex (A.expand _ _ he)))

end Silmaril.Wasm.SpecTec.Sim.Aggregates
