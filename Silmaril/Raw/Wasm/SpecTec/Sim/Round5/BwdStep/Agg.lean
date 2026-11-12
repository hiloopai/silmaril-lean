module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Store
public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Thms

/-!
# Round 5: `array.set-array`, backward (`Step` 35)

`z; (REF.ARRAY_ADDR a) (CONST I32 i) val (ARRAY.SET x) ~> $with_array(z, a, i, $packfield_(zt, val))`
with the premise `$type(z, x) ~~ ARRAY (mut? zt)`. Read back:

* `type_inv`: `$type(z, x)` evaluates only at a type the frame's module lists (`f.type? x`);
* the `Expand` premise picks Core's expansion (`R4Fwd.ExpandInv`, proved for `Prims.builtins`),
  so `zt` is the image of the array's storage type (`R4Fwd.zt_of_expand`);
* `packfield_inv`: `$packfield_(zt, val)` evaluates only on Core's domain `packable zt v`, to the
  image of `packField zt v` (the second clause's pattern `CONST I32 i` fails definitely on every
  other value, and `B` does not answer `$packfield_`);
* `withArray_inv`: `$with_array(z, a, i, fv)` evaluates only when array `a` exists and `i` is
  below its length (the record update's `setIdx`).

So Core's `arraySetArray` fires and its successor's image is the rule's (forward evaluation and
`EvalExp.unique`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef TryClausesUndef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (fires_step codes_four payload_of_caseE head_of_caseE rhs_nil body_pair
  const32_of_lhs val_of_var head_arraySet head_refArray idx_of_var')
open Round4Int (BI)
open Round4Read (ReadValid)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Arguments, inverted -/

/-- An argument list with an expression head, inverted. -/
theorem evalArgs_cons_inv {env : Env} {ρ : VarEnv} {e : Exp} {rest : List Arg} {ws : List ArgV}
    (h : EvalArgs env ρ (.expA e :: rest) ws) :
    ∃ v ws', EvalExp env ρ e v ∧ EvalArgs env ρ rest ws' ∧ ws = .val v :: ws' := by
  obtain ⟨n, h⟩ := h
  match n, h with
  | 0, h => simp [evalArgs] at h
  | 1, h => simp [evalArgs, List.mapM_cons, evalArg] at h
  | n + 2, h =>
      simp only [evalArgs, List.mapM_cons, evalArg] at h
      cases hv : evalExp n env ρ e with
      | error err => simp [hv, Functor.map, Except.map, bind, Except.bind] at h
      | ok v =>
          cases hws : List.mapM (evalArg (n + 1) env ρ) rest with
          | error err => simp [hv, hws, Functor.map, Except.map, bind, Except.bind] at h
          | ok ws' =>
              simp [hv, hws, Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at h
              exact ⟨v, ws', ⟨n, hv⟩, ⟨n + 2, by simpa [evalArgs] using hws⟩, h.symm⟩

/-- The arguments of a call that evaluates, evaluated. -/
theorem args_of_call {env : Env} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {v : Value}
    (h : EvalExp env ρ (.callE x args) v) : ∃ ws, EvalArgs env ρ args ws := by
  obtain ⟨ws, -, -, -, ha, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  exact ⟨ws, ha⟩

/-! ## `B` answers none of the aggregate definitions -/

theorem call_type_none (ws : List ArgV) : (BI P hn host).call "type" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

theorem call_withArray_none (ws : List ArgV) : (BI P hn host).call "with_array" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

theorem call_withStruct_none (ws : List ArgV) : (BI P hn host).call "with_struct" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

theorem call_packfield_none (ws : List ArgV) : (BI P hn host).call "packfield_" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-! ## `$type(z, x)`, inverted -/

/-- **`$type(z, x)`, read back**: the module lists `x`, and the value is the image of its type. -/
theorem type_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {x : TypeIdx}
    {T : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (Encode.toValue x))
    (h : EvalExp (simEnv (BI P hn host)) ρ (.callE "type" [.expA (.varE "z"), .expA (.varE "x")])
      T) :
    ∃ d, f.type? x = some d ∧ T = CT.defType d := by
  have D := Aggregates.aggDefs_simEnv (BI P hn host)
  have SD := State.stateDefs_simEnv (BI P hn host)
  have hbody := BwdPureStep.evalExp_call1_inv D.type_ (Prims.findDef_none_of_valsOnly hρ _)
    (call_type_none _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fx)
      Equiv.evalArgs_nil)) State.matchArgs_zxPat h
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hbody
  have eL : L = .list (f.module.types.map CT.defType) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof SD rfl (evalExp_var rfl), Aggregates.frameV_module f⟩,
      Aggregates.moduleV_types f.module⟩)
  have ej : Value.num (.natN j) = .num (.natN x.toNat) :=
    EvalExp.unique hj (State.evalExp_idxPayload rfl)
  simp only [Value.num.injEq, Num.natN.injEq] at ej
  subst eL ej
  simp only [Value.idx?, List.getElem?_map] at hLj
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hLj
  exact ⟨d, hd, rfl⟩

/-! ## `$packfield_`, inverted -/

/-- A two-component tuple pattern fails definitely when its first component does. -/
theorem matchExp_tupE_two_undef {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : MatchExpUndef env ρ e₁ v₁) : MatchExpUndef env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂]) := by
  obtain ⟨n, h⟩ := h
  refine ⟨n + 3, ?_⟩
  simp only [matchExp, Res.ofOption, Value.asTuple?, Bind.bind, Except.bind, matchExps,
    matchExp_undef_of_le (show n ≤ n + 1 by omega) h]

/-- The pattern `CONST I32 i` fails definitely on the image of every value but an `i32`. -/
theorem constI32Pat_undef {env : Env} {ρ : VarEnv} {v : Val}
    (hv : ∀ b, v ≠ .num ⟨.int .i32, b⟩) :
    MatchExpUndef env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"])) (valV v) := by
  rcases v with ⟨t, b⟩ | b | r
  · rcases t with t | t
    · cases t
      · exact absurd rfl (hv b)
      · show MatchExpUndef _ _ _ (.case "CONST" (.tuple [.case "I64" (.tuple []), _]))
        exact matchExp_caseE_undef' (matchExp_tupE_two_undef (matchExp_caseE_undef (by decide)))
    · cases t
      · show MatchExpUndef _ _ _ (.case "CONST" (.tuple [.case "F32" (.tuple []), _]))
        exact matchExp_caseE_undef' (matchExp_tupE_two_undef (matchExp_caseE_undef (by decide)))
      · show MatchExpUndef _ _ _ (.case "CONST" (.tuple [.case "F64" (.tuple []), _]))
        exact matchExp_caseE_undef' (matchExp_tupE_two_undef (matchExp_caseE_undef (by decide)))
  · show MatchExpUndef _ _ _ (.case "VCONST" _)
    exact matchExp_caseE_undef (by decide)
  · cases r <;> exact matchExp_caseE_undef (by decide)

/-- **`$packfield_` is undefined off Core's domain**: at a packed storage type and a value that is
not an `i32`, no clause applies and `B` does not answer. -/
theorem not_applies_packfield {p : PackType} {v : Val} (hp : packable (.pack p) v = false)
    {u : Value} :
    ¬ Applies (simEnv (BI P hn host)) "packfield_" [.val (tyV (Ty.pack p : CStorageType)),
      .val (valV v)] u := by
  rintro ⟨ps, t, cs, hd, hc⟩
  obtain ⟨ps', t', q, hd'⟩ := R4Fwd.findDef_packfield (BI P hn host)
  rw [hd'] at hd
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd
  have hv : ∀ b, v ≠ .num ⟨.int .i32, b⟩ := by
    rintro b rfl
    simp [packable] at hp
  have hu : TryClausesUndef (simEnv (BI P hn host))
      [.defD q Aggregates.packPats (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])) [],
        R4Fwd.packClause₂] [.val (tyV (Ty.pack p : CStorageType)), .val (valV v)] :=
    IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (R4Fwd.argSubOk_valtypePat_pack p rfl)))
      (IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (Prims.matchExp_subE (matchExp_varE rfl))
          (R4Fwd.argSubOk_packtypePat_pack p rfl))
        (matchArgs_cons_undef (matchArg_expA_undef (constI32Pat_undef hv))))
        IntNumeric.tryClausesUndef_nil)
  rcases hc with hc | ⟨-, hb⟩
  · exact Equiv.ExecNumeric.not_tryClauses_and_undef hc hu
  · rw [simEnv, Env.builtins_withBuiltins, call_packfield_none] at hb
    cases hb

/-- **`$packfield_(zt, val)`, read back**: `val` is in Core's domain and the value is the image
of `packField`. -/
theorem packfield_inv (zt : CStorageType) (v : Val) {u : Value}
    (h : Applies (simEnv (BI P hn host)) "packfield_" [.val (tyV zt), .val (valV v)] u) :
    packable zt v = true ∧ u = fieldValV (packField zt v) := by
  by_cases hp : packable zt v = true
  · exact ⟨hp, Applies.unique h (R4Fwd.applies_packfield (Prims.floatB_builtins hn host) zt v hp)⟩
  · rcases zt with t | p
    · simp [packable] at hp
    · exact absurd h (not_applies_packfield (Bool.of_not_eq_true hp))

/-! ## `$with_array`, inverted -/

/-- **A `$with_array(z, a, i, fv)` call that evaluates writes inside an existing array.** -/
theorem withArray_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {A I : Nat}
    {ei eF : Exp} {F W : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN A)))
    (hi : EvalExp (simEnv (BI P hn host)) ρ ei (.num (.natN I)))
    (hF : EvalExp (simEnv (BI P hn host)) ρ eF F)
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.callE "with_array" [.expA (.varE "z"), .expA (.varE "a"), .expA ei, .expA eF]) W) :
    ∃ ai, s.arrays[A]? = some ai ∧ I < ai.fields.length := by
  have D := Aggregates.aggDefs_simEnv (BI P hn host)
  have SD := State.stateDefs_simEnv (BI P hn host)
  have hbody := BwdPureStep.evalExp_call1_inv D.withArray (Prims.findDef_none_of_valsOnly hρ _)
    (call_withArray_none _)
    (Equiv.evalArgs_cons (evalExp_var fz) (Equiv.evalArgs_cons (evalExp_var fa)
      (Equiv.evalArgs_cons hi (Equiv.evalArgs_cons hF Equiv.evalArgs_nil))))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))) h
  obtain ⟨W₁, W₂, h₁, -, -⟩ := body_pair hbody
  obtain ⟨S, Fv, hS, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S = storeV hn s := EvalExp.unique hS (State.evalExp_sof SD rfl (evalExp_var rfl))
  subst eS
  obtain ⟨u, iv, i, u', hu, hiv, hi', hset, -⟩ := BwdPureStep.pathSet_idx_inv hps
  have eiv : iv = .num (.natN I) := EvalExp.unique hiv (evalExp_var rfl)
  subst eiv
  simp only [Value.asNat?, Option.some.injEq] at hi'
  subst hi'
  obtain ⟨u₀, hu₀, hFl⟩ := BwdPureStep.pathGet_dot_inv hu
  obtain ⟨L, iv₂, a', hL, hiv₂, ha', hLa⟩ := BwdPureStep.pathGet_idx_inv hu₀
  obtain ⟨R, hR, hRf⟩ := BwdPureStep.pathGet_dot_inv hL
  have eR := BwdPureStep.pathGet_root_inv hR
  subst eR
  have hS' : (storeV hn s).field? "ARRAYS" = some (.list (s.arrays.map arrayInstV)) := rfl
  rw [hS', Option.some.injEq] at hRf
  subst hRf
  have eiv₂ : iv₂ = .num (.natN A) := EvalExp.unique hiv₂ (evalExp_var rfl)
  subst eiv₂
  simp only [Value.asNat?, Option.some.injEq] at ha'
  subst ha'
  simp only [Value.idx?, List.getElem?_map] at hLa
  obtain ⟨ai, hai, rfl⟩ := Option.map_eq_some_iff.1 hLa
  have hFl' : (arrayInstV ai).field? "FIELDS" = some (.list (ai.fields.map fieldValV)) := rfl
  rw [hFl', Option.some.injEq] at hFl
  subst hFl
  refine ⟨ai, hai, ?_⟩
  simp only [Value.setIdx, List.length_map] at hset
  by_contra hc
  simp [hc] at hset

/-- The composite type an `Expand` image of the `ARRAY` shape names is an array type. -/
theorem array_of_tyV {ct : CCompType} {e : Exp} {env : Env} {ρ : VarEnv}
    (h : EvalExp env ρ (.caseE "ARRAY" e) (tyV ct)) :
    ∃ m zt, ct = .array (.field m zt) := by
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 h
  match ct, hu with
  | .array (.field m zt), _ => exact ⟨m, zt, rfl⟩
  | .struct _, hu => exact absurd (Value.case.inj hu).1 (by decide)
  | .func _ _, hu => exact absurd (Value.case.inj hu).1 (by decide)

/-- **`Step/array.set-array` (35) backward**, at the concrete `B`. -/
theorem bwd_arraySetArray {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 35 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).arraySetArray hf
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes_four hes
  obtain ⟨n, rfl⟩ := head_refArray (head_of_caseE h₁)
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN n)) := idx_of_var' h₁ rfl
  obtain ⟨i, rfl, hi⟩ := const32_of_lhs h₂
  obtain ⟨v, rfl, fval⟩ := val_of_var hq (.tail _ (.tail _ (.tail _ (.head _)))) h₃
  obtain ⟨x, rfl⟩ := head_arraySet (head_of_caseE h₄)
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x) := idx_of_var' h₄ rfl
  have hρ := valsOnly_bindVals σ
  -- the premise `$type(z, x) ~~ ARRAY (mut? zt)`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨v₁, vs', h₁', hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨d, hd, rfl⟩ := type_inv hρ fz fx h₁'
  obtain ⟨v₂, vs'', h₂', hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨m, zt, rfl⟩ := array_of_tyV h₂'
  have fzt := evalExp_varE_iff.1 (R4Fwd.zt_of_expand (R4Fwd.expandInv_builtins hn host) hρ hd hct
    (evalExp_var fz) (evalExp_var fx) hwe hD)
  -- the right-hand side
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  obtain ⟨ws, hws⟩ := args_of_call hW
  obtain ⟨-, ws₁, -, hws₁, rfl⟩ := evalArgs_cons_inv hws
  obtain ⟨-, ws₂, -, hws₂, rfl⟩ := evalArgs_cons_inv hws₁
  obtain ⟨-, ws₃, -, hws₃, rfl⟩ := evalArgs_cons_inv hws₂
  obtain ⟨F, ws₄, hF, -, rfl⟩ := evalArgs_cons_inv hws₃
  obtain ⟨hpk, rfl⟩ := packfield_inv zt v ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons (evalExp_var fzt)
      (Equiv.evalArgs_cons (evalExp_var fval) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 hF))
  obtain ⟨ai, hai, hlt⟩ := withArray_inv hρ fz fa (RefsGC.evalExp_unpct hi) hF hW
  have ew := Aggregates.evalExp_withArray (Aggregates.aggDefs_simEnv _) (State.stateDefs_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) hai hlt (evalExp_var fz) (evalExp_var fa)
    (RefsGC.evalExp_unpct hi) hF
  refine ⟨⟨s.setArrayField n i.toNat (packField zt v), f, []⟩, ?_,
    .aggregate (.arraySetArray hai hlt hd hct hpk)⟩
  rw [EvalExp.unique hW ew]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
