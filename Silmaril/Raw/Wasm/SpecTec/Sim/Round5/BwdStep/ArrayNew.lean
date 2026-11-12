module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Struct

/-!
# Round 5: `array.new_fixed`, backward (`Step` 32)

`z; val^n (ARRAY.NEW_FIXED x (% n)) ~> $add_arrayinst(z, [ai]); (REF.ARRAY_ADDR a)` with the
premises `$type(z, x) ~~ ARRAY (mut? zt)` and
`a = |$arrayinst(z)| ∧ ai = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n}`.

The left-hand side is a concatenation whose first part is the `^n` iteration over `val*`;
`iterListN1_inv` inverts it (the domain is a list of `n` elements, the body holds pointwise), so
the code is `val*`'s images followed by the instruction, and family E's `StructDecode.vals` reads
`val*` back as Core values. The `FIELDS` iteration is inverted the same way and each element read
back by `packfield_inv`, so every value is `packable` and `ai` is the image of Core's new array.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (payload_of_caseE head_of_caseE)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## A `^n` iteration over one variable domain, inverted -/

/-- **A `^n` iteration over one variable domain, inverted**: the domain is a list of the count's
length, as is the output, and the body holds pointwise. -/
theorem iterListN1_inv {env : Env} {ρ : VarEnv} {b : Exp} {x y c : IL.Id} {v : Value}
    (h : EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none) [.mk x (.varE y)])) v) :
    ∃ l out, v = .list out ∧ ρ.findVal? y = some (.list l) ∧
      ρ.findVal? c = some (.num (.natN l.length)) ∧ out.length = l.length ∧
      ∀ k (h₁ : k < l.length) (h₂ : k < out.length),
        EvalExp env (ρ.bindVals [(x, l[k])]) b out[k] := by
  obtain ⟨n, h⟩ := evalExp_iterE_iff.1 h
  match n, h with
  | 0, h => simp [evalIterE] at h
  | 1, h => simp [evalIterE, evalDoms, bind, Except.bind] at h
  | 2, h => simp [evalIterE, evalDoms, bind, Except.bind, Functor.map, Except.map, evalExp] at h
  | n + 3, h =>
      simp only [evalIterE, evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc, evalExp] at h
      simp only [Res.bind_eq_ok, Res.map_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨xvs, ⟨p₁, ⟨V, hy, rfl⟩, xs, hxs, hxvs⟩, kv, hkv, k, hk, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hxvs hxs
      subst hxs hxvs
      simp only [evalIterList, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨ds, hds, hall, vs, hvs, hout⟩ := h
      cases V <;> simp [Value.asList?] at hds
      rename_i l
      subst hds
      simp only [Except.ok.injEq] at hout
      subst hout
      simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at hall
      subst hall
      cases kv <;> simp [Value.asNat?] at hk
      rename_i m
      cases m <;> simp at hk
      subst hk
      simp only [evalRounds] at hvs
      obtain ⟨hlen, hget⟩ := mapM_ok_get hvs
      simp only [iterRows, List.length_map, List.length_range] at hlen
      refine ⟨l, vs, rfl, hy, hkv, hlen, fun k h₁ h₂ => ⟨n, ?_⟩⟩
      have := hget k (by simpa [iterRows] using h₁) h₂
      simpa [iterRows, iterRow, h₁, List.getElem?_eq_getElem] using this

/-! ## Small inversions -/

/-- A conjunction that denotes `true` has both conjuncts `true`. -/
theorem evalExp_and_elim {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.binE .andOp .boolT e₁ e₂) (.bool true)) :
    EvalExp env ρ e₁ (.bool true) ∧ EvalExp env ρ e₂ (.bool true) := by
  obtain ⟨v₁, h₁, hs⟩ := evalExp_binE_iff.mp h
  rcases hs with hs | ⟨-, v₂, h₂, hb⟩
  · cases v₁ <;> simp [boolShort] at hs
    rename_i b
    cases b <;> simp at hs
  · cases v₁ <;> cases v₂ <;> simp_all [binValues, boolBin, Num.bin]

/-- A two-field record, inverted. -/
theorem evalExpFields_two_inv {env : Env} {ρ : VarEnv} {a₁ a₂ : AtomS} {e₁ e₂ : Exp}
    {gs : List (AtomS × Value)} (h : EvalExpFields env ρ [.mk a₁ e₁, .mk a₂ e₂] gs) :
    ∃ v₁ v₂, EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ gs = [(a₁, v₁), (a₂, v₂)] := by
  obtain ⟨n, h⟩ := h
  match n, h with
  | 0, h => simp [evalExpFields] at h
  | n + 1, h =>
      simp only [evalExpFields, List.mapM_cons, List.mapM_nil, Res.bind_eq_ok, Res.map_eq_ok]
        at h
      obtain ⟨g₁, ⟨v₁, h₁, rfl⟩, gs', ⟨g₂, ⟨v₂, h₂, rfl⟩, gs'', hgs'', hgs'⟩, hgs⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hgs'' hgs' hgs
      subst hgs'' hgs' hgs
      exact ⟨v₁, v₂, ⟨n, h₁⟩, ⟨n, h₂⟩, rfl⟩

/-- An image list ending in one element splits the code the same way. -/
theorem adminsToV_eq_snoc {code : List Admin} {l : List Value} {c : Value}
    (h : adminsToV code = l ++ [c]) :
    ∃ A a, code = A ++ [a] ∧ adminsToV A = l ∧ adminToV a = c := by
  rw [adminsToV_eq_map] at h
  obtain ⟨A, B, rfl, hA, hB⟩ := List.map_eq_append_iff.1 h
  obtain ⟨a, rfl, ha⟩ : ∃ a, B = [a] ∧ adminToV a = c := by
    match B, hB with
    | [a], hB => exact ⟨a, rfl, by simpa using hB⟩
  exact ⟨A, a, rfl, by rw [adminsToV_eq_map]; exact hA, ha⟩

theorem head_arrayNewFixed {a : Admin} (h : Typing.adminHead a = "ARRAY.NEW_FIXED") :
    ∃ x n, a = .plain (.arrayNewFixed x n) := by
  revert h
  admin_head_inv

theorem call_addArray_none (ws : List ArgV) : (BI P hn host).call "add_arrayinst" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

/-- **`$packfield_(zt, val)^n`, read back**: every value is packable and the fields are Core's. -/
theorem packFields_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {zt : CStorageType} {vs : List Val}
    {V : Value} (fzt : ρ.findVal? "zt" = some (tyV zt))
    (h : EvalExp (simEnv (BI P hn host)) ρ (.iterE (.callE "packfield_" [.expA (.varE "zt"),
      .expA (.varE "val")]) (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")])) V)
    (fv : ρ.findVal? "val*" = some (.list (vs.map valV))) :
    (∀ v ∈ vs, packable zt v = true) ∧ V = .list ((vs.map (packField zt)).map fieldValV) := by
  obtain ⟨l, out, rfl, hl, -, hlen, hb⟩ := iterListN1_inv h
  rw [fv, Option.some.injEq, Value.list.injEq] at hl
  subst hl
  have key : ∀ k (hk : k < vs.length), packable zt vs[k] = true ∧
      ∀ (hk' : k < out.length), out[k] = fieldValV (packField zt vs[k]) := by
    intro k hk
    have hk₁ : k < (vs.map valV).length := by simpa using hk
    have hk₂ : k < out.length := by simpa [hlen] using hk
    have hbk := hb k hk₁ hk₂
    have hρ' : ValsOnly (ρ.bindVals [("val", (vs.map valV)[k])]) := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
    have fzt' : (ρ.bindVals [("val", (vs.map valV)[k])]).findVal? "zt" = some (tyV zt) := by
      simpa [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind] using fzt
    have fval' : (ρ.bindVals [("val", (vs.map valV)[k])]).findVal? "val" =
        some (valV vs[k]) := by
      simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]
    obtain ⟨hp, he⟩ := packfield_inv zt vs[k] ((applies_iff_callDef
      (Prims.findDef_none_of_valsOnly hρ' _) (Equiv.evalArgs_cons (evalExp_var fzt')
        (Equiv.evalArgs_cons (evalExp_var fval') Equiv.evalArgs_nil))).2
      (evalExp_callE_iff.1 hbk))
    exact ⟨hp, fun _ => he⟩
  refine ⟨fun v hv => ?_, congrArg Value.list (List.ext_getElem (by simp [hlen])
    fun k h₁ h₂ => ?_)⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    exact (key k hk).1
  · have hk : k < vs.length := by simpa [hlen] using h₁
    simpa using (key k hk).2 h₁

/-! ## The rule -/

/-- **`Step/array.new_fixed` (32) backward**, at the concrete `B`. -/
theorem bwd_arrayNewFixed {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 32 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq (hasStepRules_simEnv _).arrayNewFixed hf
  have hρ := valsOnly_bindVals σ
  obtain ⟨hz, hcode⟩ := RefsGC.cfgz_inv (z := stateV hn s f) (l := adminsToV is)
    (RefsGC.lhs_of_concl he)
  have fz := evalExp_varE_iff.1 hz
  have hr := RefsGC.rhs_of_concl he
  -- the code: `val^n` and the instruction
  obtain ⟨v₁, v₂, h₁, h₂, hcat⟩ := evalExp_catE_iff.1 hcode
  obtain ⟨u, hu, rfl⟩ := evalExp_listE_iff.1 h₂
  obtain ⟨c₁, us, hc₁, hus, rfl⟩ := evalExps_cons_iff.1 hu
  obtain rfl := evalExps_nil_iff.1 hus
  obtain ⟨V, hV, tV⟩ := hq "val*" _ (.tail _ (.tail _ (.head _)))
  obtain ⟨l', l, rfl, hl', fn, hlen, hb⟩ := iterListN1_inv h₁
  simp only [Value.cat?, Option.some.injEq, Value.list.injEq] at hcat
  have el : l = l' := List.ext_getElem hlen fun k h₁ h₂ =>
    EvalExp.unique (hb k h₂ h₁) (RefsGC.evalExp_sub_of (evalExp_var (by
      simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind])))
  subst el
  obtain ⟨A, a, rfl, hA, ha⟩ := adminsToV_eq_snoc hcat.symm
  have eV : V = .list l := Option.some.inj (hV.symm.trans hl')
  subst eV
  obtain ⟨vs, rfl⟩ := (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)).vals _ _ hρ
    (by rw [hA]; exact tV)
  rw [Sim.adminsToV_vals] at hA
  subst hA
  -- the instruction
  obtain ⟨x, n', rfl⟩ := head_arrayNewFixed (head_of_caseE (ha ▸ hc₁))
  subst ha
  obtain ⟨u, hu', he'⟩ := payload_of_caseE hc₁
  have eu : u = .tuple [Encode.toValue x, .case "%" (.tuple [.num (.natN n'.val)])] :=
    (Value.case.inj he').2.symm
  subst eu
  have hxn := RefsGC.elems_of_tup hu'
  have fx := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hxn).1
  have fn' := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hxn).2).1))).1
  have hvn : vs.length = n'.val := by
    have := fn.symm.trans fn'
    simpa using this
  -- the premise `$type(z, x) ~~ ARRAY (mut? zt)`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_cons_self ..))
  obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨w₁, ws', hw₁, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain ⟨d, hd, rfl⟩ := type_inv hρ fz fx hw₁
  obtain ⟨w₂, ws'', hw₂, hws'', rfl⟩ := evalExps_cons_iff.1 hws'
  obtain rfl := evalExps_nil_iff.1 hws''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨m, zt, rfl⟩ := array_of_tyV hw₂
  have fzt := evalExp_varE_iff.1 (R4Fwd.zt_of_expand (R4Fwd.expandInv_builtins hn host) hρ hd hct
    (evalExp_var fz) (evalExp_var fx) hwe hD)
  -- the premise `a = |$arrayinst(z)| ∧ ai = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n}`
  obtain ⟨hA₁, hA₂⟩ := evalExp_and_elim (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))))
  obtain ⟨Va, hVa, hlenA⟩ := Bwd.eq_of_cmp hA₁
  have eVa : Va = .num (.natN s.arrays.length) := by
    have := RefsGC.evalExp_len (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv (BI P hn host))
      (Prims.findDef_none_of_valsOnly hρ _) (e := .varE "z") (s := s) (f := f) (hn := hn)
      (evalExp_var fz))
    simpa using EvalExp.unique hlenA this
  subst eVa
  obtain ⟨VAI, hVAI, hstr⟩ := Bwd.eq_of_cmp hA₂
  obtain ⟨gs, hgs, rfl⟩ := evalExp_strE_iff.1 hstr
  obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := evalExpFields_two_inv hgs
  obtain ⟨d', hd', rfl⟩ := type_inv hρ fz fx hg₁
  rw [hd] at hd'
  obtain rfl := Option.some.inj hd'
  obtain ⟨hpk, rfl⟩ := packFields_inv hρ fzt hg₂ hl'
  -- the right-hand side
  have fai : (VarEnv.empty.bindVals σ).findVal? "ai" =
      some (arrayInstV ⟨d, vs.map (packField zt)⟩) := evalExp_varE_iff.1 hVAI
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN s.arrays.length)) :=
    evalExp_varE_iff.1 hVa
  have hadd := Aggregates.evalExp_addArray (Aggregates.aggDefs_simEnv (BI P hn host))
    (State.stateDefs_simEnv _)
    (Prims.findDef_none_of_valsOnly hρ _) (ez := .varE "z") (el := .listE [.varE "ai"])
    (evalExp_var fz) (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons' (evalExp_var fai)
      RefsGC.evalExps_nil'))
  refine ⟨⟨s.addArray ⟨d, vs.map (packField zt)⟩, f, [arrRef s.arrays.length]⟩,
    EvalExp.unique hr ?_, .aggregate (.arrayNewFixed hd hct hvn hpk)⟩
  exact evalExp_case (evalExp_tup2 hadd (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
    (evalExp_case (evalExp_var fa)) RefsGC.evalExps_nil')))

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
