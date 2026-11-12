module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.ArrayNew

/-!
# Round 5: `struct.new`, backward (`Step` 29)

`z; val^n (STRUCT.NEW x) ~> $add_structinst(z, [si]); (REF.STRUCT_ADDR a)` with the premises
`$type(z, x) ~~ STRUCT (%% mut? zt)^n`, `a = |$structinst(z)|` and
`si = {TYPE $type(z, x), FIELDS $packfield_(zt, val)^n}`. As `array.new_fixed` (`ArrayNew.lean`),
with the two-domain `^n` iterations inverted by `iterListN2_inv`: the `Expand` premise binds
`zt*` to the images of the fields' storage types and fixes `n` to the number of fields, and each
field value is read back by `packfield_inv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV mutV tyV_list)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open BwdPureStep (payload_of_caseE head_of_caseE)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **A `^n` iteration over two variable domains, inverted.** -/
theorem iterListN2_inv {env : Env} {ρ : VarEnv} {b : Exp} {x₁ x₂ y₁ y₂ c : IL.Id} {v : Value}
    (h : EvalExp env ρ (.iterE b (.mk (.listN (.varE c) none)
      [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)])) v) :
    ∃ l₁ l₂ out, v = .list out ∧ ρ.findVal? y₁ = some (.list l₁) ∧
      ρ.findVal? y₂ = some (.list l₂) ∧ ρ.findVal? c = some (.num (.natN l₁.length)) ∧
      l₂.length = l₁.length ∧ out.length = l₁.length ∧
      ∀ k (h₁ : k < l₁.length) (h₂ : k < l₂.length) (h₃ : k < out.length),
        EvalExp env (ρ.bindVals [(x₁, l₁[k]), (x₂, l₂[k])]) b out[k] := by
  obtain ⟨n, h⟩ := evalExp_iterE_iff.1 h
  match n, h with
  | 0, h => simp [evalIterE] at h
  | 1, h => simp [evalIterE, evalDoms, bind, Except.bind] at h
  | 2, h => simp [evalIterE, evalDoms, bind, Except.bind, Functor.map, Except.map, evalExp] at h
  | n + 3, h =>
      simp only [evalIterE, evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc, evalExp] at h
      simp only [Res.bind_eq_ok, Res.map_eq_ok, Res.ofOption_eq_ok] at h
      obtain ⟨xvs, ⟨p₁, ⟨V₁, hy₁, rfl⟩, xs, ⟨p₂, ⟨V₂, hy₂, rfl⟩, xs', hxs', hxs⟩, hxvs⟩, kv, hkv,
        k, hk, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hxvs hxs' hxs
      subst hxs' hxs hxvs
      simp only [evalIterList, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨ds, hds, hall, vs, hvs, hout⟩ := h
      cases V₁ <;> cases V₂ <;> simp [Value.asList?] at hds
      rename_i l₁ l₂
      subst hds
      simp only [Except.ok.injEq] at hout
      subst hout
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hall
      obtain ⟨rfl, hl₂⟩ := hall
      cases kv <;> simp [Value.asNat?] at hk
      rename_i m
      cases m <;> simp at hk
      subst hk
      simp only [evalRounds] at hvs
      obtain ⟨hlen, hget⟩ := mapM_ok_get hvs
      simp only [iterRows, List.length_map, List.length_range] at hlen
      refine ⟨l₁, l₂, vs, rfl, hy₁, hy₂, hkv, hl₂, hlen, fun k h₁ h₂ h₃ => ⟨n, ?_⟩⟩
      have := hget k (by simpa [iterRows] using h₁) h₃
      simpa [iterRows, iterRow, h₁, h₂, List.getElem?_eq_getElem] using this

/-- **`zt*` and `n` from the `STRUCT (%% mut? zt)^n` expansion.** -/
theorem ztStarN_of_expand {env : Env} {ρ : VarEnv} {fs : Ty (.list .field)}
    (h : EvalExp env ρ (.caseE "STRUCT" (.caseE "%" (.tupE [.iterE (.caseE "%%" (.tupE
      [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]), .varE "zt"]))
      (.mk (.listN (.varE "n") none) [.mk "mut?" (.varE "mut?*"), .mk "zt" (.varE "zt*")])])))
      (tyV (Ty.struct fs : CCompType))) :
    ρ.findVal? "zt*" = some (.list (fs.toList.map (tyV ∘ fieldStorage))) ∧
      ρ.findVal? "n" = some (.num (.natN fs.toList.length)) := by
  have hst : tyV (Ty.struct fs : CCompType) =
      .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
    simp only [tyV, tyV_list]
    rfl
  rw [hst] at h
  have hit := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv (RefsGC.case_inv h)))).1
  obtain ⟨l₁, l₂, out, hout, -, h₂, hc, hl₂, hlo, hb⟩ := iterListN2_inv hit
  simp only [Value.list.injEq] at hout
  subst hout
  have hlen : l₁.length = fs.toList.length := by simpa using hlo.symm
  refine ⟨?_, by rw [hc, hlen]⟩
  rw [h₂]
  refine congrArg (some ∘ Value.list) (List.ext_getElem (by simp [hl₂, hlen]) fun k hk₁ hk₂ => ?_)
  have hk₀ : k < (fs.toList.map tyV).length := by simpa using hk₂
  have hb' := hb k (by omega) hk₁ hk₀
  rw [List.getElem_map, Aggregates.tyV_field] at hb'
  have hzt := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv hb'))).2).1
  have fzt : ((ρ.bindVals [("mut?", l₁[k]), ("zt", l₂[k])]).findVal? "zt") = some l₂[k] := by
    simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]
  rw [EvalExp.unique (evalExp_var fzt) hzt]
  simp

/-- **`$packfield_(zt, val)^n` over `val*` and `zt*`, read back.** -/
theorem packFields2_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {fs : List CFieldType} {vs : List Val}
    {V : Value}
    (h : EvalExp (simEnv (BI P hn host)) ρ (.iterE (.callE "packfield_" [.expA (.varE "zt"),
      .expA (.varE "val")]) (.mk (.listN (.varE "n") none)
        [.mk "val" (.varE "val*"), .mk "zt" (.varE "zt*")])) V)
    (fv : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (fzt : ρ.findVal? "zt*" = some (.list (fs.map (tyV ∘ fieldStorage)))) :
    vs.length = fs.length ∧ (∀ p ∈ fs.zip vs, packable (fieldStorage p.1) p.2 = true) ∧
      V = .list (((fs.zip vs).map fun (ft, v) => packField (fieldStorage ft) v).map fieldValV) := by
  obtain ⟨l₁, l₂, out, rfl, h₁, h₂, -, hl₂, hlo, hb⟩ := iterListN2_inv h
  rw [fv, Option.some.injEq, Value.list.injEq] at h₁
  rw [fzt, Option.some.injEq, Value.list.injEq] at h₂
  subst h₁ h₂
  have hvf : vs.length = fs.length := by simpa using hl₂.symm
  have key : ∀ k (hk : k < vs.length) (hk' : k < fs.length),
      packable (fieldStorage fs[k]) vs[k] = true ∧
      ∀ (hk'' : k < out.length), out[k] = fieldValV (packField (fieldStorage fs[k]) vs[k]) := by
    intro k hk hk'
    have hk₁ : k < (vs.map valV).length := by simpa using hk
    have hk₂ : k < (fs.map (tyV ∘ fieldStorage)).length := by simpa using hk'
    have hk₃ : k < out.length := by simpa [hlo] using hk
    have hbk := hb k hk₁ hk₂ hk₃
    have hρ' : ValsOnly (ρ.bindVals [("val", (vs.map valV)[k]),
        ("zt", (fs.map (tyV ∘ fieldStorage))[k])]) := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
    have fzt' : (ρ.bindVals [("val", (vs.map valV)[k]),
        ("zt", (fs.map (tyV ∘ fieldStorage))[k])]).findVal? "zt" =
        some (tyV (fieldStorage fs[k])) := by
      simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]
    have fval' : (ρ.bindVals [("val", (vs.map valV)[k]),
        ("zt", (fs.map (tyV ∘ fieldStorage))[k])]).findVal? "val" = some (valV vs[k]) := by
      simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]
    obtain ⟨hp, he⟩ := packfield_inv (fieldStorage fs[k]) vs[k] ((applies_iff_callDef
      (Prims.findDef_none_of_valsOnly hρ' _) (Equiv.evalArgs_cons (evalExp_var fzt')
        (Equiv.evalArgs_cons (evalExp_var fval') Equiv.evalArgs_nil))).2
      (evalExp_callE_iff.1 hbk))
    exact ⟨hp, fun _ => he⟩
  refine ⟨hvf, fun p hp => ?_, congrArg Value.list (List.ext_getElem (by simp [hlo, hvf])
    fun k h₁ h₂ => ?_)⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have hk' : k < fs.length ∧ k < vs.length := by simpa using hk
    simpa using (key k hk'.2 hk'.1).1
  · have hk : k < vs.length := by simpa [hlo] using h₁
    have hk' : k < fs.length := by omega
    simpa using (key k hk hk').2 h₁

theorem head_structNew {a : Admin} (h : Typing.adminHead a = "STRUCT.NEW") :
    ∃ x, a = .plain (.structNew x) := by
  revert h
  admin_head_inv

/-- **`Step/struct.new` (29) backward**, at the concrete `B`. -/
theorem bwd_structNew {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 29 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, he, hp⟩ := State.Fires.rule_eq (hasStepRules_simEnv _).structNew hf
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
  obtain ⟨x, rfl⟩ := head_structNew (head_of_caseE (ha ▸ hc₁))
  subst ha
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x) :=
    BwdPureStep.idx_of_var' hc₁ rfl
  -- the premise `$type(z, x) ~~ STRUCT (%% mut? zt)^n`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_cons_self ..))
  obtain ⟨ws, hws, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨w₁, ws', hw₁, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain ⟨d, hd, rfl⟩ := type_inv hρ fz fx hw₁
  obtain ⟨w₂, ws'', hw₂, hws'', rfl⟩ := evalExps_cons_iff.1 hws'
  obtain rfl := evalExps_nil_iff.1 hws''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨fs, rfl⟩ := struct_of_tyV hw₂
  obtain ⟨fzt, -⟩ := ztStarN_of_expand hw₂
  -- the premises `a = |$structinst(z)|` and `si = {TYPE $type(z, x), FIELDS …}`
  obtain ⟨Va, hVa, hlenA⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  have eVa : Va = .num (.natN s.structs.length) := by
    have := RefsGC.evalExp_len (Aggregates.evalExp_structinst
      (Aggregates.aggDefs_simEnv (BI P hn host)) (Prims.findDef_none_of_valsOnly hρ _)
      (e := .varE "z") (s := s) (f := f) (hn := hn) (evalExp_var fz))
    simpa using EvalExp.unique hlenA this
  subst eVa
  obtain ⟨VSI, hVSI, hstr⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  obtain ⟨gs, hgs, rfl⟩ := evalExp_strE_iff.1 hstr
  obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := evalExpFields_two_inv hgs
  obtain ⟨d', hd', rfl⟩ := type_inv hρ fz fx hg₁
  rw [hd] at hd'
  obtain rfl := Option.some.inj hd'
  obtain ⟨hvn, hpk, rfl⟩ := packFields2_inv hρ hg₂ hl' fzt
  -- the right-hand side
  have fsi : (VarEnv.empty.bindVals σ).findVal? "si" = some (structInstV
      ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩) :=
    evalExp_varE_iff.1 hVSI
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN s.structs.length)) :=
    evalExp_varE_iff.1 hVa
  have hadd := Aggregates.evalExp_addStruct (Aggregates.aggDefs_simEnv (BI P hn host))
    (State.stateDefs_simEnv _) (Prims.findDef_none_of_valsOnly hρ _) (ez := .varE "z")
    (el := .listE [.varE "si"]) (evalExp_var fz) (RefsGC.evalExp_listE_of
      (RefsGC.evalExps_cons' (evalExp_var fsi) RefsGC.evalExps_nil'))
  refine ⟨⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩,
    f, [.ref (.struct s.structs.length)]⟩, EvalExp.unique hr ?_,
    .aggregate (.structNew hd hct hvn hpk)⟩
  exact evalExp_case (evalExp_tup2 hadd (RefsGC.evalExp_listE_of (RefsGC.evalExps_cons'
    (evalExp_case (evalExp_var fa)) RefsGC.evalExps_nil')))

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
