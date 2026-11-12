module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Agg

/-!
# Round 5: `struct.set-struct`, backward (`Step` 31)

As `array.set-array` (`Agg.lean`), with the struct's field list rebuilt in the `Expand` premise as
the two-domain iteration `STRUCT (%% mut? zt)*` over the quantifiers `mut?*`, `zt*`.
`iterList2_inv` inverts such an iteration (the evaluator's `evalIterE`/`evalIterList`/
`evalRounds`): both domains are lists of the output's length and the body evaluates pointwise.
Against the image of Core's expansion `STRUCT fs` this binds `zt*` to the images of the fields'
storage types (`ztStar_of_expand`), so `zt*[i]` is the `i`-th field's storage type, and
`$packfield_` and `$with_struct` are read back as in `Agg.lean`.
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
open BwdPureStep (fires_step codes_three payload_of_caseE head_of_caseE rhs_nil body_pair
  val_of_var head_structSet idx_of_var')
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Two-domain iterations, inverted -/

/-- `mapM` of a function into `Res`, read back pointwise. -/
theorem mapM_ok_get {α β : Type} {f : α → Res β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length ∧
      ∀ k (hk : k < l.length) (hk' : k < r.length), f l[k] = .ok r[k]
  | [], r, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
  | a :: l, r, h => by
      simp only [List.mapM_cons, bind, Except.bind] at h
      cases ha : f a with
      | error e => simp [ha] at h
      | ok b =>
          cases hl : l.mapM f with
          | error e => simp [ha, hl] at h
          | ok bs =>
              simp only [ha, hl, pure, Except.pure, Except.ok.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := mapM_ok_get hl
              refine ⟨by simp [hlen], fun k hk hk' => ?_⟩
              cases k with
              | zero => simpa using ha
              | succ k => simpa using hget k (by simpa using hk) (by simpa using hk')

/-- **A `*` iteration over two variable domains, inverted.** -/
theorem iterList2_inv {env : Env} {ρ : VarEnv} {b : Exp} {x₁ x₂ y₁ y₂ : IL.Id} {out : List Value}
    (h : EvalExp env ρ (.iterE b (.mk .list [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)])) (.list out)) :
    ∃ l₁ l₂, ρ.findVal? y₁ = some (.list l₁) ∧ ρ.findVal? y₂ = some (.list l₂) ∧
      l₁.length = out.length ∧ l₂.length = out.length ∧
      ∀ k (h₁ : k < l₁.length) (h₂ : k < l₂.length) (h₃ : k < out.length),
        EvalExp env (ρ.bindVals [(x₁, l₁[k]), (x₂, l₂[k])]) b out[k] := by
  obtain ⟨n, h⟩ := evalExp_iterE_iff.1 h
  match n, h with
  | 0, h => simp [evalIterE] at h
  | 1, h => simp [evalIterE, evalDoms, bind, Except.bind] at h
  | 2, h => simp [evalIterE, evalDoms, bind, Except.bind, Functor.map, Except.map, evalExp] at h
  | n + 3, h =>
      simp only [evalIterE, evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc, evalExp] at h
      simp only [Res.bind_eq_ok, Res.map_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨xvs, ⟨p₁, ⟨V₁, hy₁, rfl⟩, xs, ⟨p₂, ⟨V₂, hy₂, rfl⟩, xs', hxs', hxs⟩, hxvs⟩, -, k, hk, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at hxvs hxs' hxs
      subst hxs' hxs hxvs
      cases V₁ <;> simp [Value.asList?] at hk
      rename_i l₁
      subst hk
      simp only [evalIterList, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨ds, hds, hall, vs, hvs, hout⟩ := h
      cases V₂ <;> simp [Value.asList?] at hds
      rename_i l₂
      subst hds
      simp only [Except.ok.injEq, Value.list.injEq] at hout
      subst hout
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hall
      simp only [evalRounds] at hvs
      obtain ⟨hlen, hget⟩ := mapM_ok_get hvs
      simp only [iterRows, List.length_map, List.length_range] at hlen
      refine ⟨l₁, l₂, hy₁, hy₂, hlen.symm, hall.2.trans hlen.symm, fun k h₁ h₂ h₃ => ⟨n, ?_⟩⟩
      have := hget k (by simpa [iterRows] using h₁) h₃
      simpa [iterRows, iterRow, h₁, h₂, List.getElem?_eq_getElem] using this

/-! ## `zt*` from the `STRUCT` expansion -/

theorem head_refStruct {a : Admin} (h : Typing.adminHead a = "REF.STRUCT_ADDR") :
    ∃ n, a = .ref (.struct n) := by
  revert h
  admin_head_inv

/-- The composite type an `Expand` image of the `STRUCT` shape names is a struct type. -/
theorem struct_of_tyV {ct : CCompType} {e : Exp} {env : Env} {ρ : VarEnv}
    (h : EvalExp env ρ (.caseE "STRUCT" e) (tyV ct)) : ∃ fs, ct = .struct fs := by
  obtain ⟨u, -, hu⟩ := evalExp_caseE_iff.1 h
  match ct, hu with
  | .struct fs, _ => exact ⟨fs, rfl⟩
  | .array _, hu => exact absurd (Value.case.inj hu).1 (by decide)
  | .func _ _, hu => exact absurd (Value.case.inj hu).1 (by decide)

/-- **`zt*` from the `STRUCT` expansion**: the premise pattern `STRUCT (%% mut? zt)*`, evaluated
to the image of `STRUCT fs`, binds `zt*` to the images of the fields' storage types. -/
theorem ztStar_of_expand {env : Env} {ρ : VarEnv} {fs : Ty (.list .field)}
    (h : EvalExp env ρ (.caseE "STRUCT" (.caseE "%" (.tupE [.iterE (.caseE "%%" (.tupE
      [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]), .varE "zt"]))
      (.mk .list [.mk "mut?" (.varE "mut?*"), .mk "zt" (.varE "zt*")])])))
      (tyV (Ty.struct fs : CCompType))) :
    ∃ l, ρ.findVal? "zt*" = some (.list l) ∧ l = fs.toList.map (tyV ∘ fieldStorage) := by
  have hst : tyV (Ty.struct fs : CCompType) =
      .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) := by
    simp only [tyV, tyV_list]
    rfl
  rw [hst] at h
  have hit := (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup
    (RefsGC.case_inv (RefsGC.case_inv h)))).1
  obtain ⟨l₁, l₂, -, h₂, hl₁, hl₂, hb⟩ := iterList2_inv hit
  refine ⟨l₂, h₂, List.ext_getElem (by simpa using hl₂) fun k hk₁ hk₂ => ?_⟩
  have hk₀ : k < (fs.toList.map tyV).length := by simpa using hk₂
  have hb' := hb k (by omega) hk₁ hk₀
  rw [List.getElem_map, Aggregates.tyV_field] at hb'
  have hzt := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv hb'))).2).1
  have fzt : ((ρ.bindVals [("mut?", l₁[k]), ("zt", l₂[k])]).findVal? "zt") = some l₂[k] := by
    simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]
  rw [EvalExp.unique (evalExp_var fzt) hzt]
  simp

/-! ## `$with_struct`, inverted, and the rule -/

/-- **A `$with_struct(z, a, i, fv)` call that evaluates writes inside an existing struct.** -/
theorem withStruct_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {A I : Nat}
    {ei eF : Exp} {F W : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN A)))
    (hi : EvalExp (simEnv (BI P hn host)) ρ ei (.num (.natN I)))
    (hF : EvalExp (simEnv (BI P hn host)) ρ eF F)
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.callE "with_struct" [.expA (.varE "z"), .expA (.varE "a"), .expA ei, .expA eF]) W) :
    ∃ si, s.structs[A]? = some si ∧ I < si.fields.length := by
  have D := Aggregates.aggDefs_simEnv (BI P hn host)
  have SD := State.stateDefs_simEnv (BI P hn host)
  have hbody := BwdPureStep.evalExp_call1_inv D.withStruct (Prims.findDef_none_of_valsOnly hρ _)
    (call_withStruct_none _)
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
  have hS' : (storeV hn s).field? "STRUCTS" = some (.list (s.structs.map structInstV)) := rfl
  rw [hS', Option.some.injEq] at hRf
  subst hRf
  have eiv₂ : iv₂ = .num (.natN A) := EvalExp.unique hiv₂ (evalExp_var rfl)
  subst eiv₂
  simp only [Value.asNat?, Option.some.injEq] at ha'
  subst ha'
  simp only [Value.idx?, List.getElem?_map] at hLa
  obtain ⟨si, hsi, rfl⟩ := Option.map_eq_some_iff.1 hLa
  have hFl' : (structInstV si).field? "FIELDS" = some (.list (si.fields.map fieldValV)) := rfl
  rw [hFl', Option.some.injEq] at hFl
  subst hFl
  refine ⟨si, hsi, ?_⟩
  simp only [Value.setIdx, List.length_map] at hset
  by_contra hc
  simp [hc] at hset

/-- **`Step/struct.set-struct` (31) backward**, at the concrete `B`. -/
theorem bwd_structSetStruct {c : Config H} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step" 31 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv _).structSetStruct hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨n, rfl⟩ := head_refStruct (head_of_caseE h₁)
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN n)) := idx_of_var' h₁ rfl
  obtain ⟨v, rfl, fval⟩ := val_of_var hq (.tail _ (.tail _ (.head _))) h₂
  obtain ⟨x, i, rfl⟩ := head_structSet (head_of_caseE h₃)
  obtain ⟨u, hu, he⟩ := payload_of_caseE h₃
  have eu : u = .tuple [Encode.toValue x, Encode.toValue i] := (Value.case.inj he).2.symm
  subst eu
  have hxi := RefsGC.elems_of_tup hu
  have fx := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv hxi).1
  have fi := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hxi).2).1
  have hρ := valsOnly_bindVals σ
  -- the premise `$type(z, x) ~~ STRUCT (%% mut? zt)*`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨v₁, vs', h₁', hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨d, hd, rfl⟩ := type_inv hρ fz fx h₁'
  obtain ⟨v₂, vs'', h₂', hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨fs, rfl⟩ := struct_of_tyV h₂'
  obtain ⟨l, fzt, rfl⟩ := ztStar_of_expand h₂'
  -- the right-hand side
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  obtain ⟨ws, hws⟩ := args_of_call hW
  obtain ⟨-, ws₁, -, hws₁, rfl⟩ := evalArgs_cons_inv hws
  obtain ⟨-, ws₂, -, hws₂, rfl⟩ := evalArgs_cons_inv hws₁
  obtain ⟨-, ws₃, -, hws₃, rfl⟩ := evalArgs_cons_inv hws₂
  obtain ⟨F, ws₄, hF, -, rfl⟩ := evalArgs_cons_inv hws₃
  have hii : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN i.toNat)) := RefsGC.evalExp_unpct
    (evalExp_var fi)
  obtain ⟨wsF, hwsF⟩ := args_of_call hF
  obtain ⟨ZT, wsF', hZT, -, rfl⟩ := evalArgs_cons_inv hwsF
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hZT
  have eL : L = .list (fs.toList.map (tyV ∘ fieldStorage)) :=
    EvalExp.unique hL (Equiv.Execution.evalExp_iterPat (by decide) fzt)
  have ej : Value.num (.natN j) = .num (.natN i.toNat) := EvalExp.unique hj hii
  simp only [Value.num.injEq, Num.natN.injEq] at ej
  subst eL ej
  simp only [Value.idx?, List.getElem?_map] at hLj
  obtain ⟨ft, hft, rfl⟩ := Option.map_eq_some_iff.1 hLj
  obtain ⟨hpk, rfl⟩ := packfield_inv (fieldStorage ft) v ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons hZT
      (Equiv.evalArgs_cons (evalExp_var fval) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 hF))
  obtain ⟨si, hsi, hlt⟩ := withStruct_inv hρ fz fa hii hF hW
  have ew := Aggregates.evalExp_withStruct (Aggregates.aggDefs_simEnv _)
    (State.stateDefs_simEnv _) (Prims.findDef_none_of_valsOnly hρ _) hsi hlt (evalExp_var fz)
    (evalExp_var fa) hii hF
  refine ⟨⟨s.setStructField n i.toNat (packField (fieldStorage ft) v), f, []⟩, ?_,
    .aggregate (.structSetStruct hd hct hft hsi hlt hpk)⟩
  rw [EvalExp.unique hW ew]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
