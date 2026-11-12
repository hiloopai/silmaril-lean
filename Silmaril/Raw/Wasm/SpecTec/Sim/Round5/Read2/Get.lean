module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Unpack

/-!
# Round 5, pass 3, track read: `struct.get-struct` (71), `array.get-array` (79), backward

`z; (REF.ARRAY_ADDR a) (CONST I32 i) (ARRAY.GET sx? x) ~>
$unpackfield_(zt, sx?, $arrayinst(z)[a].FIELDS[i])` with `Expand($type(z, x), ARRAY (mut? zt))`.
Read back: the field read evaluates only at an existing array and an index in bounds
(`arrayField_inv`); the `Expand` premise gives the array type and `zt` (`expandArray_inv`);
`$unpackfield_` evaluates only on Core's domain `unpackable` (`unpackfield_inv`).

`struct.get-struct` (71) is the same with `$structinst`, and with `zt*[i]` for `zt`: the
`Expand` premise `STRUCT (%% mut? zt)*` binds `zt*` to the images of the fields' storage types
(`BwdStep.ztStar_of_expand`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)
open Round4Read (decode_refArray decode_aconst_at)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **The last instruction of a three-instruction left-hand side**, evaluated. -/
theorem lhs3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {s : Store H} {f : Frame}
    {a₁ a₂ a₃ : Admin}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [e₁, e₂, e₃]]))
      (configV hn ⟨s, f, [a₁, a₂, a₃]⟩)) :
    EvalExp env ρ e₃ (adminToV a₃) := by
  have h' : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [e₁, e₂, e₃]]))
      (.case "%;%" (.tuple [stateV hn s f, .list [adminToV a₁, adminToV a₂, adminToV a₃]])) := h
  have hl := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h'))).2).1
  have hs := RefsGC.elems_of_list hl
  exact (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.evalExps_cons_inv hs).2).2).1

/-- **`$arrayinst(z)[a].FIELDS[i]`, read back**: the array exists and the index is in bounds. -/
theorem arrayField_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat}
    {i : Nat} {FV : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN k))) (fi : ρ.findVal? "i" = some (idxV i))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) FV) :
    ∃ ai fv, s.arrays[k]? = some ai ∧ ai.fields[i]? = some fv ∧ FV = fieldValV fv := by
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 h
  obtain ⟨R, hR, hRF⟩ := evalExp_dotE_iff.1 hL
  obtain ⟨Ls, j', hLs, hj', hidx⟩ := evalExp_idxE_iff.1 hR
  have eLs : Ls = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hLs (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv _)
      (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz))
  have ej' : j' = k := by simpa using EvalExp.unique hj' (evalExp_var fa)
  have ej : j = i := by simpa using EvalExp.unique hj (RefsGC.evalExp_unpct (evalExp_var fi))
  subst eLs ej' ej
  have hmap : (s.arrays[j']?).map arrayInstV = some R := by simpa [Value.idx?] using hidx
  obtain ⟨ai, ha, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have eL : L = .list (ai.fields.map fieldValV) := by simpa [arrayInstV] using hRF.symm
  subst eL
  have hmap' : (ai.fields[j]?).map fieldValV = some FV := by simpa [Value.idx?] using hLj
  obtain ⟨fv, hfv, rfl⟩ := Option.map_eq_some_iff.1 hmap'
  exact ⟨ai, fv, ha, hfv, rfl⟩

/-- **A one-instruction right-hand side `[e <: instr]`**, inverted. -/
theorem rhs_sub1_inv {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : Typ} {w : Value}
    (h : EvalExp env ρ (.listE [.subE e t₁ t₂]) w) : ∃ u, EvalExp env ρ e u ∧ w = .list [u] := by
  obtain ⟨us, hus, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨u, us', hu, hus', rfl⟩ := evalExps_cons_iff.1 hus
  obtain rfl := evalExps_nil_iff.1 hus'
  exact ⟨u, (evalExp_subE_iff.1 hu), rfl⟩

/-- **`Step_read` 79 (`array.get-array`), backward.** -/
theorem bwd_arrayGetArray : ∀ (c : Config H) (w : Value),
    Fires (simEnv (BI P hn host)) "Step_read" 79 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.arrayGetArray hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  have hl := RefsGC.lhs_of_concl he
  have hc : ∃ G, configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]), .case "ARRAY.GET" G]]) := by
    concl_inv hl
  obtain ⟨G, hcfg⟩ := hc
  obtain ⟨hZ, hcode⟩ := cfg_inv hcfg
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Aggregates.adminsToV_eq_triple hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨sx, x, rfl⟩ := BwdRead.head_arrayGet (Typing.adminToV_case h₃).symm
  subst hZ
  have h₃' : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "ARRAY.GET" (.tupE [.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")]),
        .varE "x"])) (.case "ARRAY.GET" (.tuple [.opt (sx.map Equiv.sxV), Encode.toValue x])) :=
    lhs3_inv hl
  have hg := RefsGC.elems_of_tup (RefsGC.case_inv h₃')
  have hsxE := (RefsGC.evalExps_cons_inv hg).1
  have fx := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hg).2).1
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  obtain ⟨d, m, zt, hd, hexp, fzt, -⟩ := expandArray_inv fz fx hwe hD
  obtain ⟨U, hU, rfl⟩ := rhs_sub1_inv (RefsGC.rhs_of_concl he)
  obtain ⟨ws, hws⟩ := BwdStep.args_of_call hU
  obtain ⟨-, ws₁, -, hws₁, rfl⟩ := BwdStep.evalArgs_cons_inv hws
  obtain ⟨-, ws₂, -, hws₂, rfl⟩ := BwdStep.evalArgs_cons_inv hws₁
  obtain ⟨FV, ws₃, hFV, -, rfl⟩ := BwdStep.evalArgs_cons_inv hws₂
  obtain ⟨ai, fv, ha, hfv, rfl⟩ := arrayField_inv hρ fz fa fi hFV
  obtain ⟨hu, rfl⟩ := unpackfield_inv zt sx fv ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons (evalExp_var fzt)
      (Equiv.evalArgs_cons hsxE (Equiv.evalArgs_cons hFV Equiv.evalArgs_nil)))).2
    (evalExp_callE_iff.1 hU))
  refine ⟨[(unpackField sx fv).toAdmin], ?_, .aggregate (.arrayGetArray ha hfv hd hexp hu)⟩
  simp [adminsToV, State.adminToV_toAdmin]

/-- **`$structinst(z)[a].FIELDS[i]`, read back**: the struct exists and the index is in bounds. -/
theorem structField_inv {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat}
    {i : Nat} {FV : Value} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN k)))
    (hi : EvalExp (simEnv (BI P hn host)) ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN i)))
    (h : EvalExp (simEnv (BI P hn host)) ρ
      (.idxE (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) FV) :
    ∃ si fv, s.structs[k]? = some si ∧ si.fields[i]? = some fv ∧ FV = fieldValV fv := by
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 h
  obtain ⟨R, hR, hRF⟩ := evalExp_dotE_iff.1 hL
  obtain ⟨Ls, j', hLs, hj', hidx⟩ := evalExp_idxE_iff.1 hR
  have eLs : Ls = .list (s.structs.map structInstV) :=
    EvalExp.unique hLs (Aggregates.evalExp_structinst (Aggregates.aggDefs_simEnv _)
      (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz))
  have ej' : j' = k := by simpa using EvalExp.unique hj' (evalExp_var fa)
  have ej : j = i := by simpa using EvalExp.unique hj hi
  subst eLs ej' ej
  have hmap : (s.structs[j']?).map structInstV = some R := by simpa [Value.idx?] using hidx
  obtain ⟨si, hsi, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have eL : L = .list (si.fields.map fieldValV) := by simpa [structInstV] using hRF.symm
  subst eL
  have hmap' : (si.fields[j]?).map fieldValV = some FV := by simpa [Value.idx?] using hLj
  obtain ⟨fv, hfv, rfl⟩ := Option.map_eq_some_iff.1 hmap'
  exact ⟨si, fv, hsi, hfv, rfl⟩

/-- **`Step_read` 71 (`struct.get-struct`), backward.** -/
theorem bwd_structGetStruct : ∀ (c : Config H) (w : Value),
    Fires (simEnv (BI P hn host)) "Step_read" 71 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.structGetStruct hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨hz, hcode⟩ := RefsGC.cfgz_inv (z := stateV hn s f) (l := adminsToV is)
    (RefsGC.lhs_of_concl he)
  have fz := evalExp_varE_iff.1 hz
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := BwdPureStep.codes_two (RefsGC.elems_of_list hcode)
  obtain ⟨n, rfl⟩ := BwdStep.head_refStruct (BwdPureStep.head_of_caseE h₁)
  have fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN n)) :=
    BwdPureStep.idx_of_var' h₁ rfl
  obtain ⟨sx, x, i, rfl⟩ := BwdRead.head_structGet (BwdPureStep.head_of_caseE h₂)
  obtain ⟨u, hu, he'⟩ := BwdPureStep.payload_of_caseE h₂
  have eu : u = .tuple [.opt (sx.map Equiv.sxV), Encode.toValue x, Encode.toValue i] :=
    (Value.case.inj he').2.symm
  subst eu
  have hg := RefsGC.elems_of_tup hu
  have hsxE := (RefsGC.evalExps_cons_inv hg).1
  have fx := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hg).2).1
  have fi := evalExp_varE_iff.1 (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.evalExps_cons_inv hg).2).2).1
  have hii : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN i.toNat)) := RefsGC.evalExp_unpct
    (evalExp_var fi)
  -- the premise `$type(z, x) ~~ STRUCT (%% mut? zt)*`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ (List.mem_singleton_self _))
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨v₁, vs', h₁', hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨d, hd, rfl⟩ := BwdStep.type_inv hρ fz fx h₁'
  obtain ⟨v₂, vs'', h₂', hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨fs, rfl⟩ := BwdStep.struct_of_tyV h₂'
  obtain ⟨l, fzt, rfl⟩ := BwdStep.ztStar_of_expand h₂'
  -- the right-hand side
  obtain ⟨U, hU, rfl⟩ := rhs_sub1_inv (RefsGC.rhs_of_concl he)
  obtain ⟨ws, hws⟩ := BwdStep.args_of_call hU
  obtain ⟨ZT, ws₁, hZT, hws₁, rfl⟩ := BwdStep.evalArgs_cons_inv hws
  obtain ⟨-, ws₂, -, hws₂, rfl⟩ := BwdStep.evalArgs_cons_inv hws₁
  obtain ⟨FV, ws₃, hFV, -, rfl⟩ := BwdStep.evalArgs_cons_inv hws₂
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hZT
  have eL : L = .list (fs.toList.map (tyV ∘ fieldStorage)) :=
    EvalExp.unique hL (Equiv.Execution.evalExp_iterPat (by decide) fzt)
  have ej : Value.num (.natN j) = .num (.natN i.toNat) := EvalExp.unique hj hii
  simp only [Value.num.injEq, Num.natN.injEq] at ej
  subst eL ej
  simp only [Value.idx?, List.getElem?_map] at hLj
  obtain ⟨ft, hft, rfl⟩ := Option.map_eq_some_iff.1 hLj
  obtain ⟨si, fv, hsi, hfv, rfl⟩ := structField_inv hρ fz fa hii hFV
  obtain ⟨hup, rfl⟩ := unpackfield_inv (fieldStorage ft) sx fv ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons hZT
      (Equiv.evalArgs_cons hsxE (Equiv.evalArgs_cons hFV Equiv.evalArgs_nil)))).2
    (evalExp_callE_iff.1 hU))
  refine ⟨[(unpackField sx fv).toAdmin], ?_,
    .aggregate (.structGetStruct hsi hfv hd hct hft hup)⟩
  simp [adminsToV, State.adminToV_toAdmin]

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
