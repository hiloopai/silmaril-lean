module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Extract

/-!
# Round 5: `vextract_lane-pack` (rule 72), backward

At the concrete builtins, `Step_pure/vextract_lane-pack` fires only on
`[v128.const b, vecExtractLane sh (some sx) li]` with a packed shape `sh` (its quantifier `pt` is
a `packtype`, `packed_of_packtype`), and the premise's `$extend__` of the lane is Core's extended
lane (`extractPack` and `Applies.unique`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d115)
open Round4Int (BI)

variable {H : Type}

set_option maxRecDepth 100000 in
theorem findTyp_packtype {B : Builtins} : (simEnv B).findTyp? "packtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d115 0))]) := rfl

/-- A value of type `packtype` is a case `packtype` declares. -/
theorem packtype_tag {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "packtype" []) v) :
    ∃ op w, v = .case op w ∧ IntNumeric.findCase (IntNumeric.instCases Original.d115 0) op ≠ none := by
  have hl : localTyp? ρ "packtype" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_packtype] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact ⟨op, w, rfl, fun hn => IntNumeric.not_hasTypCase_of_findCase_none hn hc⟩
  · exact absurd hi' not_hasTypInsts_nil

set_option maxRecDepth 100000 in
/-- **A shape whose lane type is a `packtype` is a packed integer shape.** -/
theorem packed_of_packtype {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {sh : Shape}
    (h : HasTyp (simEnv B) ρ (.varT "packtype" []) (Vec.laneTypeV sh)) :
    ∃ s, sh = .int s ∧ s.laneWidth < 32 := by
  obtain ⟨op, w, he, hf⟩ := packtype_tag hρ h
  rcases sh with s | s <;> cases s
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩
  · obtain ⟨rfl, -⟩ : "I32" = op ∧ _ := by simpa [Vec.laneTypeV, Vec.intLaneV, caseNilV] using he
    exact absurd rfl hf
  · obtain ⟨rfl, -⟩ : "I64" = op ∧ _ := by simpa [Vec.laneTypeV, Vec.intLaneV, caseNilV] using he
    exact absurd rfl hf
  · obtain ⟨rfl, -⟩ : "F32" = op ∧ _ := by simpa [Vec.laneTypeV, Vec.floatLaneV, caseNilV] using he
    exact absurd rfl hf
  · obtain ⟨rfl, -⟩ : "F64" = op ∧ _ := by simpa [Vec.laneTypeV, Vec.floatLaneV, caseNilV] using he
    exact absurd rfl hf

/-- The left-hand instruction of `vextract_lane-pack`, inverted. -/
theorem inv_vextractPack {env : Env} {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.caseE "VEXTRACT_LANE" (.tupE [.caseE "%X%" (.tupE [.subE (.varE "pt")
      (.varT "packtype" []) (.varT "lanetype" []), .varE "M"]), .optE (some (.varE "sx")),
      .varE "i"])) v) :
    ∃ ptv Mv sxv iv, v = .case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [ptv, Mv]),
      .opt (some sxv), iv]) ∧ ρ.findVal? "pt" = some ptv ∧ ρ.findVal? "M" = some Mv ∧
      ρ.findVal? "sx" = some sxv ∧ ρ.findVal? "i" = some iv := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨sv, vs₁, hsh, hvs₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨ov, vs₂, hov, hvs₂, rfl⟩ := evalExps_cons_iff.1 hvs₁
  obtain ⟨iv, vs₃, hiv, hvs₃, rfl⟩ := evalExps_cons_iff.1 hvs₂
  obtain rfl := evalExps_nil_iff.1 hvs₃
  obtain ⟨shw, hshw, rfl⟩ := evalExp_caseE_iff.1 hsh
  obtain ⟨ptv, Mv, rfl, hpt, hM⟩ := Vec.inv_tup2 hshw
  obtain ⟨sxv, hsx, rfl⟩ := evalExp_optE_some_iff.1 hov
  exact ⟨ptv, Mv, sxv, iv, rfl, evalExp_varE_iff.1 (evalExp_subE_iff.1 hpt),
    evalExp_varE_iff.1 hM, evalExp_varE_iff.1 hsx, evalExp_varE_iff.1 hiv⟩

/-- **`Step_pure/vextract_lane-pack` (rule 72), backward**, at the concrete builtins. -/
theorem bwd_vextractLanePack {P : Profile} {hn : H → String} {host : HostSemantics H}
    {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" 72 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, hp⟩ := fires_if1Q (Vec.hasVectorRules_simEnv _).vextractLanePack hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := Vec.inst_c1 he
  obtain ⟨ptv, Mv, sxv, iv, rfl, fpt, fM, fsx, fi⟩ := inv_vextractPack hy
  obtain ⟨c₂, rfl, fc₂⟩ := Vec.inv_constI32 hz
  obtain ⟨b, ins, rfl, rfl, hins⟩ := Vec.decode_c1 BwdStep.vecDecode (by simp [Vec.vecTags]) hcode
  obtain ⟨sh, sx, li, rfl, hx⟩ := vecInstrV?_vextractLane hins
  have hx' : Vec.shapeV sh = .case "%X%" (.tuple [ptv, Mv]) ∧ sx.map Vec.sxV = some sxv ∧
      Vec.laneIdxV li = iv := by
    simpa using hx.symm
  obtain ⟨hpt, hM⟩ := shapeV_inv hx'.1
  obtain ⟨sg, rfl, hsg⟩ := Option.map_eq_some_iff.1 hx'.2.1
  obtain ⟨ptw, fptw, hptw⟩ := hq "pt" (.varT "packtype" []) (by simp)
  have hptw' : ptw = Vec.laneTypeV sh := (Option.some.inj (fptw.symm.trans fpt)).trans hpt
  obtain ⟨si, rfl, hw⟩ := packed_of_packtype ⟨rfl, rfl, rfl⟩ (hptw' ▸ hptw)
  have fi' : (VarEnv.empty.bindVals σ).findVal? "i" = some (Vec.laneIdxV li) := hx'.2.2 ▸ fi
  have fpt' : (VarEnv.empty.bindVals σ).findVal? "pt" = some (Vec.intLaneV si) := fpt.trans
    (congrArg some hpt)
  have fM' : (VarEnv.empty.bindVals σ).findVal? "M" = some (pctV si.lanes) := hM ▸ fM
  have hsh : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) (.caseE "%X%"
      (.tupE [.subE (.varE "pt") (.varT "packtype" []) (.varT "lanetype" []), .varE "M"]))
      (Vec.shapeV (.int si)) :=
    hx'.1 ▸ evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fpt)) (evalExp_var fM))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hp
  have e₁ : v₁ = c₂ := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans fc₂)
  have e₂ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  obtain ⟨ws, -, -, -, hargs, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h₂)
  have happ : Applies (simEnv (BI P hn host)) "extend__" ws v₂ :=
    (Equiv.ExecNumeric.applies_iff_callDef rfl hargs).2 (evalExp_callE_iff.1 h₂)
  obtain ⟨nv, ws₁, rfl, hnv₀, hargs₁⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨tv, ws₂, rfl, ht, hargs₂⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs₁
  obtain ⟨sv', ws₃, rfl, hs', hargs₃⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs₂
  obtain ⟨lv, ws₄, rfl, hl, hargs₄⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs₃
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs₄
  obtain ⟨hlt, hlv⟩ := inv_laneAt rfl hsh f₁ fi' hl
  have htv : tv = .num (.natN 32) := evalExp_numE_iff.1 ht
  have hsv : sv' = Vec.sxV sg := (Option.some.inj ((evalExp_varE_iff.1 hs').symm.trans fsx)).trans
    hsg.symm
  have hnv : Applies (simEnv (BI P hn host)) "psize" [.val (Vec.intLaneV si)] nv :=
    Vec.inv_call rfl (Vec.evalArgs_var fpt' Equiv.evalArgs_nil) hnv₀
  obtain ⟨ls, l, n, hls, hk, hpsize, hext⟩ := extractPack P hn host si sg b li.val hlt hw
  have hls' : ls = lanesV (.int si) b :=
    Value.list.inj (Equiv.ExecNumeric.Applies.unique hls (applies_lanes P hn host (.int si) b))
  have hl' : l = lv := by
    rw [hls', getElem?_lanesV (.int si) b hlt] at hk
    exact (Option.some.inj hk).symm.trans hlv.symm
  have hn' : n = nv := Equiv.ExecNumeric.Applies.unique hpsize hnv
  have hv₂ : v₂ = numV ⟨(Shape.int si).unpacked, vecExtractLane (.int si) (some sg) li.val b⟩ :=
    Equiv.ExecNumeric.Applies.unique happ (by rw [htv, hsv, ← hl', ← hn']; exact hext)
  have hi32 : Vec.numTypeV (Shape.int si).unpacked = Equiv.Execution.i32V := by
    cases si
    · rfl
    · rfl
    · simp [IntShape.laneWidth] at hw
    · simp [IntShape.laneWidth] at hw
  refine ⟨[(Val.num ⟨(Shape.int si).unpacked, vecExtractLane (.int si) (some sg) li.val b⟩).toAdmin],
    ?_, .vector (.vecExtractLane (.int si) (some sg) li b hlt)⟩
  show Value.list [Equiv.Execution.constV Equiv.Execution.i32V c₂] =
    .list [adminToV (Val.num _).toAdmin]
  rw [Vec.adminToV_valNum, hi32, ← e₁, e₂, hv₂]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
