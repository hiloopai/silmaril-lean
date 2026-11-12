module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Lanes
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Thms

/-!
# Round 5: `vextract_lane-num` (rule 71), backward

At the concrete builtins, `Step_pure/vextract_lane-num` fires only on
`[v128.const b, vecExtractLane sh none li]` with an unpacked shape `sh` (its quantifier `nt` is a
`numtype`, `not_hasTyp_numtype_pack`), and then produces the image of Core's step: the lane is
`lanesV sh b` at `li` (`applies_lanes` and `Applies.unique`), which is Core's extracted lane
(`laneV_eq_numV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecVector (vconstV evalExp_pctFst_iff)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d89)
open Round4Int (BI)

variable {H : Type}

/-! ## `numtype` holds no packed lane type -/

/-- A value of type `numtype` is a case `numtype` declares. -/
theorem numtype_tag {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "numtype" []) v) :
    ∃ op w, v = .case op w ∧ IntNumeric.findCase (IntNumeric.instCases Original.d89 0) op ≠ none := by
  have hl : localTyp? ρ "numtype" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [IntNumeric.findTyp_numtype] at htd
  cases htd
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    exact ⟨op, w, rfl, fun hn => IntNumeric.not_hasTypCase_of_findCase_none hn hc⟩
  · exact absurd hi' not_hasTypInsts_nil

set_option maxRecDepth 100000 in
/-- `I8` and `I16` are not `numtype`s. -/
theorem not_hasTyp_numtype_pack {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) (sh : IntShape)
    (hw : sh.laneWidth < 32) : ¬ HasTyp (simEnv B) ρ (.varT "numtype" []) (Vec.intLaneV sh) := by
  intro h
  obtain ⟨op, w, he, hf⟩ := numtype_tag hρ h
  cases sh
  · obtain ⟨rfl, -⟩ : "I8" = op ∧ _ := by simpa [Vec.intLaneV, caseNilV] using he
    exact hf rfl
  · obtain ⟨rfl, -⟩ : "I16" = op ∧ _ := by simpa [Vec.intLaneV, caseNilV] using he
    exact hf rfl
  · simp [IntShape.laneWidth] at hw
  · simp [IntShape.laneWidth] at hw

/-! ## Decoding -/

/-- `vecInstrV?` at `VEXTRACT_LANE`. -/
theorem vecInstrV?_vextractLane {i : Instr} {x : Value}
    (h : Vec.vecInstrV? i = some (.case "VEXTRACT_LANE" x)) :
    ∃ sh sx li, i = .vecExtractLane sh sx li ∧
      x = .tuple [Vec.shapeV sh, .opt (sx.map Vec.sxV), Vec.laneIdxV li] := by
  cases i <;> simp [Vec.vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- A shape image is `%X%` of its lane type and lane count. -/
theorem shapeV_inv {sh : Shape} {l m : Value} (h : Vec.shapeV sh = .case "%X%" (.tuple [l, m])) :
    l = Vec.laneTypeV sh ∧ m = pctV sh.lanes := by
  rcases sh with s | s <;>
    simpa [Vec.shapeV, Vec.ishV, Vec.fshV, Vec.laneTypeV, Shape.lanes, eq_comm] using h

/-- At an unpacked shape the lane type is the unpacked number type. -/
theorem laneTypeV_unpacked {sh : Shape} (hw : 32 ≤ sh.laneWidth) :
    Vec.laneTypeV sh = Vec.numTypeV sh.unpacked := by
  rcases sh with s | s <;> cases s
  · simp [Shape.laneWidth, IntShape.laneWidth] at hw
  · simp [Shape.laneWidth, IntShape.laneWidth] at hw
  all_goals rfl

/-! ## The conclusion and the premise of rule 71 -/

/-- The left-hand instruction of `vextract_lane-num`, inverted. -/
theorem inv_vextractNum {env : Env} {ρ : VarEnv} {v : Value}
    (h : EvalExp env ρ (.caseE "VEXTRACT_LANE" (.tupE [.caseE "%X%" (.tupE [.subE (.varE "nt")
      (.varT "numtype" []) (.varT "lanetype" []), .varE "M"]), .optE none, .varE "i"])) v) :
    ∃ ntv Mv iv, v = .case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [ntv, Mv]), .opt none, iv]) ∧
      ρ.findVal? "nt" = some ntv ∧ ρ.findVal? "M" = some Mv ∧ ρ.findVal? "i" = some iv := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨sv, vs₁, hsh, hvs₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨ov, vs₂, hov, hvs₂, rfl⟩ := evalExps_cons_iff.1 hvs₁
  obtain ⟨iv, vs₃, hiv, hvs₃, rfl⟩ := evalExps_cons_iff.1 hvs₂
  obtain rfl := evalExps_nil_iff.1 hvs₃
  obtain ⟨shw, hshw, rfl⟩ := evalExp_caseE_iff.1 hsh
  obtain ⟨ntv, Mv, rfl, hnt, hM⟩ := Vec.inv_tup2 hshw
  obtain rfl := evalExp_optE_none_iff.1 hov
  exact ⟨ntv, Mv, iv, rfl, evalExp_varE_iff.1 (evalExp_subE_iff.1 hnt), evalExp_varE_iff.1 hM,
    evalExp_varE_iff.1 hiv⟩

/-- A rule with one `if` premise, inverted with its quantifier typing kept. -/
theorem fires_if1Q {env : Env} {x : IL.Id} {i : Nat} {nm : IL.Id} {qs : List Param} {e p : Exp}
    {v : Value} (hr : Equiv.Validation.HasRuleAt env x "%~>%" i (.ruleD nm qs "%~>%" e [.ifPr p]))
    (hf : Fires env x i v) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      EvalExp env (VarEnv.empty.bindVals σ) p (.bool true) := by
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := Vec.fires_body hr hf
  have h0 : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  exact ⟨σ, h0 ▸ hq, h0 ▸ he, h0 ▸ Vec.inv_if (hp _ List.mem_cons_self)⟩

/-- `$lanes_(sh, c_1)[i!%.0]` at the concrete builtins, inverted: the lane of `lanesV`. -/
theorem inv_laneAt {P : Profile} {hn : H → String} {host : HostSemantics H} {ρ : VarEnv}
    {x : IL.Id} {t₁ t₂ : Typ} {sh : Shape} {b : V128} {li : LaneIdx} {v : Value}
    (hd : ρ.findDef? "lanes_" = none)
    (hsh : EvalExp (simEnv (BI P hn host)) ρ (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂,
      .varE "M"])) (Vec.shapeV sh))
    (hc₁ : ρ.findVal? "c_1" = some (Vec.vecV b)) (hi : ρ.findVal? "i" = some (Vec.laneIdxV li))
    (h : EvalExp (simEnv (BI P hn host)) ρ (.idxE (.callE "lanes_" [.expA (.caseE "%X%"
      (.tupE [.subE (.varE x) t₁ t₂, .varE "M"])), .expA (.varE "c_1")])
      (.projE (.uncaseE (.varE "i") "%") 0)) v) :
    li.val < sh.lanes ∧ v = laneV sh ((sh.lanesOf b).getD li.val 0) := by
  obtain ⟨lv, k, hcall, hk, hidx⟩ := evalExp_idxE_iff.1 h
  have hargs : EvalArgs (simEnv (BI P hn host)) ρ [.expA (.caseE "%X%" (.tupE
      [.subE (.varE x) t₁ t₂, .varE "M"])), .expA (.varE "c_1")]
      [.val (Vec.shapeV sh), .val (Vec.vecV b)] :=
    Equiv.evalArgs_cons hsh (Equiv.evalArgs_cons (evalExp_var hc₁) Equiv.evalArgs_nil)
  have hl : lv = .list (lanesV sh b) :=
    Equiv.ExecNumeric.Applies.unique (Vec.inv_call hd hargs hcall) (applies_lanes P hn host sh b)
  obtain ⟨rest, hrest⟩ := evalExp_pctFst_iff.1 hk
  have hkv : k = li.val := by
    rw [hi] at hrest
    simp only [Vec.laneIdxV, pctV, Option.some.injEq, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, Value.num.injEq, Num.natN.injEq, true_and] at hrest
    exact hrest.1.symm
  have hget : (lanesV sh b)[li.val]? = some v := by
    rw [hl, hkv] at hidx
    exact hidx
  have hlt : li.val < sh.lanes := by
    have := (List.getElem?_eq_some_iff.1 hget).1
    simpa [lanesV, Shape.lanesOf] using this
  exact ⟨hlt, Option.some.inj (hget.symm.trans (getElem?_lanesV sh b hlt))⟩

/-- `CONST nt c`, where `nt` is the extracted shape's lane type, is Core's result image. -/
theorem constV_lane_eq {sh : Shape} (hw : 32 ≤ sh.laneWidth) (b : V128) (k : Nat) :
    Value.case "CONST" (.tuple [Vec.laneTypeV sh, laneV sh ((sh.lanesOf b).getD k 0)]) =
      adminToV (Val.num ⟨sh.unpacked, vecExtractLane sh none k b⟩).toAdmin := by
  rw [Vec.adminToV_valNum, laneTypeV_unpacked hw, laneV_eq_numV sh b k hw]
  rfl

/-- A shape whose lane type is a `numtype` is unpacked. -/
theorem laneWidth_of_numtype {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {sh : Shape}
    (h : HasTyp (simEnv B) ρ (.varT "numtype" []) (Vec.laneTypeV sh)) : 32 ≤ sh.laneWidth := by
  rcases sh with s | s
  · by_contra hlt
    exact not_hasTyp_numtype_pack hρ s (by simpa [Shape.laneWidth] using hlt) h
  · cases s <;> decide

/-- **`Step_pure/vextract_lane-num` (rule 71), backward**, at the concrete builtins. -/
theorem bwd_vextractLaneNum {P : Profile} {hn : H → String} {host : HostSemantics H}
    {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" 71 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, hq, he, hp⟩ := fires_if1Q (Vec.hasVectorRules_simEnv _).vextractLaneNum hf
  obtain ⟨c₁, y, z, hcode, rfl, f₁, hy, hz⟩ := Vec.inst_c1 he
  obtain ⟨ntv, Mv, iv, rfl, fnt, fM, fi⟩ := inv_vextractNum hy
  obtain ⟨ntv', c₂, rfl, fnt', fc₂⟩ := Vec.inv_op2 hz
  obtain ⟨b, ins, rfl, rfl, hins⟩ := Vec.decode_c1 BwdStep.vecDecode (by simp [Vec.vecTags]) hcode
  obtain ⟨sh, sx, li, rfl, hx⟩ := vecInstrV?_vextractLane hins
  have hx' : Vec.shapeV sh = .case "%X%" (.tuple [ntv, Mv]) ∧ sx.map Vec.sxV = none ∧
      Vec.laneIdxV li = iv := by
    simpa using hx.symm
  have hnt : ntv = Vec.laneTypeV sh := (shapeV_inv hx'.1).1
  have hsx : sx = none := Option.map_eq_none_iff.1 hx'.2.1
  have hnt' : ntv' = ntv := Option.some.inj (fnt'.symm.trans fnt)
  obtain ⟨ntw, fntw, hntw⟩ := hq "nt" (.varT "numtype" []) (by simp)
  have hntw' : ntw = Vec.laneTypeV sh := (Option.some.inj (fntw.symm.trans fnt)).trans hnt
  have hw : 32 ≤ sh.laneWidth := laneWidth_of_numtype ⟨rfl, rfl, rfl⟩ (hntw' ▸ hntw)
  have hsh : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ) (.caseE "%X%"
      (.tupE [.subE (.varE "nt") (.varT "numtype" []) (.varT "lanetype" []), .varE "M"]))
      (Vec.shapeV sh) :=
    hx'.1 ▸ evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fnt)) (evalExp_var fM))
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 hp
  have e₁ : v₁ = c₂ := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans fc₂)
  have e₂ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  obtain ⟨hlt, hv₂⟩ := inv_laneAt rfl hsh f₁ (hx'.2.2 ▸ fi) h₂
  subst hsx
  refine ⟨[(Val.num ⟨sh.unpacked, vecExtractLane sh none li.val b⟩).toAdmin], ?_,
    .vector (.vecExtractLane sh none li b hlt)⟩
  have hc₂ : c₂ = laneV sh ((sh.lanesOf b).getD li.val 0) := e₁.symm.trans (e₂.trans hv₂)
  rw [hnt', hnt, hc₂, constV_lane_eq hw]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
