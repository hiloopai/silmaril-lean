module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Float

/-!
# Family V: lane extraction, forward

`Step_pure/vextract_lane-num` (rule 71) and `vextract_lane-pack` (rule 72), constructed under the
declarative reading, and `VectorStep.vecExtractLane` forward through them. The typing fact
`VecTyping.extractSx` (the IL premise of `VEXTRACT_LANE`: a signedness exactly for packed lanes)
rules out the other combinations of shape and signedness.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vextractLaneNumRule vextractLanePackRule
  vreplaceLaneRule vconstV evalExp_pctFst_iff)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.Execution (constV i32V caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

/-- `$lanes_(sh, c_1)[i!%.0]`, with the shape spelt `%X%(x, M)` for a variable lane type `x`. -/
theorem evalExp_laneAt {env : Env} {ρ : VarEnv} {x : IL.Id} {t₁ t₂ : Typ} {lt M c₁ l : Value}
    {k : Nat} {ls : List Value} (hd : ρ.findDef? "lanes_" = none) (hx : ρ.findVal? x = some lt)
    (hM : ρ.findVal? "M" = some M)
    (hc₁ : ρ.findVal? "c_1" = some c₁) (hi : ρ.findVal? "i" = some (pctV k))
    (ha : Applies env "lanes_" [.val (.case "%X%" (.tuple [lt, M])), .val c₁] (.list ls))
    (hk : ls[k]? = some l) :
    EvalExp env ρ (.idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂,
      .varE "M"])), .expA (.varE "c_1")]) (.projE (.uncaseE (.varE "i") "%") 0)) l := by
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂, .varE "M"]))
      (.case "%X%" (.tuple [lt, M])) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var hx)) (evalExp_var hM))
  have hargs : EvalArgs env ρ [.expA (.caseE "%X%" (.tupE [.subE (.varE x) t₁ t₂, .varE "M"])),
      .expA (.varE "c_1")] [.val (.case "%X%" (.tuple [lt, M])), .val c₁] :=
    Equiv.evalArgs_cons esh (evalArgs_var hc₁ Equiv.evalArgs_nil)
  have ecall := evalExp_call hd hargs ha
  have eidx : EvalExp env ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN k)) :=
    evalExp_pctFst_iff.2 ⟨[], hi⟩
  exact evalExp_idxE_iff.2 ⟨_, k, ecall, eidx, hk⟩

/-- `Step_pure/vextract_lane-num` (rule 71). -/
theorem spure_vextractLaneNum {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 71 vextractLaneNumRule) {c₁ nt M c₂ : Value} {k : Nat}
    {ls : List Value} (hc₁ : TypedV env vecT c₁) (hnt : TypedV env numtypeT nt)
    (hM : TypedV env (.varT "M" []) M) (hi : TypedV env (.varT "laneidx" []) (pctV k))
    (hc₂ : TypedDep env "nt" nt (numT "nt") c₂)
    (ha : Applies env "lanes_" [.val (.case "%X%" (.tuple [nt, M])), .val c₁] (.list ls))
    (hk : ls[k]? = some c₂) :
    SPure env [vconstV c₁, .case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [nt, M]),
      .opt none, pctV k])] [constV nt c₂] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("nt", nt), ("M", M), ("i", pctV k), ("c_2", c₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "nt" = some nt := rfl
  have f3 : ρ.findVal? "M" = some M := rfl
  have f4 : ρ.findVal? "i" = some (pctV k) := rfl
  have f5 : ρ.findVal? "c_2" = some c₂ := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "nt" numtypeT, .expP "M" (.varT "M" []),
      .expP "i" (.varT "laneidx" []), .expP "c_2" (numT "nt")] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hnt ρ hρ) (QuantsOk.cons f3 (hM ρ hρ)
      (QuantsOk.cons f4 (hi ρ hρ) (QuantsOk.cons f5 (hc₂ ρ hρ f2) QuantsOk.nil))))
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.subE (.varE "nt") numtypeT (.varT "lanetype" []),
      .varE "M"])) (.case "%X%" (.tuple [nt, M])) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var f2)) (evalExp_var f3))
  have einstr : EvalExp env ρ (.caseE "VEXTRACT_LANE" (.tupE [.caseE "%X%" (.tupE
      [.subE (.varE "nt") numtypeT (.varT "lanetype" []), .varE "M"]), .optE none, .varE "i"]))
      (.case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [nt, M]), .opt none, pctV k])) :=
    evalExp_case (evalExp_tup3 esh ⟨1, by simp [evalExp]⟩ (evalExp_var f4))
  have hl : EvalExp env ρ (.idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "nt") numtypeT (.varT "lanetype" []), .varE "M"])), .expA (.varE "c_1")])
      (.projE (.uncaseE (.varE "i") "%") 0)) c₂ :=
    evalExp_laneAt rfl f2 f3 f1 f4 ha hk
  have hp : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "c_2") (.idxE (.callE "lanes_"
      [.expA (.caseE "%X%" (.tupE [.subE (.varE "nt") numtypeT (.varT "lanetype" []),
        .varE "M"])), .expA (.varE "c_1")]) (.projE (.uncaseE (.varE "i") "%") 0)))
      (.bool true) :=
    evalExp_cmpE_iff.2 ⟨c₂, c₂, evalExp_var f5, hl, by simp [cmpValues]⟩
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) einstr)
      (evalExp_list1 (evalExp_constVar f2 f5)))
    (prems_one (.ifPr hp))

/-- `Step_pure/vextract_lane-pack` (rule 72). -/
theorem spure_vextractLanePack {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 72 vextractLanePackRule) {c₁ pt M sx c₂ l n : Value}
    {k : Nat} {ls : List Value} (hc₁ : TypedV env vecT c₁)
    (hpt : TypedV env (.varT "packtype" []) pt) (hM : TypedV env (.varT "M" []) M)
    (hsx : TypedV env (.varT "sx" []) sx) (hi : TypedV env (.varT "laneidx" []) (pctV k))
    (hc₂ : TypedV env i32T c₂)
    (ha : Applies env "lanes_" [.val (.case "%X%" (.tuple [pt, M])), .val c₁] (.list ls))
    (hk : ls[k]? = some l) (hn : Applies env "psize" [.val pt] n)
    (he : Applies env "extend__" [.val n, .val (.num (.natN 32)), .val sx, .val l] c₂) :
    SPure env [vconstV c₁, .case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [pt, M]),
      .opt (some sx), pctV k])] [constV i32V c₂] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("pt", pt), ("M", M), ("sx", sx), ("i", pctV k),
    ("c_2", c₂)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "pt" = some pt := rfl
  have f3 : ρ.findVal? "M" = some M := rfl
  have f4 : ρ.findVal? "sx" = some sx := rfl
  have f5 : ρ.findVal? "i" = some (pctV k) := rfl
  have f6 : ρ.findVal? "c_2" = some c₂ := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "pt" (.varT "packtype" []),
      .expP "M" (.varT "M" []), .expP "sx" (.varT "sx" []), .expP "i" (.varT "laneidx" []),
      .expP "c_2" i32T] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hpt ρ hρ) (QuantsOk.cons f3 (hM ρ hρ)
      (QuantsOk.cons f4 (hsx ρ hρ) (QuantsOk.cons f5 (hi ρ hρ) (QuantsOk.cons f6 (hc₂ ρ hρ)
      QuantsOk.nil)))))
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.subE (.varE "pt") (.varT "packtype" [])
      (.varT "lanetype" []), .varE "M"])) (.case "%X%" (.tuple [pt, M])) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var f2)) (evalExp_var f3))
  have esx : EvalExp env ρ (.optE (some (.varE "sx"))) (.opt (some sx)) := by
    obtain ⟨m, hm⟩ := evalExp_var (env := env) f4
    exact ⟨m + 1, by simp [evalExp, hm]⟩
  have einstr : EvalExp env ρ (.caseE "VEXTRACT_LANE" (.tupE [.caseE "%X%" (.tupE
      [.subE (.varE "pt") (.varT "packtype" []) (.varT "lanetype" []), .varE "M"]),
      .optE (some (.varE "sx")), .varE "i"]))
      (.case "VEXTRACT_LANE" (.tuple [.case "%X%" (.tuple [pt, M]), .opt (some sx), pctV k])) :=
    evalExp_case (evalExp_tup3 esh esx (evalExp_var f5))
  have hl : EvalExp env ρ (.idxE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "pt") (.varT "packtype" []) (.varT "lanetype" []), .varE "M"])),
      .expA (.varE "c_1")]) (.projE (.uncaseE (.varE "i") "%") 0)) l :=
    evalExp_laneAt rfl f2 f3 f1 f5 ha hk
  have hps : EvalExp env ρ (.callE "psize" [.expA (.varE "pt")]) n :=
    evalExp_call rfl (evalArgs_var f2 Equiv.evalArgs_nil) hn
  have hargs : EvalArgs env ρ [.expA (.callE "psize" [.expA (.varE "pt")]),
      .expA (.numE (.natN 32)), .expA (.varE "sx"), .expA (.idxE (.callE "lanes_"
        [.expA (.caseE "%X%" (.tupE [.subE (.varE "pt") (.varT "packtype" [])
          (.varT "lanetype" []), .varE "M"])), .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") 0))]
      [.val n, .val (.num (.natN 32)), .val sx, .val l] :=
    Equiv.evalArgs_cons hps (Equiv.evalArgs_cons (evalExp_numE_iff.2 rfl)
      (evalArgs_var f4 (Equiv.evalArgs_cons hl Equiv.evalArgs_nil)))
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) einstr)
      (evalExp_list1 (evalExp_constI32 f6)))
    (prems_one (.ifPr (evalExp_eq_call f6 rfl hargs he)))

/-! ## `VectorStep.vecExtractLane`, forward -/

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgree env P) (Fy : FloatTyping env)
  {s : Store H} {f : Frame}

include T hr V Ty A Fy

/-- The unpacked case (rule 71): shapes whose lanes are 32 or 64 bits wide. -/
theorem fwd_vecExtractLaneNum (sh : Shape) (i : LaneIdx) (a : V128) (hi : i.val < sh.lanes)
    (hw : 32 ≤ sh.laneWidth) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane sh none i)]⟩
      ⟨s, f, [(Val.num ⟨sh.unpacked, vecExtractLane sh none i.val a⟩).toAdmin]⟩ := by
  obtain ⟨ls, ha, hk⟩ := A.extractNum sh a i.val hi hw
  rcases sh with sh | sh <;> cases sh
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i32)) (Ty.dim (.int .i32x4)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i32, _⟩)
      ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.int .i64)) (Ty.dim (.int .i64x2)) (Ty.laneidx i) (Fy.num "nt" ⟨.int .i64, _⟩)
      ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f32)) (Ty.dim (.float .f32x4)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f32, _⟩) ha hk)
  · exact fwd_of_spure T hr (spure_vextractLaneNum V.vextractLaneNum (Ty.vec a)
      (Fy.numtype (.float .f64)) (Ty.dim (.float .f64x2)) (Ty.laneidx i)
      (Fy.num "nt" ⟨.float .f64, _⟩) ha hk)

omit Fy in
/-- The packed case (rule 72): integer shapes with 8- or 16-bit lanes. -/
theorem fwd_vecExtractLanePack (sh : IntShape) (sx : Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes) (hw : sh.laneWidth < 32) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane (.int sh) (some sx) i)]⟩
      ⟨s, f, [(Val.num ⟨(Shape.int sh).unpacked,
        vecExtractLane (.int sh) (some sx) i.val a⟩).toAdmin]⟩ := by
  obtain ⟨ls, l, n, ha, hk, hn', he⟩ := A.extractPack sh sx a i.val hi hw
  cases sh
  · exact fwd_of_spure T hr (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i8x16)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact fwd_of_spure T hr (spure_vextractLanePack V.vextractLanePack (Ty.vec a)
      (Ty.packtype _ hw) (Ty.dim (.int .i16x8)) (Ty.sx sx) (Ty.laneidx i) (Ty.i32 _) ha hk hn' he)
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- `VectorStep.vecExtractLane`, forward: rule 71 or 72, by the typing of the instruction. -/
theorem fwd_vecExtractLane (sh : Shape) (sx : Option Signedness) (i : LaneIdx) (a : V128)
    (hi : i.val < sh.lanes) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecExtractLane sh sx i)]⟩
      ⟨s, f, [(Val.num ⟨sh.unpacked, vecExtractLane sh sx i.val a⟩).toAdmin]⟩ := by
  intro hc hc'
  have hty : InstrTyped env (.vecExtractLane sh sx i) := typed_last2 T (typed_code T hc)
  have hsx : sx = none ↔ 32 ≤ sh.laneWidth := Ty.extractSx sh sx i hty
  cases sx with
  | none => exact fwd_vecExtractLaneNum T hr V Ty A Fy sh i a hi (hsx.1 rfl) hc hc'
  | some x =>
      have hw : ¬ 32 ≤ sh.laneWidth := fun h => by cases hsx.2 h
      cases sh with
      | int sh =>
          exact fwd_vecExtractLanePack T hr V Ty A sh x i a hi (by
            simp only [Shape.laneWidth] at hw; omega) hc hc'
      | float sh => cases sh <;> exact absurd (by decide) hw

end

/-! ## Lane replacement -/

/-- A list update at an index the scope denotes. -/
theorem pathSet_idxRoot {env : Env} {ρ : VarEnv} {v w u : Value} {e : Exp} {k : Nat}
    (he : EvalExp env ρ e (.num (.natN k))) (hs : v.setIdx k w = some u) :
    PathSet env ρ v (.idxP .rootP e) w u := by
  obtain ⟨m, hm⟩ := he
  refine ⟨m + 2, ?_⟩
  have hm' : evalExp (m + 1) env ρ e = .ok (.num (.natN k)) := evalExp_ok_of_le (by omega) hm
  simp [pathSet, pathGet, hm', hs, Value.asNat?, Res.ofOption]

/-- Every shape is `%X%` of its lane type and lane count. -/
theorem shapeV_eq (sh : Shape) :
    shapeV sh = .case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]) := by
  cases sh <;> rfl

/-- `Step_pure/vreplace_lane` (rule 73). -/
theorem spure_vreplaceLane {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 73 vreplaceLaneRule)
    {c₁ lnn nt c₂ M c l u : Value} {k : Nat} {ls : List Value} (hc₁ : TypedV env vecT c₁)
    (hlnn : TypedV env (.varT "Lnn" []) lnn)
    (hc₂ : TypedDep env "Lnn" lnn (.varT "num_" [.expA (.callE "lunpack" [.expA (.varE "Lnn")])])
      c₂)
    (hM : TypedV env (.varT "M" []) M) (hi : TypedV env (.varT "laneidx" []) (pctV k))
    (hc : TypedV env vecT c) (hu : Applies env "lunpack" [.val lnn] nt)
    (hl : Applies env "lanes_" [.val (.case "%X%" (.tuple [lnn, M])), .val c₁] (.list ls))
    (hp : Applies env "lpacknum_" [.val lnn, .val c₂] l)
    (hs : (Value.list ls).setIdx k l = some u)
    (hinv : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [lnn, M])), .val u] c) :
    SPure env [vconstV c₁, constV nt c₂,
      .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [lnn, M]), pctV k])] [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("Lnn", lnn), ("c_2", c₂), ("M", M),
    ("i", pctV k), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "Lnn" = some lnn := rfl
  have f3 : ρ.findVal? "c_2" = some c₂ := rfl
  have f4 : ρ.findVal? "M" = some M := rfl
  have f5 : ρ.findVal? "i" = some (pctV k) := rfl
  have f6 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "Lnn" (.varT "Lnn" []),
      .expP "c_2" (.varT "num_" [.expA (.callE "lunpack" [.expA (.varE "Lnn")])]),
      .expP "M" (.varT "M" []), .expP "i" (.varT "laneidx" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hlnn ρ hρ) (QuantsOk.cons f3 (hc₂ ρ hρ f2)
      (QuantsOk.cons f4 (hM ρ hρ) (QuantsOk.cons f5 (hi ρ hρ) (QuantsOk.cons f6 (hc ρ hρ)
      QuantsOk.nil)))))
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]))
      (.case "%X%" (.tuple [lnn, M])) :=
    evalExp_op2 f2 f4
  have enum : EvalExp env ρ (.caseE "CONST" (.tupE [.callE "lunpack" [.expA (.varE "Lnn")],
      .varE "c_2"])) (constV nt c₂) :=
    evalExp_case (evalExp_tup2 (evalExp_call rfl (evalArgs_var f2 Equiv.evalArgs_nil) hu)
      (evalExp_var f3))
  have elanes : EvalExp env ρ (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.varE "Lnn",
      .varE "M"])), .expA (.varE "c_1")]) (.list ls) :=
    evalExp_call rfl (Equiv.evalArgs_cons esh (evalArgs_var f1 Equiv.evalArgs_nil)) hl
  have epack : EvalExp env ρ (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_2")]) l :=
    evalExp_call rfl (evalArgs_var f2 (evalArgs_var f3 Equiv.evalArgs_nil)) hp
  have eidx : EvalExp env ρ (.projE (.uncaseE (.varE "i") "%") 0) (.num (.natN k)) :=
    evalExp_pctFst_iff.2 ⟨[], f5⟩
  have eupd : EvalExp env ρ (.updE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.varE "Lnn",
      .varE "M"])), .expA (.varE "c_1")]) (.idxP .rootP (.projE (.uncaseE (.varE "i") "%") 0))
      (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_2")])) u :=
    evalExp_updE_iff.2 ⟨_, _, elanes, epack, pathSet_idxRoot eidx hs⟩
  have hargs : EvalArgs env ρ [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])),
      .expA (.updE (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])),
        .expA (.varE "c_1")]) (.idxP .rootP (.projE (.uncaseE (.varE "i") "%") 0))
        (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_2")]))]
      [.val (.case "%X%" (.tuple [lnn, M])), .val u] :=
    Equiv.evalArgs_cons esh (Equiv.evalArgs_cons eupd Equiv.evalArgs_nil)
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list3 (evalExp_vconst f1) enum
        (evalExp_case (evalExp_tup2 esh (evalExp_var f5))))
      (evalExp_list1 (evalExp_vconst f6)))
    (prems_one (.ifPr (evalExp_eq_call f6 rfl hargs hinv)))

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgree env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecReplaceLane`, forward (`Step_pure/vreplace_lane`). -/
theorem fwd_vecReplaceLane (sh : Shape) (i : LaneIdx) (a : V128) (x : BitVec sh.unpacked.width)
    (hi : i.val < sh.lanes) :
    FwdP env hn ⟨s, f, [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)]⟩ ⟨s, f, [vconst (vecReplaceLane sh i.val a x)]⟩ := by
  obtain ⟨ls, l, u, hu, hl, hp, hs, hinv⟩ := A.replaceLane sh a i.val x hi
  have hl' : Applies env "lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes])),
      .val (vecV a)] (.list ls) := shapeV_eq sh ▸ hl
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val u] (vecV (vecReplaceLane sh i.val a x)) := shapeV_eq sh ▸ hinv
  have hsp : SPure env [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
        pctV i.val])] [vconstV (vecV (vecReplaceLane sh i.val a x))] :=
    spure_vreplaceLane V.vreplaceLane (Ty.vec a) (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh)
      (Ty.laneidx i) (Ty.vec _) hu hl' hp hs hinv'
  have e₁ : adminsToV [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin,
      .plain (.vecReplaceLane sh i)] =
      [vconstV (vecV a), constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]),
          pctV i.val])] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact fwd_of_spure T hr (e₁ ▸ hsp)

end

end Silmaril.Wasm.SpecTec.Sim.Vec
