module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Lanes
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Iter

/-!
# Family V: `vsplat` and `vtestop`, forward

The two vector rules whose premises iterate: `Step_pure/vsplat` (rule 70: `$lpacknum_(Lnn, c_1)^M`,
a domain-free iteration, and `$lunpack(Lnn)` in the conclusion) and `Step_pure/vtestop` (rule 64:
the lanes quantified as `i*`, then `$prod` of `$inez_` over them). Under the evaluator reading
both are dead at the pin (`Equiv.ExecVector.not_ruleFires_vsplat_pinned`,
`Equiv.ExecStepRules.not_ruleFires_vtestop_pinned`); under the declarative reading they fire.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vsplatRule vtestopRule vconstV
  evalExp_pctFst_iff)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.Execution (constV i32V caseNilV pctV iterPat)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

/-- The IL type `num_($lunpack(Lnn))`. -/
abbrev lunpackNumT : Typ := .varT "num_" [.expA (.callE "lunpack" [.expA (.varE "Lnn")])]

/-- The IL type `lane_($lanetype(Jnn X M))*`. -/
abbrev lanesT : Typ :=
  .iterT (.varT "lane_" [.expA (.callE "lanetype" [.expA (.caseE "%X%" (.tupE
    [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])]) .list

/-- `Step_pure/vsplat` (rule 70). -/
theorem spure_vsplat {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 70 vsplatRule)
    {lnn nt c₁ c l : Value} {k : Nat} (hlnn : TypedV env (.varT "Lnn" []) lnn)
    (hc₁ : TypedDep env "Lnn" lnn lunpackNumT c₁) (hM : TypedV env (.varT "M" []) (pctV k))
    (hc : TypedV env vecT c) (hu : Applies env "lunpack" [.val lnn] nt)
    (hp : Applies env "lpacknum_" [.val lnn, .val c₁] l)
    (hinv : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [lnn, pctV k])),
      .val (.list (List.replicate k l))] c) :
    SPure env [constV nt c₁, .case "VSPLAT" (.case "%X%" (.tuple [lnn, pctV k]))]
      [vconstV c] := by
  let ρ := VarEnv.empty.bindVals [("Lnn", lnn), ("c_1", c₁), ("M", pctV k), ("c", c)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "Lnn" = some lnn := rfl
  have f2 : ρ.findVal? "c_1" = some c₁ := rfl
  have f3 : ρ.findVal? "M" = some (pctV k) := rfl
  have f4 : ρ.findVal? "c" = some c := rfl
  have hq : QuantsOk env ρ [.expP "Lnn" (.varT "Lnn" []), .expP "c_1" lunpackNumT,
      .expP "M" (.varT "M" []), .expP "c" vecT] :=
    QuantsOk.cons f1 (hlnn ρ hρ) (QuantsOk.cons f2 (hc₁ ρ hρ f1) (QuantsOk.cons f3 (hM ρ hρ)
      (QuantsOk.cons f4 (hc ρ hρ) QuantsOk.nil)))
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]))
      (.case "%X%" (.tuple [lnn, pctV k])) :=
    evalExp_op2 f1 f3
  have enum : EvalExp env ρ (.caseE "CONST" (.tupE [.callE "lunpack" [.expA (.varE "Lnn")],
      .varE "c_1"])) (constV nt c₁) :=
    evalExp_case (evalExp_tup2 (evalExp_call rfl (evalArgs_var f1 Equiv.evalArgs_nil) hu)
      (evalExp_var f2))
  have epack : EvalExp env ρ (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_1")]) l :=
    evalExp_call rfl (evalArgs_var f1 (evalArgs_var f2 Equiv.evalArgs_nil)) hp
  have ek : EvalExp env ρ (.projE (.uncaseE (.varE "M") "%") 0) (.num (.natN k)) :=
    evalExp_pctFst_iff.2 ⟨[], f3⟩
  have erep : EvalExp env ρ (.iterE (.callE "lpacknum_" [.expA (.varE "Lnn"),
      .expA (.varE "c_1")]) (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) []))
      (.list (List.replicate k l)) :=
    evalExp_iterListN_nodom ek epack
  have hargs : EvalArgs env ρ [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])),
      .expA (.iterE (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_1")])
        (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) []))]
      [.val (.case "%X%" (.tuple [lnn, pctV k])), .val (.list (List.replicate k l))] :=
    Equiv.evalArgs_cons esh (Equiv.evalArgs_cons erep Equiv.evalArgs_nil)
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 enum (evalExp_case esh)) (evalExp_list1 (evalExp_vconst f4)))
    (prems_one (.ifPr (evalExp_eq_call f4 rfl hargs hinv)))

/-- `$inez_($jsizenn(Jnn), i)!%.0`, in the scope of one round of `vtestop`'s iteration. -/
theorem evalExp_inezLane {env : Env} {σ : VarEnv} {jnn jsz l : Value} {b : Nat}
    (hd₁ : σ.findDef? "inez_" = none) (hd₂ : σ.findDef? "jsizenn" = none)
    (hj : σ.findVal? "Jnn" = some jnn) (hi : σ.findVal? "i" = some l)
    (hjs : Applies env "jsizenn" [.val jnn] jsz)
    (hz : Applies env "inez_" [.val jsz, .val l] (pctV b)) :
    EvalExp env σ (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn" [.expA (.varE "Jnn")]),
      .expA (.varE "i")]) "%") 0) (.num (.natN b)) := by
  have ejs : EvalExp env σ (.callE "jsizenn" [.expA (.varE "Jnn")]) jsz :=
    evalExp_call hd₂ (evalArgs_var hj Equiv.evalArgs_nil) hjs
  have ez : EvalExp env σ (.callE "inez_" [.expA (.callE "jsizenn" [.expA (.varE "Jnn")]),
      .expA (.varE "i")]) (pctV b) :=
    evalExp_call hd₁ (Equiv.evalArgs_cons ejs (evalArgs_var hi Equiv.evalArgs_nil)) hz
  exact evalExp_projE_iff.2 ⟨[.num (.natN b)], evalExp_uncaseE_iff.2 ez, le_refl _, rfl⟩

/-- `Step_pure/vtestop` (rule 64). -/
theorem spure_vtestop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 64 vtestopRule)
    {c₁ jnn M jsz : Value} {r : Nat} {ls : List Value} {bs : List Nat}
    (hc₁ : TypedV env vecT c₁) (hj : TypedV env (.varT "Jnn" []) jnn)
    (hM : TypedV env (.varT "M" []) M) (hc : TypedV env i32T (pctV r))
    (hls : TypedDep2 env "Jnn" jnn "M" M lanesT (.list ls))
    (hl : Applies env "lanes_" [.val (.case "%X%" (.tuple [jnn, M])), .val c₁] (.list ls))
    (hjs : Applies env "jsizenn" [.val jnn] jsz)
    (hz : List.Forall₂ (fun l b => Applies env "inez_" [.val jsz, .val l] (pctV b)) ls bs)
    (hp : Applies env "prod" [.val (.list (bs.map fun b => .num (.natN b)))] (.num (.natN r))) :
    SPure env [vconstV c₁, .case "VTESTOP" (.tuple [.case "%X%" (.tuple [jnn, M]),
      caseNilV "ALL_TRUE"])] [constV i32V (pctV r)] := by
  let ρ := VarEnv.empty.bindVals [("c_1", c₁), ("Jnn", jnn), ("M", M), ("c", pctV r),
    ("i*", .list ls)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have f1 : ρ.findVal? "c_1" = some c₁ := rfl
  have f2 : ρ.findVal? "Jnn" = some jnn := rfl
  have f3 : ρ.findVal? "M" = some M := rfl
  have f4 : ρ.findVal? "c" = some (pctV r) := rfl
  have f5 : ρ.findVal? "i*" = some (.list ls) := rfl
  have hq : QuantsOk env ρ [.expP "c_1" vecT, .expP "Jnn" (.varT "Jnn" []),
      .expP "M" (.varT "M" []), .expP "c" i32T, .expP "i*" lanesT] :=
    QuantsOk.cons f1 (hc₁ ρ hρ) (QuantsOk.cons f2 (hj ρ hρ) (QuantsOk.cons f3 (hM ρ hρ)
      (QuantsOk.cons f4 (hc ρ hρ) (QuantsOk.cons f5 (hls ρ hρ f2 f3) QuantsOk.nil))))
  have esh : EvalExp env ρ (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" [])
      (.varT "lanetype" []), .varE "M"])) (.case "%X%" (.tuple [jnn, M])) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var f2)) (evalExp_var f3))
  have eall : EvalExp env ρ (.caseE "ALL_TRUE" (.tupE [])) (caseNilV "ALL_TRUE") :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_nil, rfl⟩)
  have elanes : EvalExp env ρ (.callE "lanes_" [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn")
      (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])), .expA (.varE "c_1")]) (.list ls) :=
    evalExp_call rfl (Equiv.evalArgs_cons esh (evalArgs_var f1 Equiv.evalArgs_nil)) hl
  have ei : EvalExp env ρ (iterPat "i" "i*") (.list ls) :=
    Equiv.Execution.evalExp_iterPat (by decide) f5
  have hp₁ : EvalExp env ρ (.cmpE .eqOp .boolT (iterPat "i" "i*") (.callE "lanes_"
      [.expA (.caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []),
        .varE "M"])), .expA (.varE "c_1")])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, ei, elanes, by simp [cmpValues]⟩
  have hround : List.Forall₂ (fun l w => EvalExp env (ρ.bindVals [("i", l)])
      (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn" [.expA (.varE "Jnn")]),
        .expA (.varE "i")]) "%") 0) w) ls (bs.map fun b => .num (.natN b)) :=
    List.forall₂_map_right_iff.2 (hz.imp fun _ _ hb => evalExp_inezLane rfl rfl rfl rfl hjs hb)
  have eit : EvalExp env ρ (.iterE (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn"
      [.expA (.varE "Jnn")]), .expA (.varE "i")]) "%") 0) (.mk .list [.mk "i" (.varE "i*")]))
      (.list (bs.map fun b => .num (.natN b))) :=
    evalExp_iterList1 f5 hround
  have eprod : EvalExp env ρ (.callE "prod" [.expA (.iterE (.projE (.uncaseE (.callE "inez_"
      [.expA (.callE "jsizenn" [.expA (.varE "Jnn")]), .expA (.varE "i")]) "%") 0)
      (.mk .list [.mk "i" (.varE "i*")]))]) (.num (.natN r)) :=
    evalExp_call rfl (Equiv.evalArgs_cons eit Equiv.evalArgs_nil) hp
  have hp₂ : EvalExp env ρ (.cmpE .eqOp .boolT (.projE (.uncaseE (.varE "c") "%") 0)
      (.callE "prod" [.expA (.iterE (.projE (.uncaseE (.callE "inez_" [.expA (.callE "jsizenn"
        [.expA (.varE "Jnn")]), .expA (.varE "i")]) "%") 0)
        (.mk .list [.mk "i" (.varE "i*")]))])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, evalExp_pctFst_iff.2 ⟨[], f4⟩, eprod, by simp [cmpValues]⟩
  exact dderives_of_ruleAt h _ hq
    (evalExp_tup2 (evalExp_list2 (evalExp_vconst f1) (evalExp_case (evalExp_tup2 esh eall)))
      (evalExp_list1 (evalExp_constI32 f4)))
    (prems_two (.ifPr hp₁) (.ifPr hp₂))

section

variable {H : Type} {env : Env} {hn : H → String} {P : Profile}
  (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 0 pureRule)
  (V : HasVectorRules env) (Ty : Round5.SimdTy.VecTypingL env) (A : VecAgree env P)
  {s : Store H} {f : Frame}

include T hr V Ty A

/-- `VectorStep.vecSplat`, forward (`Step_pure/vsplat`). -/
theorem fwd_vecSplat (sh : Shape) (x : BitVec sh.unpacked.width) :
    FwdP env hn ⟨s, f, [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]⟩
      ⟨s, f, [vconst (vecSplat sh x)]⟩ := by
  obtain ⟨l, hu, hp, hinv⟩ := A.splat sh x
  have hinv' : Applies env "inv_lanes_" [.val (.case "%X%" (.tuple [laneTypeV sh,
      pctV sh.lanes])), .val (.list (List.replicate sh.lanes l))] (vecV (vecSplat sh x)) :=
    shapeV_eq sh ▸ hinv
  have hsp : SPure env [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
      .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))]
      [vconstV (vecV (vecSplat sh x))] :=
    spure_vsplat V.vsplat (Ty.lnn sh) (Ty.numLunpack sh x) (Ty.dim sh) (Ty.vec _) hu hp hinv'
  have e₁ : adminsToV [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)] =
      [constV (numTypeV sh.unpacked) (numV ⟨sh.unpacked, x⟩),
        .case "VSPLAT" (.case "%X%" (.tuple [laneTypeV sh, pctV sh.lanes]))] := by
    simp only [adminsToV, adminToV_valNum]
    rw [← shapeV_eq]
    rfl
  exact fwd_of_spure T hr (e₁ ▸ hsp)

/-- `VectorStep.vecAllTrue`, forward (`Step_pure/vtestop`). -/
theorem fwd_vecAllTrue (sh : IntShape) (a : V128) :
    FwdP env hn ⟨s, f, [vconst a, .plain (.vecAllTrue sh)]⟩
      ⟨s, f, [constI32 (vecAllTrue sh a)]⟩ := by
  obtain ⟨ls, jsz, bs, hl, hjs, hz, hp⟩ := A.allTrue sh a
  exact fwd_of_spure T hr (spure_vtestop V.vtestop (Ty.vec a) (Ty.jnn sh) (Ty.dim (.int sh))
    (Ty.i32 _) (Ty.lanes sh a ls hl) hl hjs hz hp)

end

end Silmaril.Wasm.SpecTec.Sim.Vec
