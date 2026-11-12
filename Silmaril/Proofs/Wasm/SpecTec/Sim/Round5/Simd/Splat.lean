module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Replace

/-!
# Round 5: `vsplat` (rule 70), backward

At the concrete builtins, `Step_pure/vsplat` fires only on `[c, vecSplat sh]` with `c` a numeral
of `sh`'s unpacked type (`$lunpack` decides it), and produces `vecSplat sh x`: the premise's
`$lpacknum_(Lnn, c_1)^M` is `M` copies of the wrapped lane (evaluation is deterministic,
`EvalExp.unique`), whose `$inv_lanes_` is the splat (`lanesV_vecSplat`, `applies_invLanes`).
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
open Round4Int (BI)

variable {H : Type}

/-- `vecInstrV?` at `VSPLAT`. -/
theorem vecInstrV?_vsplat {i : Instr} {x : Value}
    (h : Vec.vecInstrV? i = some (.case "VSPLAT" x)) :
    ∃ sh, i = .vecSplat sh ∧ x = Vec.shapeV sh := by
  cases i <;> simp [Vec.vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- The rule's left-hand side, inverted. -/
theorem inv_vsplatLhs {env : Env} {ρ : VarEnv} {xs : List Value} {w : Value}
    (he : EvalExp env ρ (.tupE [.listE [.caseE "CONST" (.tupE [.callE "lunpack"
      [.expA (.varE "Lnn")], .varE "c_1"]), .caseE "VSPLAT" (.caseE "%X%" (.tupE [.varE "Lnn",
      .varE "M"]))], .listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"])]])
      (.tuple [.list xs, w])) :
    ∃ ntv c₁ lnn Mv c, xs = [.case "CONST" (.tuple [ntv, c₁]),
      .case "VSPLAT" (.case "%X%" (.tuple [lnn, Mv]))] ∧ w = .list [vconstV c] ∧
      EvalExp env ρ (.callE "lunpack" [.expA (.varE "Lnn")]) ntv ∧
      ρ.findVal? "c_1" = some c₁ ∧ ρ.findVal? "Lnn" = some lnn ∧ ρ.findVal? "M" = some Mv ∧
      ρ.findVal? "c" = some c := by
  obtain ⟨l, r, hv, hl, hr⟩ := Vec.inv_tup2 he
  obtain ⟨x₁, x₂, rfl, h₁, h₂⟩ := Vec.inv_list2 hl
  obtain ⟨p₁, hp₁, rfl⟩ := evalExp_caseE_iff.1 h₁
  obtain ⟨ntv, c₁, rfl, hnt, hc₁⟩ := Vec.inv_tup2 hp₁
  obtain ⟨p₂, hp₂, rfl⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨lnn, Mv, rfl, fl, fM⟩ := Vec.inv_op2 hp₂
  obtain ⟨z, rfl, hz⟩ := Vec.inv_list1 hr
  obtain ⟨c, rfl, fc⟩ := Vec.inv_vconst hz
  obtain ⟨hxs, hw⟩ := Vec.tuple2_inj hv
  exact ⟨ntv, c₁, lnn, Mv, c, Value.list.inj hxs, hw, hnt, evalExp_varE_iff.1 hc₁, fl, fM, fc⟩

/-- **`Step_pure/vsplat` (rule 70), backward**, at the concrete builtins. -/
theorem bwd_vsplat {P : Profile} {hn : H → String} {host : HostSemantics H}
    {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" 70 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := fires_if1Q (Vec.hasVectorRules_simEnv _).vsplat hf
  obtain ⟨ntv, c₁, lnn, Mv, c, hxs, rfl, hnt, f₁, fl, fM, fc⟩ := inv_vsplatLhs he
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := Vec.adminsToV_eq_two hxs
  obtain ⟨⟨t, x⟩, rfl, rfl, rfl⟩ := dec_numConst h₁
  obtain ⟨ins, rfl, hins⟩ := BwdStep.vecDecode.vinstr a₂ "VSPLAT" _ (by simp [Vec.vecTags]) h₂
  obtain ⟨sh, rfl, hx⟩ := vecInstrV?_vsplat hins
  obtain ⟨hl, hM⟩ := shapeV_inv hx.symm
  have fl' : (VarEnv.empty.bindVals σ).findVal? "Lnn" = some (Vec.laneTypeV sh) :=
    fl.trans (congrArg some hl)
  have fM' : (VarEnv.empty.bindVals σ).findVal? "M" = some (pctV sh.lanes) :=
    fM.trans (congrArg some hM)
  have hu : Applies (simEnv (BI P hn host)) "lunpack" [.val (Vec.laneTypeV sh)]
      (Vec.numTypeV t) :=
    Vec.inv_call rfl (Vec.evalArgs_var fl' Equiv.evalArgs_nil) hnt
  have ht : t = sh.unpacked :=
    numTypeV_injective (Equiv.ExecNumeric.Applies.unique hu (applies_lunpack sh))
  subst ht
  have hsh : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])) (Vec.shapeV sh) :=
    hx ▸ Vec.evalExp_op2 fl fM
  have hpack : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_1")])
      (laneV sh (x.setWidth sh.laneWidth)) :=
    Vec.evalExp_call rfl (Vec.evalArgs_var fl' (Vec.evalArgs_var f₁ Equiv.evalArgs_nil))
      (applies_lpacknum (Prims.floatB_builtins hn host) sh x)
  have hrep : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.iterE (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_1")])
        (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) []))
      (.list (lanesV sh (vecSplat sh x))) := by
    rw [lanesV_vecSplat]
    exact Vec.evalExp_iterListN_nodom (evalExp_pctFst_iff.2 ⟨[], fM'⟩) hpack
  have hargs : EvalArgs (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      [.expA (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])),
        .expA (.iterE (.callE "lpacknum_" [.expA (.varE "Lnn"), .expA (.varE "c_1")])
          (.mk (.listN (.projE (.uncaseE (.varE "M") "%") 0) none) []))]
      [.val (Vec.shapeV sh), .val (.list (lanesV sh (vecSplat sh x)))] :=
    Equiv.evalArgs_cons hsh (Equiv.evalArgs_cons hrep Equiv.evalArgs_nil)
  have hc : c = Vec.vecV (vecSplat sh x) :=
    Vec.inv_eq_call fc rfl hargs (applies_invLanes P hn host sh _) hp
  refine ⟨[vconst (vecSplat sh x)], ?_, .vector (.vecSplat sh x)⟩
  rw [hc]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
