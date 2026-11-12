module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.ExtractPack
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Pack

/-!
# Round 5: `vreplace_lane` (rule 73), backward

At the concrete builtins, `Step_pure/vreplace_lane` fires only on
`[v128.const b, c, vecReplaceLane sh li]` with `c` a numeral of `sh`'s unpacked type (`$lunpack`
decides it, `applies_lunpack`) and `li` in range (the list update succeeds, `pathSet_idxRoot_inv`),
and produces `vecReplaceLane sh li b x` (`lanesV_vecReplaceLane`, `applies_invLanes`).
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

/-! ## Decoding -/

/-- `numTypeV` is injective. -/
theorem numTypeV_injective : Function.Injective Vec.numTypeV := by
  intro s t h
  rcases s with s | s <;> rcases t with t | t <;> cases s <;> cases t <;>
    simp_all [Vec.numTypeV, caseNilV]

/-- **A `CONST nt c` image is a Core numeric constant.** -/
theorem dec_numConst {a : Admin} {nt c : Value}
    (h : adminToV a = .case "CONST" (.tuple [nt, c])) :
    ∃ n : NumVal, a = (Val.num n).toAdmin ∧ nt = Vec.numTypeV n.type ∧ c = numV n := by
  cases a with
  | plain i =>
    rcases IntNumeric.dec_const h with ⟨t, b, rfl, hp⟩ | ⟨t, b, rfl⟩
    · have hp' : nt = IntNumeric.ntV t ∧ c = Equiv.bvV b := by simpa using hp
      refine ⟨⟨.int t, b⟩, rfl, ?_, hp'.2⟩
      rw [hp'.1]
      cases t <;> rfl
    · have h' : Value.case "CONST" (.tuple [Vec.numTypeV (.float t), floatV t b]) =
          .case "CONST" (.tuple [nt, c]) := (Vec.instrToV_floatConst t b).symm.trans h
      have hp' : Vec.numTypeV (.float t) = nt ∧ floatV t b = c := by simpa using h'
      exact ⟨⟨.float t, b⟩, by cases t <;> rfl, hp'.1.symm, hp'.2.symm⟩
  | ref r => cases r <;> simp [adminToV, Equiv.RuntimeBridge.refToValue] at h
  | _ => simp [adminToV, caseNilV] at h

/-- `vecInstrV?` at `VREPLACE_LANE`. -/
theorem vecInstrV?_vreplaceLane {i : Instr} {x : Value}
    (h : Vec.vecInstrV? i = some (.case "VREPLACE_LANE" x)) :
    ∃ sh li, i = .vecReplaceLane sh li ∧ x = .tuple [Vec.shapeV sh, Vec.laneIdxV li] := by
  cases i <;> simp [Vec.vecInstrV?] at h
  exact ⟨_, _, rfl, h.symm⟩

/-- A list update at an index the scope denotes, inverted. -/
theorem pathSet_idxRoot_inv {env : Env} {ρ : VarEnv} {v w u : Value} {e : Exp}
    (h : PathSet env ρ v (.idxP .rootP e) w u) :
    ∃ k, EvalExp env ρ e (.num (.natN k)) ∧ v.setIdx k w = some u := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | _ | m
  · simp [pathSet] at hn
  · simp [pathSet, pathGet] at hn
  · simp only [pathSet, pathGet, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
    obtain ⟨v', hv', iv, hiv, k, hk, u', hu', hpu⟩ := hn
    have hvv : v' = v := (Except.ok.inj hv').symm
    have hiv' : iv = .num (.natN k) := by
      cases iv with
      | num m => cases m <;> simp_all [Value.asNat?]
      | _ => simp [Value.asNat?] at hk
    have hu : u' = u := Except.ok.inj hpu
    exact ⟨k, ⟨m + 1, hiv' ▸ hiv⟩, hvv ▸ hu ▸ hu'⟩

/-- The rule's left-hand side, inverted. -/
theorem inv_vreplaceLhs {env : Env} {ρ : VarEnv} {xs : List Value} {w : Value}
    (he : EvalExp env ρ (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []),
      .varE "c_1"]), .caseE "CONST" (.tupE [.callE "lunpack" [.expA (.varE "Lnn")], .varE "c_2"]),
      .caseE "VREPLACE_LANE" (.tupE [.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"]), .varE "i"])],
      .listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"])]])
      (.tuple [.list xs, w])) :
    ∃ c₁ ntv c₂ lnn Mv iv c, xs = [vconstV c₁, .case "CONST" (.tuple [ntv, c₂]),
      .case "VREPLACE_LANE" (.tuple [.case "%X%" (.tuple [lnn, Mv]), iv])] ∧ w = .list [vconstV c] ∧
      ρ.findVal? "c_1" = some c₁ ∧ EvalExp env ρ (.callE "lunpack" [.expA (.varE "Lnn")]) ntv ∧
      ρ.findVal? "c_2" = some c₂ ∧ ρ.findVal? "Lnn" = some lnn ∧ ρ.findVal? "M" = some Mv ∧
      ρ.findVal? "i" = some iv ∧ ρ.findVal? "c" = some c := by
  obtain ⟨l, r, hv, hl, hr⟩ := Vec.inv_tup2 he
  obtain ⟨x₁, x₂, x₃, rfl, h₁, h₂, h₃⟩ := Vec.inv_list3 hl
  obtain ⟨c₁, rfl, f₁⟩ := Vec.inv_vconst h₁
  obtain ⟨p₂, hp₂, rfl⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨ntv, c₂, rfl, hnt, hc₂⟩ := Vec.inv_tup2 hp₂
  obtain ⟨p₃, hp₃, rfl⟩ := evalExp_caseE_iff.1 h₃
  obtain ⟨shv, iv, rfl, hsh, hi⟩ := Vec.inv_tup2 hp₃
  obtain ⟨lnn, Mv, rfl, fl, fM⟩ := Vec.inv_op2 hsh
  obtain ⟨z, rfl, hz⟩ := Vec.inv_list1 hr
  obtain ⟨c, rfl, fc⟩ := Vec.inv_vconst hz
  obtain ⟨hxs, hw⟩ := Vec.tuple2_inj hv
  exact ⟨c₁, ntv, c₂, lnn, Mv, iv, c, Value.list.inj hxs, hw, f₁, hnt,
    evalExp_varE_iff.1 hc₂, fl, fM, evalExp_varE_iff.1 hi, fc⟩

/-- **`Step_pure/vreplace_lane` (rule 73), backward**, at the concrete builtins. -/
theorem bwd_vreplaceLane {P : Profile} {hn : H → String} {host : HostSemantics H}
    {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" 73 (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨σ, -, he, hp⟩ := fires_if1Q (Vec.hasVectorRules_simEnv _).vreplaceLane hf
  obtain ⟨c₁, ntv, c₂, lnn, Mv, iv, c, hxs, rfl, f₁, hnt, f₂, fl, fM, fi, fc⟩ :=
    inv_vreplaceLhs he
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Vec.adminsToV_eq_three hxs
  obtain ⟨b, rfl, rfl⟩ := BwdStep.vecDecode.vconst a₁ c₁ h₁
  obtain ⟨⟨t, x⟩, rfl, rfl, rfl⟩ := dec_numConst h₂
  obtain ⟨ins, rfl, hins⟩ :=
    BwdStep.vecDecode.vinstr a₃ "VREPLACE_LANE" _ (by simp [Vec.vecTags]) h₃
  obtain ⟨sh, li, rfl, hx⟩ := vecInstrV?_vreplaceLane hins
  have hx' : Vec.shapeV sh = .case "%X%" (.tuple [lnn, Mv]) ∧ Vec.laneIdxV li = iv := by
    simpa using hx.symm
  have hl : lnn = Vec.laneTypeV sh := (shapeV_inv hx'.1).1
  have fl' : (VarEnv.empty.bindVals σ).findVal? "Lnn" = some (Vec.laneTypeV sh) :=
    fl.trans (congrArg some hl)
  have hu : Applies (simEnv (BI P hn host)) "lunpack" [.val (Vec.laneTypeV sh)]
      (Vec.numTypeV t) :=
    Vec.inv_call rfl (Vec.evalArgs_var fl' Equiv.evalArgs_nil) hnt
  have ht : t = sh.unpacked :=
    numTypeV_injective (Equiv.ExecNumeric.Applies.unique hu (applies_lunpack sh))
  subst ht
  have hsh : EvalExp (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
      (.caseE "%X%" (.tupE [.varE "Lnn", .varE "M"])) (Vec.shapeV sh) :=
    hx'.1 ▸ Vec.evalExp_op2 fl fM
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 hp
  have hc : v₁ = c := Option.some.inj ((evalExp_varE_iff.1 e₁).symm.trans fc)
  have h12 : v₁ = v₂ := by simpa [cmpValues] using hcmp
  obtain ⟨ws, -, -, -, hargs, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 e₂)
  have happ : Applies (simEnv (BI P hn host)) "inv_lanes_" ws v₂ :=
    (Equiv.ExecNumeric.applies_iff_callDef rfl hargs).2 (evalExp_callE_iff.1 e₂)
  obtain ⟨sv, ws₁, rfl, hsv, hargs₁⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs
  obtain ⟨uv, ws₂, rfl, huv, hargs₂⟩ := Equiv.ExecVector.evalArgs_expA_cons_iff.1 hargs₁
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs₂
  have hsv' : sv = Vec.shapeV sh := EvalExp.unique hsv hsh
  obtain ⟨lv, pv, hlv, hpv, hps⟩ := evalExp_updE_iff.1 huv
  have hlv' : lv = .list (lanesV sh b) := Equiv.ExecNumeric.Applies.unique
    (Vec.inv_call rfl (Equiv.evalArgs_cons hsh (Vec.evalArgs_var f₁ Equiv.evalArgs_nil)) hlv)
    (applies_lanes P hn host sh b)
  have hpv' : pv = laneV sh (x.setWidth sh.laneWidth) := Equiv.ExecNumeric.Applies.unique
    (Vec.inv_call rfl (Vec.evalArgs_var fl' (Vec.evalArgs_var f₂ Equiv.evalArgs_nil)) hpv)
    (applies_lpacknum (Prims.floatB_builtins hn host) sh x)
  obtain ⟨k, hk, hset⟩ := pathSet_idxRoot_inv hps
  obtain ⟨rest, hrest⟩ := evalExp_pctFst_iff.1 hk
  have hkv : k = li.val := by
    rw [fi, ← hx'.2] at hrest
    simp only [Vec.laneIdxV, pctV, Option.some.injEq, Value.case.injEq, Value.tuple.injEq,
      List.cons.injEq, Value.num.injEq, Num.natN.injEq, true_and] at hrest
    exact hrest.1.symm
  have hset' : li.val < (lanesV sh b).length ∧
      .list ((lanesV sh b).set li.val (laneV sh (x.setWidth sh.laneWidth))) = uv := by
    rw [hlv', hpv', hkv] at hset
    simpa [Value.setIdx] using hset
  have hlt : li.val < sh.lanes := by simpa [lanesV, Shape.lanesOf] using hset'.1
  have huv' : uv = .list (lanesV sh (vecReplaceLane sh li.val b x)) := by
    rw [lanesV_vecReplaceLane]
    exact hset'.2.symm
  have hv₂ : v₂ = Vec.vecV (vecReplaceLane sh li.val b x) := Equiv.ExecNumeric.Applies.unique
    happ (hsv' ▸ huv' ▸ applies_invLanes P hn host sh _)
  refine ⟨[vconst (vecReplaceLane sh li.val b x)], ?_, .vector (.vecReplaceLane sh li b x hlt)⟩
  rw [← hc, h12, hv₂]
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
