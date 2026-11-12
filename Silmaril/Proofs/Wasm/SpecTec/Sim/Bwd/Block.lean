module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.ReturnCall

/-!
# Track backward: `block` and `loop` (`Step_read` 0, 1)

`bwd_block`, `bwd_loop` are the `Backward.read 0`/`1` fields, under family C's `CtrlDecode` and
`BlockInv` (`$blocktype_` read back into Core's `blockType?`; assumed). The `BLOCK`/`LOOP`
decoders are proved by a case split (`decode_block`, `decode_loop`). Both rules are dead under
the evaluator reading (a variable bound only by an `if` premise) and fire declaratively.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

set_option maxHeartbeats 4000000 in
/-- Only `block` is encoded with the tag `BLOCK`. -/
theorem instrToV_block {i : Instr} {w : Value} (h : instrToV i = .case "BLOCK" w) :
    ∃ bt body, i = .block bt body ∧ w = .tuple [Encode.toValue bt, .list (instrsToV body)] := by
  cases i
  all_goals try first
    | exact ⟨_, _, rfl, (Value.case.inj h).2.symm⟩
    | exact absurd (Value.case.inj h).1 (by decide)
    | (have h' : schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _) = _ := h
       obtain ⟨w', hw'⟩ := Exn.schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)
       rw [hw'] at h'
       exact absurd (Value.case.inj h').1 (by simp [Silmaril.Wasm.SpecTecEnc.encodeInstruction]))
  iterate 4 (all_goals (try (rename_i x; cases x)))
  all_goals first
    | exact absurd (Value.case.inj h).1 (by decide)
    | exact Value.noConfusion h

set_option maxHeartbeats 4000000 in
/-- Only `loop` is encoded with the tag `LOOP`. -/
theorem instrToV_loop {i : Instr} {w : Value} (h : instrToV i = .case "LOOP" w) :
    ∃ bt body, i = .loop bt body ∧ w = .tuple [Encode.toValue bt, .list (instrsToV body)] := by
  cases i
  all_goals try first
    | exact ⟨_, _, rfl, (Value.case.inj h).2.symm⟩
    | exact absurd (Value.case.inj h).1 (by decide)
    | (have h' : schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _) = _ := h
       obtain ⟨w', hw'⟩ := Exn.schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)
       rw [hw'] at h'
       exact absurd (Value.case.inj h').1 (by simp [Silmaril.Wasm.SpecTecEnc.encodeInstruction]))
  iterate 4 (all_goals (try (rename_i x; cases x)))
  all_goals first
    | exact absurd (Value.case.inj h).1 (by decide)
    | exact Value.noConfusion h

/-- An administrative instruction whose image is headed `BLOCK`. -/
theorem decode_block {a : Admin} {x : Value} (h : adminToV a = .case "BLOCK" x) :
    ∃ bt body, a = .plain (.block bt body) ∧
      x = .tuple [Encode.toValue bt, .list (instrsToV body)] := by
  cases a with
  | plain i =>
    obtain ⟨bt, body, rfl, hx⟩ := instrToV_block h
    exact ⟨bt, body, rfl, hx⟩
  | ref r =>
    cases r with
    | extern r => exact absurd (Value.case.inj h).1 (by decide)
    | _ => exact absurd (Value.case.inj h).1 (by decide)
  | _ => exact absurd (Value.case.inj h).1 (by decide)

/-- An administrative instruction whose image is headed `LOOP`. -/
theorem decode_loop {a : Admin} {x : Value} (h : adminToV a = .case "LOOP" x) :
    ∃ bt body, a = .plain (.loop bt body) ∧
      x = .tuple [Encode.toValue bt, .list (instrsToV body)] := by
  cases a with
  | plain i =>
    obtain ⟨bt, body, rfl, hx⟩ := instrToV_loop h
    exact ⟨bt, body, rfl, hx⟩
  | ref r =>
    cases r with
    | extern r => exact absurd (Value.case.inj h).1 (by decide)
    | _ => exact absurd (Value.case.inj h).1 (by decide)
  | _ => exact absurd (Value.case.inj h).1 (by decide)

/-- A two-argument call at bound variables, read back as `Applies`. -/
theorem applies_of_call2 {env : Env} {ρ : VarEnv} {x y₁ y₂ : IL.Id} {w₁ w₂ v : Value}
    (hd : ρ.findDef? x = none) (hy₁ : ρ.findVal? y₁ = some w₁) (hy₂ : ρ.findVal? y₂ = some w₂)
    (h : EvalExp env ρ (.callE x [.expA (.varE y₁), .expA (.varE y₂)]) v) :
    Applies env x [.val w₁, .val w₂] v :=
  (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy₁)
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy₂) (evalArgs_nil env ρ)))).2
    (evalExp_callE_iff.1 h)

/-- A triple, read back. -/
theorem tup3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) v) :
    ∃ w₁ w₂ w₃, EvalExp env ρ e₁ w₁ ∧ EvalExp env ρ e₂ w₂ ∧ EvalExp env ρ e₃ w₃ ∧
      v = .tuple [w₁, w₂, w₃] := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain ⟨w₃, ws'', h₃, hws'', rfl⟩ := evalExps_cons_iff.1 hws'
  obtain rfl := evalExps_nil_iff.1 hws''
  exact ⟨w₁, w₂, w₃, h₁, h₂, h₃, rfl⟩

/-- `%(t_1^m) ->_ [] %(t_2^n)`, read back: `m` and `n` are the lengths of `t_1*`, `t_2*`. -/
theorem blockTypePat_inv {env : Env} {ρ : VarEnv} {w : Value}
    (h : EvalExp env ρ (.caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]), .listE [],
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])])) w) :
    ∃ T₁ T₂, ρ.findVal? "m" = some (.num (.natN T₁.length)) ∧
      ρ.findVal? "n" = some (.num (.natN T₂.length)) ∧
      w = .case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
        .case "%" (.tuple [.list T₂])]) := by
  obtain ⟨v, hv, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u₁, u₂, u₃, h₁, h₂, h₃, rfl⟩ := tup3_inv hv
  obtain ⟨x₁, hx₁, rfl⟩ := pct1_inv h₁
  obtain ⟨x₃, hx₃, rfl⟩ := pct1_inv h₃
  obtain ⟨T₁, -, fm, rfl⟩ := Exn.evalExp_varN_inv (by decide) hx₁
  obtain ⟨T₂, -, fn, rfl⟩ := Exn.evalExp_varN_inv (by decide) hx₃
  have e₂ : u₂ = .list [] := EvalExp.unique h₂ evalExp_listNil
  exact ⟨T₁, T₂, fm, fn, by rw [e₂]⟩

/-- The left-hand side `z; instr*` of a `Step_read` rule, read back. -/
theorem cfg_inv {env : Env} {ρ : VarEnv} {e : Exp} {z z₀ : Value} {is : List Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", e])) (cfgV z₀ is))
    (fz : ρ.findVal? "z" = some z) : z = z₀ ∧ EvalExp env ρ e (.list is) := by
  obtain ⟨v, hv, hc⟩ := evalExp_caseE_iff.1 h
  obtain ⟨w₁, w₂, h₁, h₂, rfl⟩ := tup2_inv hv
  have e₁ : Value.tuple [z₀, .list is] = .tuple [w₁, w₂] := (Value.case.inj hc).2
  have e₂ := tuple2_inj e₁
  exact ⟨(EvalExp.unique (evalExp_var fz) h₁).trans e₂.1.symm, e₂.2 ▸ h₂⟩

section Bwd

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (D : CtrlDecode (simEnv B)) (Bi : BlockInv (simEnv B) hn)

include Bi in
/-- The premise of `block` and `loop`, read back into Core's `blockType?`. -/
theorem blockType_prem {s : Store H} {f : Frame} {ρ : VarEnv} {bt : BlockType}
    (hd : ρ.findDef? "blocktype_" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fb : ρ.findVal? "bt" = some (Encode.toValue bt))
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.callE "blocktype_" [.expA (.varE "z"), .expA (.varE "bt")])
      (.caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "m") none) [.mk "t_1" (.varE "t_1*")])]), .listE [],
        .caseE "%" (.tupE [.iterE (.varE "t_2")
          (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])]))) (.bool true)) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧
      ρ.findVal? "m" = some (.num (.natN t₁.length)) ∧
      ρ.findVal? "n" = some (.num (.natN t₂.length)) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e : v₁ = v₂ := by simpa [cmpValues] using hc
  obtain ⟨T₁, T₂, fm, fn, rfl⟩ := blockTypePat_inv h₂
  obtain ⟨t₁, t₂, hbt, h₁', h₂'⟩ := Bi.blocktype s f bt T₁ T₂ (e ▸ applies_of_call2 hd fz fb h₁)
  exact ⟨t₁, t₂, hbt, h₁' ▸ fm, h₂' ▸ fn⟩

include D Bi in
/-- `Backward.read 0` (`block`). -/
theorem bwd_block : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 0 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_readRules B).block hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨btv, fb, -⟩ := quant_of (x := "bt") (t := .varT "blocktype" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ei : EvalExp (simEnv B) _ (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  have hl₀ := cfg_inv (configV_eq hn ⟨s, f, code⟩ ▸ hl) fz
  obtain ⟨ws, fv, fm, hcode⟩ := valsN_cat hl₀.2
    (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei)))
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨l₀, a, rfl, h₀, ha⟩ := adminsToV_eq_snoc (Value.list.inj hcode)
  obtain ⟨vs, rfl, hlen⟩ := decode_vals D h₀ (ew ▸ htv)
  obtain ⟨bt, body, rfl, hx⟩ := decode_block ha
  have hbv : btv = Encode.toValue bt ∧ is = instrsToV body := by
    simpa only [Value.tuple.injEq, List.cons.injEq, Value.list.injEq, and_true] using hx
  obtain ⟨t₁, t₂, hbt, fm₁, fn₂⟩ :=
    blockType_prem B Bi rfl (hl₀.1 ▸ fz) (hbv.1 ▸ fb) (ifPrem (hp _ (.head _)))
  have hm : vs.length = t₁.length := hlen ▸ natN_inj (Option.some.inj (fm.symm.trans fm₁))
  have hw : w = .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₂.length), .list [],
      .list (ws ++ is)])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn₂)
      evalExp_listNil (evalExp_cat (evalExp_valsNPat (by decide) fm fv) ei))))
  have hw' : w = .list (adminsToV [.label t₂.length [] (vals vs ++ expression body)]) := by
    rw [hw, ← h₀, hbv.2, ← Exn.adminsToV_expression, ← adminsToV_append]
    rfl
  exact ⟨_, hw', .block hbt hm⟩

include D Bi in
/-- `Backward.read 1` (`loop`). -/
theorem bwd_loop : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 1 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_readRules B).loop hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨btv, fb, -⟩ := quant_of (x := "bt") (t := .varT "blocktype" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ei : EvalExp (simEnv B) _ (iterPat "instr" "instr*") (.list is) :=
    evalExp_iterPat (by decide) fi
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  have hl₀ := cfg_inv (configV_eq hn ⟨s, f, code⟩ ▸ hl) fz
  obtain ⟨ws, fv, fm, hcode⟩ := valsN_cat hl₀.2
    (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei)))
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  obtain ⟨l₀, a, rfl, h₀, ha⟩ := adminsToV_eq_snoc (Value.list.inj hcode)
  obtain ⟨vs, rfl, hlen⟩ := decode_vals D h₀ (ew ▸ htv)
  obtain ⟨bt, body, rfl, hx⟩ := decode_loop ha
  have hbv : btv = Encode.toValue bt ∧ is = instrsToV body := by
    simpa only [Value.tuple.injEq, List.cons.injEq, Value.list.injEq, and_true] using hx
  obtain ⟨t₁, t₂, hbt, fm₁, fn₂⟩ :=
    blockType_prem B Bi rfl (hl₀.1 ▸ fz) (hbv.1 ▸ fb) (ifPrem (hp _ (.head _)))
  have hm : vs.length = t₁.length := hlen ▸ natN_inj (Option.some.inj (fm.symm.trans fm₁))
  have hw : w = .list [.case "LABEL_%{%}%" (.tuple [.num (.natN t₁.length),
      .list [.case "LOOP" (.tuple [btv, .list is])], .list (ws ++ is)])] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fm₁)
      (evalExp_list1 (evalExp_case (evalExp_tup2 (evalExp_var fb) ei)))
      (evalExp_cat (evalExp_valsNPat (by decide) fm fv) ei))))
  have hw' : w = .list (adminsToV [.label t₁.length [.loop bt body]
      (vals vs ++ expression body)]) := by
    show w = .list [adminToV (.label t₁.length [.loop bt body] (vals vs ++ expression body))]
    rw [hw, ← h₀, hbv.1, hbv.2, adminToV_label, adminsToV_append, Exn.adminsToV_expression]
    rfl
  exact ⟨_, hw', .loop hbt hm⟩

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Bwd
