module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Generic
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms

/-!
# The control rules family C left open

`Backward` fields, at `simEnv B`, for rules whose inversion family C left open:

* `Step_pure` 8 (`br-label-zero`), 21 (`frame-vals`), 22 (`return-frame`): each needs the
  inversion of a counted iteration `val^n` (family X's `Exn.evalExp_valsNPat_inv`), which binds
  `n` to the length of `val*`;
* `Step_read` 8, 9, 10 (`return_call_ref-label`, `-handler`, `-frame-null`), which need the
  `RETURN_CALL_REF` decoder `RetDecode`.

All hold under family C's decoders `CtrlDecode` (undischarged, family E's job).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Helpers -/

/-- A concatenation of lists, read back. -/
theorem cat_list {a b : List Value} {v : Value} (h : Value.cat? (.list a) (.list b) = some v) :
    v = .list (a ++ b) :=
  (Option.some.inj h).symm

/-- `x^n ++ e` read back, when `e` denotes `l`: `n` is the length of `x*`. -/
theorem valsN_cat {env : Env} {ρ : VarEnv} {e : Exp} {l : List Value} {w : Value} {m : IL.Id}
    (h : EvalExp env ρ (.catE (valsNPat "val" "val*" m) e) w) (he : EvalExp env ρ e (.list l)) :
    ∃ ws, ρ.findVal? "val*" = some (.list ws) ∧ ρ.findVal? m = some (.num (.natN ws.length)) ∧
      w = .list (ws ++ l) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 h
  obtain ⟨ws, fv, fn, rfl⟩ := Exn.evalExp_valsNPat_inv (by decide) h₁
  have e₂ : v₂ = .list l := EvalExp.unique h₂ he
  exact ⟨ws, fv, fn, cat_list (e₂ ▸ hc)⟩

/-- An image split as `A ++ [x]`. -/
theorem adminsToV_eq_snoc {l : List Admin} {A : List Value} {x : Value}
    (h : adminsToV l = A ++ [x]) : ∃ l₁ a, l = l₁ ++ [a] ∧ adminsToV l₁ = A ∧ adminToV a = x := by
  obtain ⟨l₁, a, l₂, rfl, h₁, ha, h₂⟩ := adminsToV_eq_split (C := []) (by rw [h, List.append_nil])
  have e : l₂ = [] := by
    rw [adminsToV_eq_map] at h₂
    exact List.map_eq_nil_iff.1 h₂
  exact ⟨l₁, a, by rw [e, List.append_nil], h₁, ha⟩

/-- The parts of a decoded label image. -/
theorem label_parts {k : Nat} {cont : List Instr} {body : List Admin} {n c b : Value}
    (h : adminToV (.label k cont body) = .case "LABEL_%{%}%" (.tuple [n, c, b])) :
    n = .num (.natN k) ∧ c = .list (instrsToV cont) ∧ b = .list (adminsToV body) := by
  simp only [adminToV_label, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- The parts of a decoded handler image. -/
theorem handler_parts {k : Nat} {cs : List Catch} {body : List Admin} {n c b : Value}
    (h : adminToV (.handler k cs body) = .case "HANDLER_%{%}%" (.tuple [n, c, b])) :
    n = .num (.natN k) ∧ c = .list (cs.map Encode.toValue) ∧ b = .list (adminsToV body) := by
  simp only [adminToV_handler, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- The parts of a decoded frame image. -/
theorem frame_parts {k : Nat} {fi : Frame} {body : List Admin} {n c b : Value}
    (h : adminToV (.frame k fi body) = .case "FRAME_%{%}%" (.tuple [n, c, b])) :
    n = .num (.natN k) ∧ c = frameV fi ∧ b = .list (adminsToV body) := by
  simp only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- `natN` is injective. -/
theorem natN_inj {a b : Nat} (h : Value.num (.natN a) = .num (.natN b)) : a = b := by
  simp only [Value.num.injEq, Num.natN.injEq] at h
  exact h

/-- A value prefix decodes, with its length. -/
theorem decode_vals {env : Env} (D : CtrlDecode env) {σ : List (IL.Id × Value)} {l : List Admin}
    {ws : List Value} (hl : adminsToV l = ws)
    (ht : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs, l = vals vs ∧ ws.length = vs.length := by
  obtain ⟨vs, rfl⟩ := D.vals _ l (valsOnly_bindVals σ) (hl ▸ ht)
  exact ⟨vs, rfl, by rw [← hl, adminsToV_length, vals_length]⟩

/-! ## Decoding contexts and split bodies -/

section Decode

variable {env : Env} (D : CtrlDecode env)

include D in
/-- A one-instruction code whose image is a label image. -/
theorem decode_label {code : List Admin} {n c b : Value}
    (h : adminsToV code = [.case "LABEL_%{%}%" (.tuple [n, c, b])]) :
    ∃ k cont body, code = [.label k cont body] ∧ n = .num (.natN k) ∧
      c = .list (instrsToV cont) ∧ b = .list (adminsToV body) := by
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single h
  obtain ⟨k, cont, body, rfl⟩ := D.label a _ ha
  exact ⟨k, cont, body, rfl, label_parts ha⟩

include D in
/-- A one-instruction code whose image is a handler image. -/
theorem decode_handler {code : List Admin} {n c b : Value}
    (h : adminsToV code = [.case "HANDLER_%{%}%" (.tuple [n, c, b])]) :
    ∃ k cs body, code = [.handler k cs body] ∧ n = .num (.natN k) ∧
      c = .list (cs.map Encode.toValue) ∧ b = .list (adminsToV body) := by
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single h
  obtain ⟨k, cs, body, rfl⟩ := D.handler a _ ha
  exact ⟨k, cs, body, rfl, handler_parts ha⟩

include D in
/-- A one-instruction code whose image is a frame image. -/
theorem decode_frame {code : List Admin} {n c b : Value}
    (h : adminsToV code = [.case "FRAME_%{%}%" (.tuple [n, c, b])]) :
    ∃ k fi body, code = [.frame k fi body] ∧ n = .num (.natN k) ∧ c = frameV fi ∧
      b = .list (adminsToV body) := by
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single h
  obtain ⟨k, fi, body, rfl⟩ := D.frame a _ ha
  exact ⟨k, fi, body, rfl, frame_parts ha⟩

include D in
/-- A body `val* x instr*`, decoded. -/
theorem decode_split {σ : List (IL.Id × Value)} {body : List Admin} {ws rest : List Value}
    {x : Value} (h : .list (adminsToV body) = Value.list (ws ++ [x] ++ rest))
    (ht : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs b rest', body = vals vs ++ [b] ++ rest' ∧ adminsToV (vals vs) = ws ∧ adminToV b = x := by
  obtain ⟨b₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split (Value.list.inj h)
  obtain ⟨vs, rfl, -⟩ := decode_vals D h₁ ht
  exact ⟨vs, b, b₂, rfl, h₁, hb⟩

include D in
/-- A body `val'* val* x instr*`, decoded, with the length of `val*`. -/
theorem decode_split2 {σ : List (IL.Id × Value)} {body : List Admin}
    {ws₁ ws rest : List Value} {x : Value}
    (h : .list (adminsToV body) = Value.list (ws₁ ++ ws ++ [x] ++ rest))
    (ht₁ : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws₁))
    (ht : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs' vs b rest', body = vals vs' ++ vals vs ++ [b] ++ rest' ∧ adminsToV (vals vs) = ws ∧
      ws.length = vs.length ∧ adminToV b = x ∧ adminsToV rest' = rest := by
  obtain ⟨l₁₂, b, l₃, rfl, h₁₂, hb, h₃⟩ := adminsToV_eq_split (Value.list.inj h)
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := Exn.adminsToV_eq_append h₁₂
  obtain ⟨vs', rfl, -⟩ := decode_vals D h₁ ht₁
  obtain ⟨vs, rfl, hlen⟩ := decode_vals D h₂ ht
  exact ⟨vs', vs, b, l₃, rfl, h₂, hlen, hb, h₃⟩

include D in
/-- A body `val* REF.NULL_ADDR x instr*`, decoded. -/
theorem decode_splitNull {σ : List (IL.Id × Value)} {body : List Admin} {ws rest : List Value}
    {x : Value} (h : .list (adminsToV body) =
      Value.list (ws ++ [caseNilV "REF.NULL_ADDR"] ++ [x] ++ rest))
    (ht : HasTyp env (VarEnv.empty.bindVals σ) valsT (.list ws)) :
    ∃ vs b rest', body = vals vs ++ [.ref .null, b] ++ rest' ∧ adminToV b = x := by
  obtain ⟨l₁, b, b₂, rfl, h₁, hb, -⟩ := adminsToV_eq_split (Value.list.inj h)
  obtain ⟨l₀, n, rfl, h₀, hn₀⟩ := adminsToV_eq_snoc h₁
  obtain ⟨vs, rfl, -⟩ := decode_vals D h₀ ht
  obtain rfl := D.refNull n hn₀
  exact ⟨vs, b, b₂, by simp only [List.append_assoc, List.singleton_append], hb⟩

end Decode

variable (B : Builtins) (D : CtrlDecode (simEnv B))

/-! ## `Step_pure` 21, 22, 8 -/

include D in
/-- `Backward.pure 21` (`frame-vals`). -/
theorem bwd_frameVals : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 21 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).frameVals hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hvn : EvalExp (simEnv B) _ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  have hc : Value.list (adminsToV is) =
      .list [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), fr, .list ws])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) hvn)))
  obtain ⟨k, fi, body, rfl, hk, -, hb⟩ := decode_frame D (Value.list.inj hc)
  have hbody : adminsToV body = ws := (Value.list.inj hb).symm
  obtain ⟨vs, rfl, hlen⟩ := decode_vals D hbody (ew ▸ htv)
  have hk' : vs.length = k := by rw [← hlen]; exact natN_inj hk
  have hw' : w = .list (adminsToV (vals vs)) := by rw [hw, hbody]
  exact ⟨vals vs, hw', .frameVals hk'⟩

include D in
/-- `Backward.pure 22` (`return-frame`). -/
theorem bwd_returnFrame : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 22 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnFrame hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨ws₁, fv₁, htv₁⟩ := quant_list (x := "val'*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ev₁ : EvalExp (simEnv B) _ (valsPat "val'" "val'*") (.list ws₁) :=
    evalExp_valsPat (by decide) fv₁
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨rest, fr', -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "RETURN" (.tupE [])])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 evalExp_caseNil)) (evalExp_iterPat (by decide) fr')
  have hc : Value.list (adminsToV is) = .list [.case "FRAME_%{%}%"
      (.tuple [.num (.natN ws.length), fr, .list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rest)])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) hbody)))
  obtain ⟨k, fi, body, rfl, hk, -, hb⟩ := decode_frame D (Value.list.inj hc)
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hbr, -⟩ := decode_split2 D hb.symm htv₁ (ew ▸ htv)
  have hret : b = .plain .return_ := D.ret b hbr
  have hk' : vs.length = k := by rw [← hlen]; exact natN_inj hk
  have hw' : w = .list (adminsToV (vals vs)) := by rw [hw, h₂]
  exact ⟨vals vs, hw', hret ▸ .returnFrame hk'⟩

include D in
/-- `Backward.pure 8` (`br-label-zero`). -/
theorem bwd_brLabelZero : ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed (simEnv B) hn ⟨s, f, is⟩ →
    Fires (simEnv B) "Step_pure" 8 (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro s f is w _ hf
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body (simEnv_execRules B).brLabelZero hf)
  obtain ⟨cont, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.head _))
  have ec : EvalExp (simEnv B) _ (iterPat "instr'" "instr'*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, hw⟩ := valsN_cat hr ec
  obtain ⟨ws₁, fv₁, htv₁⟩ := quant_list (x := "val'*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ev₁ : EvalExp (simEnv B) _ (valsPat "val'" "val'*") (.list ws₁) :=
    evalExp_valsPat (by decide) fv₁
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨lv, fl, -⟩ := quant_of (x := "l") (t := labelidxT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val'" "val'*")
      (valsNPat "val" "val*" "n")) (.listE [.caseE "BR" (.varE "l")])) (iterPat "instr" "instr*"))
      (.list (ws₁ ++ ws ++ [.case "BR" lv] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev₁ (evalExp_valsNPat (by decide) fn fv))
      (evalExp_list1 (evalExp_case (evalExp_var fl)))) (evalExp_iterPat (by decide) fr)
  have hc : Value.list (adminsToV is) = .list [.case "LABEL_%{%}%"
      (.tuple [.num (.natN ws.length), .list cont, .list (ws₁ ++ ws ++ [.case "BR" lv] ++ rest)])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec hbody)))
  obtain ⟨k, cont₀, body, rfl, hk, hcont, hb⟩ := decode_label D (Value.list.inj hc)
  obtain ⟨vs', vs, b, l₃, rfl, h₂, hlen, hbr, -⟩ := decode_split2 D hb.symm htv₁ (ew ▸ htv)
  obtain ⟨l, hbl⟩ : ∃ l, b = .plain (.br l) := D.br b _ hbr
  have hlv : lv = pctV l.toNat := (Value.case.inj (hbl ▸ hbr)).2.symm
  have hl0 : l.toNat = 0 := immEq_of_eval (hlv ▸ fl) (ifPrem (hp _ (.head _)))
  have hk' : vs.length = k := by rw [← hlen]; exact natN_inj hk
  have hw' : w = .list (adminsToV (vals vs ++ expression cont₀)) := by
    rw [hw, adminsToV_append, h₂, Exn.adminsToV_expression, Value.list.inj hcont]
  exact ⟨vals vs ++ expression cont₀, hw', hbl ▸ .brLabelZero hl0 hk'⟩

/-! ## `Step_read` 8, 9, 10 -/

variable (Dr : RetDecode)

include D Dr in
/-- `Backward.read 8` (`return_call_ref-label`). -/
theorem bwd_returnCallRefLabel : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 8 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefLabel hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ey : EvalExp (simEnv B) _ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  have hc : Value.tuple [configV hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "LABEL_%{%}%"
      (.tuple [kv, .list cont, .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ rest)])],
      .list (ws ++ [.case "RETURN_CALL_REF" yy])] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev ey) (evalExp_iterPat (by decide) fr)))))))
      (evalExp_cat ev ey))
  obtain ⟨k, cont₀, body, rfl, -, -, hb⟩ := decode_label D (configV_cfgV (tuple2_inj hc).1).2.symm
  obtain ⟨vs, b, b₂, rfl, h₁, hbr⟩ := decode_split D hb.symm htv
  have hw : w = .list (adminsToV (vals vs ++ [b])) := by
    rw [(tuple2_inj hc).2, adminsToV_append, h₁, ← hbr]
    rfl
  exact ⟨vals vs ++ [b], hw, .returnCallRefLabel (Dr.returnCallRef b _ hbr)⟩

include D Dr in
/-- `Backward.read 9` (`return_call_ref-handler`). -/
theorem bwd_returnCallRefHandler : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 9 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefHandler hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨cs, fc, -⟩ := quant_list (x := "catch*") (t := .varT "catch" []) hq
    (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ey : EvalExp (simEnv B) _ (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])
      (.list [.case "RETURN_CALL_REF" yy]) := evalExp_list1 (evalExp_case (evalExp_var fy))
  have hc : Value.tuple [configV hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "HANDLER_%{%}%"
      (.tuple [kv, .list cs, .list (ws ++ [.case "RETURN_CALL_REF" yy] ++ rest)])],
      .list (ws ++ [.case "RETURN_CALL_REF" yy])] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_iterPat (by decide) fc)
        (evalExp_cat (evalExp_cat ev ey) (evalExp_iterPat (by decide) fr)))))))
      (evalExp_cat ev ey))
  obtain ⟨k, cs₀, body, rfl, -, -, hb⟩ :=
    decode_handler D (configV_cfgV (tuple2_inj hc).1).2.symm
  obtain ⟨vs, b, b₂, rfl, h₁, hbr⟩ := decode_split D hb.symm htv
  have hw : w = .list (adminsToV (vals vs ++ [b])) := by
    rw [(tuple2_inj hc).2, adminsToV_append, h₁, ← hbr]
    rfl
  exact ⟨vals vs ++ [b], hw, .returnCallRefHandler (Dr.returnCallRef b _ hbr)⟩

include D Dr in
/-- `Backward.read 10` (`return_call_ref-frame-null`). -/
theorem bwd_returnCallRefFrameNull : ∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
    Fires (simEnv B) "Step_read" 10 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, code⟩ w - hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (simEnv_readRules B).returnCallRefFrameNull hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := stateT) hq (.head _)
  obtain ⟨kv, fk, -⟩ := quant_of (x := "k") (t := nT) hq (.tail _ (.head _))
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨ws, fv, htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  have ev : EvalExp (simEnv B) _ (valsPat "val" "val*") (.list ws) := evalExp_valsPat (by decide) fv
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨rest, fr', -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hbody : EvalExp (simEnv B) _ (.catE (.catE (.catE (valsPat "val" "val*")
      (.listE [.caseE "REF.NULL_ADDR" (.tupE [])]))
      (.listE [.caseE "RETURN_CALL_REF" (.varE "yy")])) (iterPat "instr" "instr*"))
      (.list (ws ++ [caseNilV "REF.NULL_ADDR"] ++ [.case "RETURN_CALL_REF" yy] ++ rest)) :=
    evalExp_cat (evalExp_cat (evalExp_cat ev (evalExp_list1 evalExp_caseNil))
      (evalExp_list1 (evalExp_case (evalExp_var fy)))) (evalExp_iterPat (by decide) fr')
  have hc : Value.tuple [configV hn ⟨s, f, code⟩, w] = .tuple [cfgV z [.case "FRAME_%{%}%"
      (.tuple [kv, fr, .list (ws ++ [caseNilV "REF.NULL_ADDR"] ++
        [.case "RETURN_CALL_REF" yy] ++ rest)])], .list [caseNilV "TRAP"]] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fk) (evalExp_var ffr) hbody)))))
      (evalExp_list1 evalExp_caseNil))
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := decode_frame D (configV_cfgV (tuple2_inj hc).1).2.symm
  obtain ⟨vs, b, b₂, rfl, hbr⟩ := decode_splitNull D hb.symm htv
  have hst : Step P host ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, b] ++ b₂)]⟩
      ⟨s, f, [.trap]⟩ := .returnCallRefFrameNull (Dr.returnCallRef b _ hbr)
  exact ⟨[.trap], (tuple2_inj hc).2, hst⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd
