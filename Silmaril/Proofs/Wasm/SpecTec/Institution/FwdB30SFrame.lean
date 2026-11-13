module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms

/-!
# `return_call_ref` out of a frame at an address, at `Wasm30.builtins`

The redex of `Step_read/return_call_ref-frame-addr` is one frame whose body is values, then a
`RETURN_CALL_REF` (`FwdX30Fin.RetFrameAddr`). It is not a cast redex, so the `Step` facts of
`stepModel builtins` there are declarative (`Round6.Transfer.sstepB_iff_of_not_castRedex`).
Every `Step` fact from `z; [FRAME_n{f} body]` is `Step/read` at the whole redex, except a
`ctxt-frame` step:

* the three `Step_pure` rules that name `FRAME` need a body of values (`frame-vals`), a body
  whose first non-value is `RETURN` (`return-frame`) or the body `[TRAP]` (`trap-frame`); the
  first non-value of this body is the `RETURN_CALL_REF` (`frameVals_body`, `returnFrame_body`,
  `trapFrame_body`, read back with round 5's decoders, and `first_nonval`);
* `ctxt-instrs` can only step the empty code (`FwdB30X.not_ctxt_one`);
* the other context rules and the rules from 6 on name another constructor;
* `ctxt-frame` produces one frame, while Core's successor `vals vs ++ [ref, CALL_REF]` has at
  least two instructions, and `CfgRel` keeps the length (`FwdB30X.cfgRel_one_rev`).

* `sread_of_sstep_frame`: the inversion, at every `simEnv B`.
* `retFrameAddr_builtins`, `retFrameAddr_two_sided`: on `DomDet`, at every `RetFrameAddr` redex,
  a `Step_read` fact of `stepModel builtins` exists to Core's successor up to `CfgRel`, and
  every such fact to typed code is that successor up to `CfgRel`. Here `CfgRel` cannot be
  dropped in general: Core resolves the `CALL_REF` annotation, SpecTec keeps it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (caseNilV valsPat valsNPat iterPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.RefsGC (TagsIn)
open Silmaril.Wasm.SpecTec.Sim.Bwd (inv_pure inv_read inv_ctxtFrame cfgV_inj)
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

variable {H : Type}

/-! ## The first non-value of a code -/

/-- `b` is not the instruction of a value. -/
def NotVal (b : Admin) : Prop := ∀ v : Val, v.toAdmin ≠ b

/-- **The first non-value is unique**: two splits of one code at a non-value after a prefix of
values agree on that non-value. -/
theorem first_nonval {b c : Admin} (hb : NotVal b) (hc : NotVal c) :
    ∀ {X Y : List Val} {l m : List Admin}, vals X ++ b :: l = vals Y ++ c :: m → b = c
  | [], [], l, m, h => by
    have h' : b :: l = c :: m := by simpa [vals] using h
    exact (List.cons.inj h').1
  | [], y :: Y, l, m, h => by
    have h' : b :: l = y.toAdmin :: (vals Y ++ c :: m) := by simpa [vals] using h
    exact absurd (List.cons.inj h').1.symm (hb y)
  | x :: X, [], l, m, h => by
    have h' : x.toAdmin :: (vals X ++ b :: l) = c :: m := by simpa [vals] using h
    exact absurd (List.cons.inj h').1 (hc x)
  | x :: X, y :: Y, l, m, h => by
    have h' : x.toAdmin :: (vals X ++ b :: l) = y.toAdmin :: (vals Y ++ c :: m) := by
      simpa [vals] using h
    exact first_nonval hb hc (List.cons.inj h').2

/-- A `RETURN_CALL_REF` is not a value. -/
theorem notVal_rcr {c : Admin} (hc : c.IsReturnCallRef) : NotVal c := by
  intro v hv
  subst hv
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin, Admin.IsReturnCallRef] at hc

/-- `RETURN` is not a value. -/
theorem notVal_return : NotVal (.plain .return_) := by
  intro v hv
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin] at hv

/-- `TRAP` is not a value. -/
theorem notVal_trap : NotVal .trap := by
  intro v hv
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin] at hv

/-! ## The `Step_pure` rules that name `FRAME`, read back -/

/-- **`frame-vals` fires only at a frame whose body is values.** -/
theorem frameVals_body (B : Builtins) {code : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 21 (.tuple [.list (adminsToV code), w])) :
    ∃ k fi vs, code = [.frame k fi (vals vs)] := by
  have D := Typing.ctrlDecode_simEnv B
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).frameVals hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, -⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
  obtain ⟨fr, ffr, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨ws', fv', htv⟩ := quant_list (x := "val*") (t := .varT "val" []) hq
    (.tail _ (.tail _ (.head _)))
  have ew : ws' = ws := Value.list.inj (Option.some.inj (fv'.symm.trans fv))
  have hvn : EvalExp (simEnv B) _ (valsNPat "val" "val*" "n") (.list ws) :=
    evalExp_valsNPat (by decide) fn fv
  have hc : Value.list (adminsToV code) =
      .list [.case "FRAME_%{%}%" (.tuple [.num (.natN ws.length), fr, .list ws])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (Sim.evalExp_var fn) (Sim.evalExp_var ffr) hvn)))
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := Bwd.decode_frame D (Value.list.inj hc)
  have hbody : adminsToV body = ws := (Value.list.inj hb).symm
  obtain ⟨vs, rfl, -⟩ := Bwd.decode_vals D hbody (ew ▸ htv)
  exact ⟨k, fi, vs, rfl⟩

/-- **`return-frame` fires only at a frame whose body is values, `RETURN`, anything.** -/
theorem returnFrame_body (B : Builtins) {code : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 22 (.tuple [.list (adminsToV code), w])) :
    ∃ k fi vs' vs rest, code = [.frame k fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] := by
  have D := Typing.ctrlDecode_simEnv B
  obtain ⟨σ, hq, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).returnFrame hf)
  obtain ⟨hl, hr⟩ := Exn.evalExp_tup2_inv he
  obtain ⟨ws, fv, fn, -⟩ := Exn.evalExp_valsNPat_inv (by decide) hr
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
  have hc : Value.list (adminsToV code) = .list [.case "FRAME_%{%}%"
      (.tuple [.num (.natN ws.length), fr, .list (ws₁ ++ ws ++ [caseNilV "RETURN"] ++ rest)])] :=
    EvalExp.unique hl (evalExp_list1 (evalExp_case
      (evalExp_tup3 (Sim.evalExp_var fn) (Sim.evalExp_var ffr) hbody)))
  obtain ⟨k, fi, body, rfl, -, -, hb⟩ := Bwd.decode_frame D (Value.list.inj hc)
  obtain ⟨vs', vs, b, l₃, rfl, -, -, hbr, -⟩ := Bwd.decode_split2 D hb.symm htv₁ (ew ▸ htv)
  have hret : b = .plain .return_ := D.ret b hbr
  exact ⟨k, fi, vs', vs, l₃, by rw [hret]⟩

/-- **`trap-frame` fires only at the frame `[TRAP]`.** -/
theorem trapFrame_body (B : Builtins) {code : List Admin} {w : Value}
    (hf : Fires (simEnv B) "Step_pure" 29 (.tuple [.list (adminsToV code), w])) :
    ∃ k fi, code = [.frame k fi [.trap]] := by
  have D := Typing.ctrlDecode_simEnv B
  obtain ⟨σ, -, he, -⟩ := ruleBody_scope (fires_body (simEnv_execRules B).trapFrame hf)
  have hc : ∃ n' f', adminsToV code =
      [.case "FRAME_%{%}%" (.tuple [n', f', .list [caseNilV "TRAP"]])] ∧
        w = .list [caseNilV "TRAP"] := by
    concl_inv he
  obtain ⟨n', f', his, -⟩ := hc
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single his
  obtain ⟨n, fi, body, rfl⟩ := D.frame a _ ha
  have hbody : adminsToV body = [caseNilV "TRAP"] := by
    simp only [adminToV_frame, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at ha
    exact Value.list.inj ha.2.2.2.1
  obtain ⟨b, rfl, hb⟩ := adminsToV_eq_single hbody
  obtain rfl := D.trap b hb
  exact ⟨n, fi, rfl⟩

/-! ## The inversion at a frame -/

/-- The rows of `Step_pure` that a one-frame code does not refute by its constructor. -/
theorem pure_frame_rows :
    (pureInfoT.zipIdx.all fun p => outside ["FRAME_%{%}%"] p.1 || [21, 22, 29].contains p.2)
      = true := by
  decide +kernel

/-- The rows of `Step` from `ctxt-label` on that a one-frame code refutes by its constructor,
except `ctxt-frame` (index 2 of the rest). -/
theorem step_frame_rows :
    ((stepInfoT.drop 3).zipIdx.all fun p => outside ["FRAME_%{%}%"] p.1 || p.2 == 2) = true := by
  decide +kernel

/-- The body of the frame a `RETURN_CALL_REF` is returned out of. -/
abbrev rcrBody (A : List Val) (c : Admin) (rest : List Admin) : List Admin := vals A ++ c :: rest

/-- The bodies of two equal one-frame codes are equal. -/
theorem frame_body_eq {k k' : Nat} {fi fi' : Frame} {X Y : List Admin}
    (h : [Admin.frame k fi X] = [.frame k' fi' Y]) : X = Y := by
  simp only [List.cons.injEq, Admin.frame.injEq, and_true] at h
  exact h.2.2

/-- `frame-vals` does not fire at a frame returning a `RETURN_CALL_REF`. -/
theorem not_frameVals_rcr (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (v : Value) :
    ¬ Fires (simEnv B) "Step_pure" 21
      (.tuple [.list (adminsToV [.frame k fi (rcrBody A c rest)]), v]) := by
  intro hj
  obtain ⟨k', fi', vs, he⟩ := frameVals_body B hj
  have hmem : c ∈ vals vs := by
    rw [← frame_body_eq he]
    simp
  obtain ⟨v', -, hv'⟩ := List.mem_map.1 hmem
  exact notVal_rcr hc v' hv'

/-- `return-frame` does not fire at a frame returning a `RETURN_CALL_REF`. -/
theorem not_returnFrame_rcr (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (v : Value) :
    ¬ Fires (simEnv B) "Step_pure" 22
      (.tuple [.list (adminsToV [.frame k fi (rcrBody A c rest)]), v]) := by
  intro hj
  obtain ⟨k', fi', vs', vs, rest', he⟩ := returnFrame_body B hj
  have h2 : vals A ++ c :: rest = vals (vs' ++ vs) ++ .plain .return_ :: rest' := by
    rw [show vals A ++ c :: rest = rcrBody A c rest from rfl, frame_body_eq he]
    simp [vals]
  have e : c = .plain .return_ := first_nonval (notVal_rcr hc) notVal_return h2
  exact absurd (e ▸ hc) (by simp [Admin.IsReturnCallRef])

/-- `trap-frame` does not fire at a frame returning a `RETURN_CALL_REF`. -/
theorem not_trapFrame_rcr (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (v : Value) :
    ¬ Fires (simEnv B) "Step_pure" 29
      (.tuple [.list (adminsToV [.frame k fi (rcrBody A c rest)]), v]) := by
  intro hj
  obtain ⟨k', fi', he⟩ := trapFrame_body B hj
  have h2 : vals A ++ c :: rest = vals [] ++ .trap :: [] := frame_body_eq he
  have e : c = .trap := first_nonval (notVal_rcr hc) notVal_trap h2
  exact absurd (e ▸ hc) (by simp [Admin.IsReturnCallRef])

/-- **No `Step_pure` rule fires at a frame returning a `RETURN_CALL_REF`.** -/
theorem not_fires_pure_frame (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) (j : Nat) (v : Value) :
    ¬ Fires (simEnv B) "Step_pure" j
      (.tuple [.list (adminsToV [.frame k fi (rcrBody A c rest)]), v]) := by
  by_cases hm : j ∈ [21, 22, 29]
  · rcases (show j = 21 ∨ j = 22 ∨ j = 29 by simpa using hm) with rfl | rfl | rfl
    · exact not_frameVals_rcr B hc v
    · exact not_returnFrame_rcr B hc v
    · exact not_trapFrame_rcr B hc v
  · refine not_fires_of_row (tables_simEnv B).pureT (fun row hrow =>
      ⟨_, 1, .inl ⟨_, rfl, tagsIn_heads _, rfl⟩, .inl ?_⟩)
    have hp : outside ["FRAME_%{%}%"] row = true ∨ j ∈ [21, 22, 29] := by
      simpa only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] using
        List.all_eq_true.1 pure_frame_rows (row, j) (List.mk_mem_zipIdx_iff_getElem?.2 hrow)
    exact outside_spec (hp.resolve_right hm)

/-- `Step/pure` does not fire at a frame returning a `RETURN_CALL_REF`. -/
theorem not_step_pure_frame (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) {z w : Value} :
    ¬ Fires (simEnv B) "Step" 0
      (.tuple [cfgV z (adminsToV [.frame k fi (rcrBody A c rest)]), w]) := by
  intro hf
  obtain ⟨z₁, is, js, h₁, -, hq⟩ := inv_pure (tables_simEnv B).rules.pure hf
  obtain ⟨tp, rp, hrelp⟩ := (tables_simEnv B).pure
  obtain ⟨j, hj⟩ := (dderives_iff_fires hrelp).1 hq
  exact not_fires_pure_frame B hc j _ ((cfgV_inj h₁).2 ▸ hj)

/-- No `Step` rule from `ctxt-label` on fires at a one-frame code, but `ctxt-frame`. -/
theorem not_fires_step_frame (B : Builtins) {k : Nat} {fi : Frame} {body : List Admin}
    {z w : Value} (i : Nat) (hi : 3 ≤ i) (hi5 : i ≠ 5) :
    ¬ Fires (simEnv B) "Step" i (.tuple [cfgV z (adminsToV [.frame k fi body]), w]) := by
  refine not_fires_of_row (tables_simEnv B).stepT fun row hrow =>
    ⟨_, 1, .inr ⟨z, _, rfl, tagsIn_heads _, rfl⟩, .inl ?_⟩
  have hrow' : (stepInfoT.drop 3)[i - 3]? = some row := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hi]
    exact hrow
  have hp := List.all_eq_true.1 step_frame_rows (row, i - 3)
    (List.mk_mem_zipIdx_iff_getElem?.2 hrow')
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  exact outside_spec (hp.resolve_right (by omega))

/-- **Inversion at a frame returning a `RETURN_CALL_REF`**: at every `simEnv B`, a `Step` fact
from `z; [FRAME_k{fi} (vals A ++ c :: rest)]` with `c` a `RETURN_CALL_REF`, to a code that is
not one instruction (which excludes `ctxt-frame`), is `Step/read` at the whole redex. -/
theorem sread_of_sstep_frame (B : Builtins) {k : Nat} {fi : Frame} {A : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef) {z w : Value} (hw : ∀ z' x, w ≠ cfgV z' [x])
    (hs : SStep (simEnv B) (cfgV z (adminsToV [.frame k fi (rcrBody A c rest)])) w) :
    ∃ js, w = cfgV z js ∧ SRead (simEnv B) (cfgV z (adminsToV [.frame k fi (rcrBody A c rest)])) js := by
  have Tb := tables_simEnv B
  obtain ⟨tt, rules, hrel⟩ := Tb.step
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact absurd hf (not_step_pure_frame B hc)
  | 1, hf =>
    obtain ⟨z₁, is, js, h₁, h₂, hq⟩ := inv_read Tb.rules.read hf
    have e := cfgV_inj h₁
    exact ⟨js, e.1 ▸ h₂, e.1 ▸ e.2 ▸ hq⟩
  | 2, hf => exact (not_ctxt_one Tb hf).elim
  | 3, hf => exact absurd hf (not_fires_step_frame B 3 (by omega) (by omega))
  | 4, hf => exact absurd hf (not_fires_step_frame B 4 (by omega) (by omega))
  | 5, hf =>
    obtain ⟨s₁, s₁', f₁, fr, fr', n, is, is', -, h₂, -⟩ := inv_ctxtFrame Tb.rules.ctxtFrame hf
    exact (hw _ _ h₂).elim
  | n + 6, hf => exact absurd hf (not_fires_step_frame B (n + 6) (by omega) (by omega))

/-! ## At `Wasm30.builtins` -/

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- The redex body, as values and a `RETURN_CALL_REF`. -/
theorem retBody_eq (vs' vs : List Val) (a : Nat) (c : Admin) (rest : List Admin) :
    vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      rcrBody (vs' ++ vs ++ [.ref (.func a)]) c rest := by
  simp [rcrBody, vals, Val.toAdmin]

/-- Core's successor at a `RetFrameAddr` redex has two instructions or more, so no `Step` fact
`CfgRel`-related to it is one instruction. -/
theorem not_single_retSucc {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {c : Admin}
    {w : Value}
    (hrel : SpecTec.CfgRel hn (configV hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) w) :
    ∀ z' x, w ≠ cfgV z' [x] := by
  rintro z' x rfl
  obtain ⟨a', -, -, hca, -⟩ := FwdB30X.cfgRel_one_rev hrel
  have e := congrArg List.length hca
  simp at e

/-- **The inversion at a `RetFrameAddr` redex**, at the image of a configuration. -/
theorem sread_retFrameAddr (B : Builtins) {s : Store H} {f : Frame} {k : Nat} {fi : Frame}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)
    {w : Value} (hw : ∀ z' x, w ≠ cfgV z' [x])
    (hs : SStep (simEnv B)
      (configV hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩) w) :
    ∃ js, w = cfgV (stateV hn s f) js ∧ SRead (simEnv B)
      (configV hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩) js := by
  have e : configV hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ =
      cfgV (stateV hn s f)
        (adminsToV [.frame k fi (rcrBody (vs' ++ vs ++ [.ref (.func a)]) c rest)]) := by
    rw [Bwd.configV_eq, retBody_eq]
  rw [e] at hs ⊢
  exact sread_of_sstep_frame B hc hw hs

/-- **`return_call_ref` out of a frame at an address, at `builtins`**: on `DomDet`, a
`Step_read` fact of `stepModel builtins` exists to Core's successor up to `CfgRel`. -/
theorem retFrameAddr_builtins {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : FwdX30Fin.RetFrameAddr c is') :
    ∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js) := by
  obtain ⟨⟨w, hw, hrel⟩, -⟩ :=
    FwdX30Fin.stepObs_builtins (hinj := hinj) (hf := hf) (hh := hh) hc h.step
  cases h with
  | @mk s f fi k vs' vs a c₀ rest fn ps rs hc₀ hfn hex hlen =>
    have hnc := FwdX30Fin.not_castRedex_retFrameAddr (k := k) (fi := fi) (vs' := vs') (vs := vs)
      (a := a) (rest := rest) hc₀
    have hs : SStep EB (configV hn ⟨s, f, _⟩) w :=
      (Round6.Transfer.sstepB_iff_of_not_castRedex _ hn hnc w).1 hw
    obtain ⟨js, hjs, hq⟩ := sread_retFrameAddr _ hc₀ (not_single_retSucc hrel) hs
    exact ⟨js, (Round6.Transfer.sReadB_iff_noCast hnc).2 hq, hjs ▸ hrel⟩

/-- **Two-sided**: the fact exists, and every `Step_read` fact of `stepModel builtins` from the
configuration to typed code is Core's successor up to `CfgRel`. -/
theorem retFrameAddr_two_sided {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (h : FwdX30Fin.RetFrameAddr c is') :
    (∃ js, (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) ∧
      SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
        (cfgV (stateV hn c.store c.frame) js)) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) →
        SpecTec.CfgRel hn (configV hn ⟨c.store, c.frame, is'⟩)
          (cfgV (stateV hn c.store c.frame) js) :=
  ⟨retFrameAddr_builtins hc h, fun _ hjs hq => FwdX30Fin.readFact_unique_builtins hc h.step hjs hq⟩

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
