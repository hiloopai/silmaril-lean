module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeStuck
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Invert

/-!
# The backward half of the 2.0 whole step, assembled from per-rule obligations

`backward20_of_parts`: given the per-rule obligations `BwdParts20` (`Step_pure`, `Step_read` and
the `Step` rules from `local.set` on), every step of the wasm-2.0 script under the backend reading
from the image of a V2 configuration is the image of a V2 step. This is the context-rule part of
`Sim20.Task.wholeStepBwd`: `Step` rules 0–3 are handled here, for every configuration, with no
typing hypothesis.

* `inv_pure20`, `inv_read20`, `inv_ctxtLabel20`, `inv_ctxtFrame20`: the four structural rules of
  wasm-2.0 `Step` read backwards. Unlike 3.0's, they quantify their code as `instr*` and wrap each
  element in a `val <: admininstr`-style coercion (`subIterPat`), so the code on both sides of
  `Step/pure` and `Step/read` is `instr*`-typed, which the inversions record (`TypedSome`).
* `adminToV_label_inv`, `adminToV_frame_inv`: an image headed `LABEL_` or `FRAME_` is a label or a
  frame (no plain instruction is encoded with either constructor, `instrToV_head`).
* `ctxtFrame`: SpecTec 2.0's `ctxt-frame` keeps the inner frame unchanged (V2's deviation 2), so
  its backward case is V2's `Step.ctxtFrame` at a successor whose frame has the same image.
* The recursion is on `codeSize20`, the number of administrative instructions at any depth.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (iterPat evalExp_iterPat evalExp_iterBody_var)
open Silmaril.Wasm.SpecTec.Sim (RuleBody DDerives otherwise SStep SPure SRead Fires PremW QuantsOk
  ValsOnly cfgV stV evalExp_tup2 evalExp_tup3 evalExp_list1 evalExp_case dderives_iff_fires
  ruleBody_scope quant_of quant_list fires_body)
open Silmaril.Wasm.SpecTec.Sim.Bwd (rulePrem_nil cfgV_inj stV_inj tuple2_inj)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

/-! ## Coerced iterations -/

/-- `x*` with each element coerced, `(x : t₁ <: t₂)*`: how the 2.0 structural rules write their
code. -/
def subIterPat (x y : IL.Id) (t₁ t₂ : Typ) : Exp :=
  .iterE (.subE (.varE x) t₁ t₂) (.mk .list [.mk x (.varE y)])

/-- A coerced iteration evaluates to the list its domain is bound to. -/
theorem evalExp_subIterPat {env : Env} {ρ : VarEnv} {x y : IL.Id} {t₁ t₂ : Typ} (hx : x ≠ "_")
    {vs : List Value} (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (subIterPat x y t₁ t₂) (.list vs) :=
  evalExp_iterBody_var (d := 1) (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h

/-- The coerced `instr*` of the 2.0 rules. -/
abbrev instrIter (x y : IL.Id) : Exp :=
  subIterPat x y (.varT "instr" []) (.varT "admininstr" [])

/-! ## The four structural rules, read back -/

section Invert

variable {env : Env}

/-- `Step/pure`, read back. -/
theorem inv_pure20 (h₀ : HasRuleAt env "Step" "%~>%" 0 stepPureRule20) {v₁ v₂ : Value}
    (hf : Fires env "Step" 0 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ TypedSome env instrsT20 (.list is) ∧
      TypedSome env instrsT20 (.list js) ∧ SPure env is js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨is, fi, ti⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, tj⟩ :=
    quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (instrIter "instr" "instr*") (.list is) :=
    evalExp_subIterPat (by decide) fi
  have ej : EvalExp env _ (instrIter "instr'" "instr'*") (.list js) :=
    evalExp_subIterPat (by decide) fj
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SPure env is js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ei ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, ⟨_, ⟨rfl, rfl, rfl⟩, ti⟩,
    ⟨_, ⟨rfl, rfl, rfl⟩, tj⟩, hd⟩

/-- `Step/read`, read back. -/
theorem inv_read20 (h₀ : HasRuleAt env "Step" "%~>%" 1 stepReadRule20) {v₁ v₂ : Value}
    (hf : Fires env "Step" 1 (.tuple [v₁, v₂])) :
    ∃ z is js, v₁ = cfgV z is ∧ v₂ = cfgV z js ∧ TypedSome env instrsT20 (.list is) ∧
      TypedSome env instrsT20 (.list js) ∧ SRead env (cfgV z is) js := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨is, fi, ti⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (.tail _ (.head _))
  obtain ⟨js, fj, tj⟩ :=
    quant_list (x := "instr'*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  have ei : EvalExp env _ (instrIter "instr" "instr*") (.list is) :=
    evalExp_subIterPat (by decide) fi
  have ej : EvalExp env _ (instrIter "instr'" "instr'*") (.list js) :=
    evalExp_subIterPat (by decide) fj
  have ez := evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)
  have hc : Value.tuple [v₁, v₂] = .tuple [cfgV z is, cfgV z js] :=
    EvalExp.unique he (evalExp_tup2 ez (evalExp_case (evalExp_tup2 (evalExp_var fz) ej)))
  have hd : SRead env (cfgV z is) js := rulePrem_nil (hp _ (.head _)) (evalExp_tup2 ez ej)
  exact ⟨z, is, js, (tuple2_inj hc).1, (tuple2_inj hc).2, ⟨_, ⟨rfl, rfl, rfl⟩, ti⟩,
    ⟨_, ⟨rfl, rfl, rfl⟩, tj⟩, hd⟩

/-- `Step/ctxt-label`, read back. -/
theorem inv_ctxtLabel20 (h₀ : HasRuleAt env "Step" "%~>%" 2 ctxtLabelRule20) {v₁ v₂ : Value}
    (hf : Fires env "Step" 2 (.tuple [v₁, v₂])) :
    ∃ z z' n cont is is',
      v₁ = cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])] ∧
      v₂ = cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])] ∧
      SStep env (cfgV z is) (cfgV z' is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨z, fz, -⟩ := quant_of (x := "z") (t := .varT "state" []) hq (.head _)
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (.tail _ (.head _))
  obtain ⟨cont, fc, -⟩ :=
    quant_list (x := "instr_0*") (t := .varT "instr" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨z', fz', -⟩ :=
    quant_of (x := "z'") (t := .varT "state" []) hq (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have ec : EvalExp env _ (iterPat "instr_0" "instr_0*") (.list cont) :=
    evalExp_iterPat (by decide) fc
  have ei : EvalExp env _ (instrIter "instr" "instr*") (.list is) :=
    evalExp_subIterPat (by decide) fi
  have ei' : EvalExp env _ (instrIter "instr'" "instr'*") (.list is') :=
    evalExp_subIterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV z [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is])],
        cfgV z' [.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_var fz')
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) ec ei'))))))
  have hs : SStep env (cfgV z is) (cfgV z' is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (evalExp_tup2 (evalExp_var fz') ei')))
  exact ⟨z, z', n, cont, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

/-- `Step/ctxt-frame`, read back: the inner frame `fr` is the same on both sides. -/
theorem inv_ctxtFrame20 (h₀ : HasRuleAt env "Step" "%~>%" 3 ctxtFrameRule20) {v₁ v₂ : Value}
    (hf : Fires env "Step" 3 (.tuple [v₁, v₂])) :
    ∃ s s' f fr n is is',
      v₁ = cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])] ∧
      v₂ = cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is'])] ∧
      SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr) is') := by
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body h₀ hf)
  obtain ⟨s, fs, -⟩ := quant_of (x := "s") (t := .varT "store" []) hq (.head _)
  obtain ⟨f, ff, -⟩ := quant_of (x := "f") (t := .varT "frame" []) hq (.tail _ (.head _))
  obtain ⟨n, fn, -⟩ := quant_of (x := "n") (t := .varT "n" []) hq (.tail _ (.tail _ (.head _)))
  obtain ⟨fr, ffr, -⟩ :=
    quant_of (x := "f'") (t := .varT "frame" []) hq (.tail _ (.tail _ (.tail _ (.head _))))
  obtain ⟨is, fi, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨s', fs', -⟩ := quant_of (x := "s'") (t := .varT "store" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨is', fi', -⟩ := quant_list (x := "instr'*") (t := .varT "instr" []) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have ei : EvalExp env _ (instrIter "instr" "instr*") (.list is) :=
    evalExp_subIterPat (by decide) fi
  have ei' : EvalExp env _ (instrIter "instr'" "instr'*") (.list is') :=
    evalExp_subIterPat (by decide) fi'
  have hc : Value.tuple [v₁, v₂] =
      .tuple [cfgV (stV s f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is])],
        cfgV (stV s' f) [.case "FRAME_%{%}%" (.tuple [n, fr, .list is'])]] :=
    EvalExp.unique he (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei)))))
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ff)))
        (evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ffr) ei'))))))
  have hs : SStep env (cfgV (stV s fr) is) (cfgV (stV s' fr) is') := rulePrem_nil (hp _ (.head _))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ffr)))
        ei))
      (evalExp_case (evalExp_tup2
        (evalExp_case (evalExp_tup2 (evalExp_var fs') (evalExp_var ffr))) ei')))
  exact ⟨s, s', f, fr, n, is, is', (tuple2_inj hc).1, (tuple2_inj hc).2, hs⟩

end Invert

/-! ## Decoding images -/

/-- No plain instruction is encoded with `LABEL_` or `FRAME_`. -/
theorem instrToV_head (i : V2.Instr) : ∃ op x, instrToV i = .case op x ∧
    op ≠ "LABEL_%{%}%" ∧ op ≠ "FRAME_%{%}%" := by
  cases i
  case vvUnOp op => cases op; exact ⟨_, _, rfl, by decide, by decide⟩
  case vvBinOp op => cases op <;> exact ⟨_, _, rfl, by decide, by decide⟩
  case vvTernOp op => cases op; exact ⟨_, _, rfl, by decide, by decide⟩
  case vvTestOp op => cases op; exact ⟨_, _, rfl, by decide, by decide⟩
  all_goals exact ⟨_, _, rfl, by decide, by decide⟩

/-- An image headed `LABEL_` is a label. -/
theorem adminToV_label_inv {a : Admin} {x : Value} (h : adminToV a = .case "LABEL_%{%}%" x) :
    ∃ n cont body, a = .label n cont body := by
  cases a with
  | plain i =>
    obtain ⟨op, y, hy, hne, -⟩ := instrToV_head i
    have h' : instrToV i = .case "LABEL_%{%}%" x := h
    rw [hy] at h'
    exact absurd (Value.case.inj h').1 hne
  | label n cont body => exact ⟨n, cont, body, rfl⟩
  | _ => simp [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h

/-- An image headed `FRAME_` is a frame. -/
theorem adminToV_frame_inv {a : Admin} {x : Value} (h : adminToV a = .case "FRAME_%{%}%" x) :
    ∃ n fi body, a = .frame n fi body := by
  cases a with
  | plain i =>
    obtain ⟨op, y, hy, -, hne⟩ := instrToV_head i
    have h' : instrToV i = .case "FRAME_%{%}%" x := h
    rw [hy] at h'
    exact absurd (Value.case.inj h').1 hne
  | frame n fi body => exact ⟨n, fi, body, rfl⟩
  | _ => simp [adminToV, Silmaril.SpecTec.Equiv.Execution.caseNilV] at h

/-- `adminsToV` is a `map`. -/
theorem adminsToV_map : ∀ l : List Admin, adminsToV l = l.map adminToV
  | [] => rfl
  | a :: l => by
    show adminToV a :: adminsToV l = _
    rw [adminsToV_map l]
    rfl

/-- An image that is a one-element list comes from a one-element list. -/
theorem adminsToV_eq_single {l : List Admin} {v : Value} (h : adminsToV l = [v]) :
    ∃ a, l = [a] ∧ adminToV a = v := by
  rw [adminsToV_map] at h
  match l, h with
  | [a], h => exact ⟨a, rfl, by simpa using h⟩

variable {H : Type}

/-- The image of a configuration, as `cfgV`. -/
theorem configV_eq (hn : H → String) (c : Config H) :
    configV hn c = cfgV (stV (storeV hn c.store) (frameV c.frame)) (adminsToV c.code) := rfl

/-- Reading `configV` against a `cfgV`. -/
theorem configV_cfgV {hn : H → String} {c : Config H} {z : Value} {is : List Value}
    (h : configV hn c = cfgV z is) :
    z = stV (storeV hn c.store) (frameV c.frame) ∧ is = adminsToV c.code := by
  have h' := cfgV_inj h
  exact ⟨h'.1.symm, h'.2.symm⟩

/-! ## The size of active code -/

mutual
/-- The number of administrative instructions in `a`, at any depth of labels and frames. -/
def adminSize20 : Admin → Nat
  | .label _ _ b => codeSize20 b + 1
  | .frame _ _ b => codeSize20 b + 1
  | _ => 1

/-- `adminSize20`, summed over a sequence. -/
def codeSize20 : List Admin → Nat
  | [] => 0
  | a :: l => adminSize20 a + codeSize20 l
end

/-- The body of a label is smaller. -/
theorem codeSize20_label (n : Nat) (cont : List V2.Instr) (b : List Admin) :
    codeSize20 b < codeSize20 [.label n cont b] := by
  simp [codeSize20, adminSize20]

/-- The body of a frame is smaller. -/
theorem codeSize20_frame (n : Nat) (f : Frame) (b : List Admin) :
    codeSize20 b < codeSize20 [.frame n f b] := by
  simp [codeSize20, adminSize20]

/-! ## The backward recursion -/

section Rec

variable {B : Builtins} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- The backward conclusion at `c`. -/
def BwdAt (_B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H)
    (c : Config H) (w : Value) : Prop :=
  ∃ c', w = configV hn c' ∧ Step P host c c'

/-- The induction hypothesis: the backward conclusion for code smaller than `n`. -/
def IH20 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) (n : Nat) :
    Prop :=
  ∀ (c : Config H) (w : Value), codeSize20 c.code < n → SStep (simEnv20 B) (configV hn c) w →
    BwdAt B hn P host c w

/-- `Step/pure` backwards. -/
theorem bwd_pure20 (Bk : BwdParts20 B hn P host) {c : Config H} {w : Value}
    (hf : Fires (simEnv20 B) "Step" 0 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_pure20 (hasRuleAt_stepPure B) hf
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [e₁.2] at ti hi
  obtain ⟨code', rfl, hst⟩ := Bk.pure i c.code js ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .pure hst⟩

/-- `Step/read` backwards. -/
theorem bwd_read20 (Bk : BwdParts20 B hn P host) {c : Config H} {w : Value}
    (hf : Fires (simEnv20 B) "Step" 1 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_read20 (hasRuleAt_stepRead B) hf
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [← h₁] at hi
  rw [e₁.2] at ti
  obtain ⟨code', rfl, hst⟩ := Bk.read i c js ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .read hst⟩

/-- `Step/ctxt-label` backwards. -/
theorem bwd_ctxtLabel20 {n : Nat} (ih : IH20 B hn P host n) {s : Store H} {f : Frame}
    {code : List Admin} {w : Value} (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 2 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := inv_ctxtLabel20 (hasRuleAt_ctxtLabel B) hf
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := adminToV_label_inv ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (codeSize20_label k cont₀ body) (Nat.le_of_lt_succ hlt))
      (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ?_, .ctxtLabel hst⟩
  rw [h₂, e₃.1, e₃.2, ← hp.1, ← hp.2.1]
  rfl

/-- `Step/ctxt-frame` backwards: SpecTec 2.0 keeps the inner frame; V2's successor frame has the
same image. -/
theorem bwd_ctxtFrame20 {n : Nat} (ih : IH20 B hn P host n) {s : Store H} {f : Frame}
    {code : List Admin} {w : Value} (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 3 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, m, is, is', h₁, h₂, hs⟩ := inv_ctxtFrame20 (hasRuleAt_ctxtFrame B) hf
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := adminToV_frame_inv ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (Nat.lt_of_lt_of_le (codeSize20_frame k fi body) (Nat.le_of_lt_succ hlt))
      (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  have e₄ : sv' = storeV hn s₂ ∧ fr = frameV f₂ := stV_inj e₃.1
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ?_, .ctxtFrame hst⟩
  rw [h₂, e₄.1, e₃.2, e₀.2, ← hp.1, e₄.2]
  rfl

/-- One step of the backward recursion: dispatch on the `Step` rule that fired. -/
theorem bwd_dispatch20 (Bk : BwdParts20 B hn P host) {n : Nat} (ih : IH20 B hn P host n)
    {s : Store H} {f : Frame} {code : List Admin} {w : Value} (hlt : codeSize20 code < n + 1)
    (hs : SStep (simEnv20 B) (configV hn ⟨s, f, code⟩) w) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_stepPure B
  obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
  match i, hf with
  | 0, hf => exact bwd_pure20 Bk hf
  | 1, hf => exact bwd_read20 Bk hf
  | 2, hf => exact bwd_ctxtLabel20 ih hlt hf
  | 3, hf => exact bwd_ctxtFrame20 ih hlt hf
  | k + 4, hf => exact Bk.step (k + 4) (by omega) _ w hf

/-- The backward recursion, on the size of the code. -/
theorem bwd_all20 (Bk : BwdParts20 B hn P host) : ∀ n, IH20 B hn P host n
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨_, _, _⟩ _ hlt hs => bwd_dispatch20 Bk (bwd_all20 Bk n) hlt hs

end Rec

/-- **The backward half, from the per-rule obligations**: every step of the wasm-2.0 script under
the backend reading from the image of a V2 configuration is the image of a V2 step. -/
theorem backward20_of_parts {B : Builtins} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (Bk : BwdParts20 B hn P host) (c : Config H) (w : Value)
    (hs : SStepB (simEnv20 B) (configV hn c) w) : ∃ c', w = configV hn c' ∧ Step P host c c' :=
  bwd_all20 Bk (codeSize20 c.code + 1) c w (Nat.lt_succ_self _) ((sstepB20_iff B).1 hs)

/-- **`Sim20.Task.wholeStepBwd` from the per-rule obligations.** -/
theorem wholeStepBwd_of_parts
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        BwdParts20 B hn (Profile.spec nd r) host) :
    Task.wholeStepBwd := fun H hn hinj host nd r => by
  obtain ⟨B, Bk⟩ := h H hn hinj host nd r
  exact ⟨B, fun c w _ hs => backward20_of_parts Bk c w hs⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
