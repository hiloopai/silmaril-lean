module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.CallEq

/-!
# Core respects call-annotation equivalence

`step_respects`: if `c` steps to `c'` in Core, then every configuration equivalent to `c`
(`ConfigEq`: same store and frame, active code equal up to `CALL_REF` annotations) steps to a
configuration equivalent to `c'`. This is the Core half of "both semantics respect the
equivalence" (obstruction 1, `docs/projects/spectec/README.md`).

The proof is by induction on `Step`. `deep a` says that `AdminEq` relates `a` only to itself (no
`CALL_REF` at any depth of the active code, `adminEq_deep`). Every family step and most control
rules have a `deep` left-hand side, so the equivalent configuration *is* `c` (`resp_deep`). The
rules with an arbitrary tail (`br*`, `return*`, `trap-instrs`, `throw_ref-instrs`) drop the tail
(`resp_prefix`, `resp_labelPrefix`, …); the call rules accept any `CALL_REF` (`resp_call`); the
divergent host call stutters (`resp_callDiv`); and the four context rules recurse
(`resp_ctxt*`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## Respect -/

/-- A `CALL_REF`, in either representation. -/
theorem isCallRef_cases {a : Admin} (h : a.IsCallRef) :
    (∃ y, a = .plain (.callRef y)) ∨ ∃ d, a = .callRefType d := by
  unfold Admin.IsCallRef at h
  split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · exact h.elim

/-- An instruction that `AdminEq` relates only to itself: not a `CALL_REF` and not a context. -/
def rigid : Admin → Bool
  | .plain (.callRef _) | .callRefType _ | .label .. | .handler .. | .frame .. => false
  | _ => true

mutual
/-- `AdminEq` relates `a` only to itself: a rigid instruction, or a context with such a body. -/
def deep : Admin → Bool
  | .label _ _ b => codeDeep b
  | .handler _ _ b => codeDeep b
  | .frame _ _ b => codeDeep b
  | a => rigid a
/-- `Admin.deep` on every element. -/
def codeDeep : List Admin → Bool
  | [] => true
  | a :: l => deep a && codeDeep l
end

theorem rigid_not_callRef {a : Admin} (ha : rigid a = true) : ¬ a.IsCallRef := fun h => by
  rcases isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> exact Bool.noConfusion ha

theorem deep_not_callRef {a : Admin} (ha : deep a = true) : ¬ a.IsCallRef := fun h => by
  rcases isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> exact Bool.noConfusion ha

mutual
theorem adminEq_deep : ∀ {a x : Admin}, deep a = true → AdminEq a x → x = a
  | _, _, _, .refl _ => rfl
  | _, _, ha, .call h _ => absurd h (deep_not_callRef ha)
  | _, _, ha, .label h => by rw [codeEq_deep ha h]
  | _, _, ha, .handler h => by rw [codeEq_deep ha h]
  | _, _, ha, .frame h => by rw [codeEq_deep ha h]
theorem codeEq_deep : ∀ {l j : List Admin}, codeDeep l = true → CodeEq l j → j = l
  | _, _, _, .nil => rfl
  | _ :: _, _, hl, .cons ha hj => by
    have hl' : _ ∧ _ := Bool.and_eq_true_iff.1 hl
    rw [adminEq_deep hl'.1 ha, codeEq_deep hl'.2 hj]
end

/-! ## Inversions -/

theorem isReturnCallRef_deep {a : Admin} (h : a.IsReturnCallRef) : deep a = true := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · rfl
  · rfl
  · exact h.elim

theorem deep_toAdmin (v : Val) : deep v.toAdmin = true := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r <;> rfl

theorem codeDeep_append (a b : List Admin) : codeDeep (a ++ b) = (codeDeep a && codeDeep b) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [codeDeep, ih, Bool.and_assoc]

theorem codeDeep_vals (vs : List Val) : codeDeep (vals vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [vals, codeDeep, deep_toAdmin] at ih ⊢; exact ih

theorem codeEq_append_left : ∀ {a b j : List Admin}, CodeEq (a ++ b) j →
    ∃ j₁ j₂, j = j₁ ++ j₂ ∧ CodeEq a j₁ ∧ CodeEq b j₂
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hx h =>
    let ⟨j₁, j₂, e, h₁, h₂⟩ := codeEq_append_left h
    ⟨_ :: j₁, j₂, by rw [e]; rfl, .cons hx h₁, h₂⟩

theorem codeEq_prefix {p r j : List Admin} (hp : codeDeep p = true) (h : CodeEq (p ++ r) j) :
    ∃ r', j = p ++ r' ∧ CodeEq r r' := by
  obtain ⟨j₁, j₂, rfl, h₁, h₂⟩ := codeEq_append_left h
  rw [codeEq_deep hp h₁]
  exact ⟨j₂, rfl, h₂⟩

theorem codeEq_single {a : Admin} {j : List Admin} (h : CodeEq [a] j) :
    ∃ b, j = [b] ∧ AdminEq a b := by
  cases h with
  | cons hb hj => cases hj; exact ⟨_, rfl, hb⟩

theorem adminEq_label {n : Nat} {cont : List Instr} {is : List Admin} {x : Admin}
    (h : AdminEq (.label n cont is) x) : ∃ js, x = .label n cont js ∧ CodeEq is js := by
  cases h with
  | refl => exact ⟨is, rfl, CodeEq.refl _⟩
  | call h _ => exact h.elim
  | label h => exact ⟨_, rfl, h⟩

theorem adminEq_handler {n : Nat} {cs : List Catch} {is : List Admin} {x : Admin}
    (h : AdminEq (.handler n cs is) x) : ∃ js, x = .handler n cs js ∧ CodeEq is js := by
  cases h with
  | refl => exact ⟨is, rfl, CodeEq.refl _⟩
  | call h _ => exact h.elim
  | handler h => exact ⟨_, rfl, h⟩

theorem adminEq_frame {n : Nat} {fi : Frame} {is : List Admin} {x : Admin}
    (h : AdminEq (.frame n fi is) x) : ∃ js, x = .frame n fi js ∧ CodeEq is js := by
  cases h with
  | refl => exact ⟨is, rfl, CodeEq.refl _⟩
  | call h _ => exact h.elim
  | frame h => exact ⟨_, rfl, h⟩

theorem adminEq_callRef {a x : Admin} (ha : a.IsCallRef) (h : AdminEq a x) : x.IsCallRef := by
  cases h with
  | refl => exact ha
  | call _ hb => exact hb
  | label _ => exact ha.elim
  | handler _ => exact ha.elim
  | frame _ => exact ha.elim

/-! ## Configurations -/

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem cfgEq_deep {c d : Config H} (hp : codeDeep c.code = true) (h : ConfigEq c d) : d = c := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, hc⟩ := h
  have e : code' = code := codeEq_deep hp hc
  cases hs; cases hf; cases e; rfl

theorem cfgEq_prefix {s : Store H} {f : Frame} {p r : List Admin} {d : Config H}
    (hp : codeDeep p = true) (h : ConfigEq ⟨s, f, p ++ r⟩ d) :
    ∃ r', d = ⟨s, f, p ++ r'⟩ ∧ CodeEq r r' := by
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, hc⟩ := h
  obtain ⟨r', rfl, hr⟩ := codeEq_prefix hp hc
  cases hs; cases hf
  exact ⟨r', rfl, hr⟩

theorem cfgEq_one {s : Store H} {f : Frame} {a : Admin} {d : Config H}
    (h : ConfigEq ⟨s, f, [a]⟩ d) : ∃ b, d = ⟨s, f, [b]⟩ ∧ AdminEq a b := by
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, hc⟩ := h
  obtain ⟨b, rfl, hb⟩ := codeEq_single hc
  cases hs; cases hf
  exact ⟨b, rfl, hb⟩

theorem cfgEq_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {is : List Admin}
    {d : Config H} (h : ConfigEq ⟨s, f, [.label n cont is]⟩ d) :
    ∃ js, d = ⟨s, f, [.label n cont js]⟩ ∧ CodeEq is js := by
  obtain ⟨b, rfl, hb⟩ := cfgEq_one h
  obtain ⟨js, rfl, hj⟩ := adminEq_label hb
  exact ⟨js, rfl, hj⟩

theorem cfgEq_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {is : List Admin}
    {d : Config H} (h : ConfigEq ⟨s, f, [.handler n cs is]⟩ d) :
    ∃ js, d = ⟨s, f, [.handler n cs js]⟩ ∧ CodeEq is js := by
  obtain ⟨b, rfl, hb⟩ := cfgEq_one h
  obtain ⟨js, rfl, hj⟩ := adminEq_handler hb
  exact ⟨js, rfl, hj⟩

theorem cfgEq_frame {s : Store H} {f : Frame} {n : Nat} {fi : Frame} {is : List Admin}
    {d : Config H} (h : ConfigEq ⟨s, f, [.frame n fi is]⟩ d) :
    ∃ js, d = ⟨s, f, [.frame n fi js]⟩ ∧ CodeEq is js := by
  obtain ⟨b, rfl, hb⟩ := cfgEq_one h
  obtain ⟨js, rfl, hj⟩ := adminEq_frame hb
  exact ⟨js, rfl, hj⟩

theorem cfgEq_labelPrefix {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {p r : List Admin} {d : Config H} (hp : codeDeep p = true)
    (h : ConfigEq ⟨s, f, [.label n cont (p ++ r)]⟩ d) : ∃ r', d = ⟨s, f, [.label n cont (p ++ r')]⟩ := by
  obtain ⟨js, rfl, hj⟩ := cfgEq_label h
  obtain ⟨r', rfl, -⟩ := codeEq_prefix hp hj
  exact ⟨r', rfl⟩

theorem cfgEq_handlerPrefix {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {p r : List Admin} {d : Config H} (hp : codeDeep p = true)
    (h : ConfigEq ⟨s, f, [.handler n cs (p ++ r)]⟩ d) :
    ∃ r', d = ⟨s, f, [.handler n cs (p ++ r')]⟩ := by
  obtain ⟨js, rfl, hj⟩ := cfgEq_handler h
  obtain ⟨r', rfl, -⟩ := codeEq_prefix hp hj
  exact ⟨r', rfl⟩

theorem cfgEq_framePrefix {s : Store H} {f : Frame} {n : Nat} {fi : Frame}
    {p r : List Admin} {d : Config H} (hp : codeDeep p = true)
    (h : ConfigEq ⟨s, f, [.frame n fi (p ++ r)]⟩ d) : ∃ r', d = ⟨s, f, [.frame n fi (p ++ r')]⟩ := by
  obtain ⟨js, rfl, hj⟩ := cfgEq_frame h
  obtain ⟨r', rfl, -⟩ := codeEq_prefix hp hj
  exact ⟨r', rfl⟩

theorem cfgEq_call {s : Store H} {f : Frame} {p : List Admin} {c : Admin} {d : Config H}
    (hp : codeDeep p = true) (hc : c.IsCallRef) (h : ConfigEq ⟨s, f, p ++ [c]⟩ d) :
    ∃ c₂, c₂.IsCallRef ∧ d = ⟨s, f, p ++ [c₂]⟩ := by
  obtain ⟨r', rfl, hr⟩ := cfgEq_prefix hp h
  obtain ⟨c₂, rfl, hc₂⟩ := codeEq_single hr
  exact ⟨c₂, adminEq_callRef hc hc₂, rfl⟩

/-! ## The families -/

theorem deep_vconst (a : BitVec 128) : deep (vconst a) = true := rfl

@[simp] theorem deep_constI32 (b : BitVec 32) : deep (constI32 b) = true := deep_toAdmin _

theorem parametric_deep {is is' : List Admin} (h : ParametricStep is is') : codeDeep is = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, Bool.and_true, Bool.true_and]; try rfl)

theorem numeric_deep {is is' : List Admin} (h : NumericStep P is is') : codeDeep is = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, Bool.and_true, Bool.true_and]; try rfl)

theorem vector_deep {is is' : List Admin} (h : VectorStep P is is') : codeDeep is = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, deep_vconst, Bool.and_true, Bool.true_and]; try rfl)

theorem variable_deep {c c' : Config H} (h : VariableStep c c') : codeDeep c.code = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, Bool.and_true, Bool.true_and]; try rfl)

theorem table_deep {c c' : Config H} (h : TableStep P c c') : codeDeep c.code = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, deep_constI32, Bool.and_true, Bool.true_and]; try rfl)

theorem memory_deep {c c' : Config H} (h : MemoryStep P c c') : codeDeep c.code = true := by
  cases h <;> (simp only [codeDeep, deep_toAdmin, deep_constI32, Bool.and_true, Bool.true_and]; try rfl)

theorem reference_deep {c c' : Config H} (h : RefStep c c') : codeDeep c.code = true := by
  cases h <;> (simp only [codeDeep, deep_constI32, Bool.and_true, Bool.true_and]; try rfl)

theorem aggregate_deep {c c' : Config H} (h : AggregateStep c c') : codeDeep c.code = true := by
  cases h <;> (simp only [codeDeep, codeDeep_append, codeDeep_vals, deep_toAdmin, deep_constI32, Bool.and_true, Bool.true_and]; try rfl)

/-! ## Core respects `ConfigEq` -/

/-- Core respects the equivalence from `c` to `c'`: every configuration equivalent to `c` steps
to one equivalent to `c'`. -/
def Resp (P : Profile) (host : HostSemantics H) (c c' : Config H) : Prop :=
  ∀ d, ConfigEq c d → ∃ d', Step P host d d' ∧ ConfigEq c' d'

theorem codeDeep_app {a b : List Admin} (ha : codeDeep a = true) (hb : codeDeep b = true) :
    codeDeep (a ++ b) = true := by
  rw [codeDeep_append, ha, hb]
  rfl

theorem resp_deep {c c' : Config H} (hp : codeDeep c.code = true) (h : Step P host c c') :
    Resp P host c c' := fun d hd => by
  have e : d = c := cfgEq_deep hp hd
  exact ⟨c', e ▸ h, ConfigEq.refl _⟩

theorem resp_prefix {s : Store H} {f : Frame} {p r : List Admin} {c' : Config H}
    (hp : codeDeep p = true)
    (h : ∀ r', (r ≠ [] → r' ≠ []) → Step P host ⟨s, f, p ++ r'⟩ c') :
    Resp P host ⟨s, f, p ++ r⟩ c' := fun d hd => by
  obtain ⟨r', e, hr⟩ := cfgEq_prefix hp hd
  have hne : r ≠ [] → r' ≠ [] := fun h₁ h₂ =>
    h₁ (List.eq_nil_of_length_eq_zero (by rw [hr.length_eq, h₂]; rfl))
  exact ⟨c', e ▸ h r' hne, ConfigEq.refl _⟩

theorem resp_labelPrefix {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', Step P host ⟨s, f, [.label n cont (p ++ r')]⟩ c') :
    Resp P host ⟨s, f, [.label n cont (p ++ r)]⟩ c' := fun d hd => by
  obtain ⟨r', e⟩ := cfgEq_labelPrefix hp hd
  exact ⟨c', e ▸ h r', ConfigEq.refl _⟩

theorem resp_handlerPrefix {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', Step P host ⟨s, f, [.handler n cs (p ++ r')]⟩ c') :
    Resp P host ⟨s, f, [.handler n cs (p ++ r)]⟩ c' := fun d hd => by
  obtain ⟨r', e⟩ := cfgEq_handlerPrefix hp hd
  exact ⟨c', e ▸ h r', ConfigEq.refl _⟩

theorem resp_framePrefix {s : Store H} {f : Frame} {n : Nat} {fi : Frame}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', Step P host ⟨s, f, [.frame n fi (p ++ r')]⟩ c') :
    Resp P host ⟨s, f, [.frame n fi (p ++ r)]⟩ c' := fun d hd => by
  obtain ⟨r', e⟩ := cfgEq_framePrefix hp hd
  exact ⟨c', e ▸ h r', ConfigEq.refl _⟩

theorem cfgEq_call2 {s : Store H} {f : Frame} {q : List Admin} {x c : Admin} {d : Config H}
    (hq : codeDeep q = true) (hx : deep x = true) (hc : c.IsCallRef)
    (hd : ConfigEq ⟨s, f, q ++ [x, c]⟩ d) : ∃ c₂, c₂.IsCallRef ∧ d = ⟨s, f, q ++ [x, c₂]⟩ := by
  have e : ∀ c₀ : Admin, q ++ [x, c₀] = (q ++ [x]) ++ [c₀] := fun _ => by simp
  have hp : codeDeep (q ++ [x]) = true := codeDeep_app hq (by simp [codeDeep, hx])
  obtain ⟨c₂, hc₂, hd₂⟩ := cfgEq_call hp hc (e c ▸ hd)
  exact ⟨c₂, hc₂, by rw [hd₂, e]⟩

theorem resp_call {s : Store H} {f : Frame} {q : List Admin} {x c : Admin} {c' : Config H}
    (hq : codeDeep q = true) (hx : deep x = true) (hc : c.IsCallRef)
    (h : ∀ c₂ : Admin, c₂.IsCallRef → Step P host ⟨s, f, q ++ [x, c₂]⟩ c') :
    Resp P host ⟨s, f, q ++ [x, c]⟩ c' := fun d hd => by
  obtain ⟨c₂, hc₂, e⟩ := cfgEq_call2 hq hx hc hd
  exact ⟨c', e ▸ h c₂ hc₂, ConfigEq.refl _⟩

theorem resp_callDiv {s : Store H} {f : Frame} {q : List Admin} {x c : Admin}
    (hq : codeDeep q = true) (hx : deep x = true) (hc : c.IsCallRef)
    (h : ∀ c₂ : Admin, c₂.IsCallRef →
      Step P host ⟨s, f, q ++ [x, c₂]⟩ ⟨s, f, q ++ [x, c₂]⟩) :
    Resp P host ⟨s, f, q ++ [x, c]⟩ ⟨s, f, q ++ [x, c]⟩ := fun d hd => by
  obtain ⟨c₂, hc₂, e⟩ := cfgEq_call2 hq hx hc hd
  exact ⟨d, e ▸ h c₂ hc₂, hd⟩

theorem resp_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ih : Resp P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Resp P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := fun d hd => by
  have hd' : ConfigEq ⟨s, f, vals vs ++ (is ++ rest)⟩ d := by
    rw [← List.append_assoc]
    exact hd
  obtain ⟨r', rfl, hr⟩ := cfgEq_prefix (codeDeep_vals vs) hd'
  obtain ⟨j₁, j₂, rfl, h₁, h₂⟩ := codeEq_append_left hr
  obtain ⟨⟨s₂, f₂, K⟩, hst, hs, hf, hK⟩ := ih ⟨s, f, j₁⟩ ⟨rfl, rfl, h₁⟩
  have hne' : vs ≠ [] ∨ j₂ ≠ [] := hne.imp id fun h₃ h₄ =>
    h₃ (List.eq_nil_of_length_eq_zero (by rw [h₂.length_eq, h₄]; rfl))
  refine ⟨⟨s₂, f₂, vals vs ++ K ++ j₂⟩, ?_, hs, hf, ((CodeEq.refl _).append hK).append h₂⟩
  rw [← List.append_assoc]
  exact .ctxtInstrs hst hne'

theorem resp_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : Resp P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Resp P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := fun d hd => by
  obtain ⟨js, rfl, hj⟩ := cfgEq_label hd
  obtain ⟨⟨s₂, f₂, K⟩, hst, hs, hf, hK⟩ := ih ⟨s, f, js⟩ ⟨rfl, rfl, hj⟩
  exact ⟨⟨s₂, f₂, [.label n cont K]⟩, .ctxtLabel hst, hs, hf, .cons (.label hK) .nil⟩

theorem resp_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : Resp P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Resp P host ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := fun d hd => by
  obtain ⟨js, rfl, hj⟩ := cfgEq_handler hd
  obtain ⟨⟨s₂, f₂, K⟩, hst, hs, hf, hK⟩ := ih ⟨s, f, js⟩ ⟨rfl, rfl, hj⟩
  exact ⟨⟨s₂, f₂, [.handler n cs K]⟩, .ctxtHandler hst, hs, hf, .cons (.handler hK) .nil⟩

theorem resp_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : Resp P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Resp P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := fun d hd => by
  obtain ⟨js, rfl, hj⟩ := cfgEq_frame hd
  obtain ⟨⟨s₂, f₂, K⟩, hst, hs, hf, hK⟩ := ih ⟨s, fi, js⟩ ⟨rfl, rfl, hj⟩
  have hf' : fi' = f₂ := hf
  subst hf'
  exact ⟨⟨s₂, f, [.frame n fi' K]⟩, .ctxtFrame hst, hs, rfl, .cons (.frame hK) .nil⟩

theorem codeDeep_one {a : Admin} (h : deep a = true) : codeDeep [a] = true := by
  simp [codeDeep, h]

theorem codeDeep_two {a b : Admin} (ha : deep a = true) (hb : deep b = true) :
    codeDeep [a, b] = true := by
  simp [codeDeep, ha, hb]

theorem codeDeep_label1 {n : Nat} {cont : List Instr} {b : List Admin} (h : codeDeep b = true) :
    codeDeep [.label n cont b] = true := by
  simp [codeDeep, deep, h]

theorem codeDeep_handler1 {n : Nat} {cs : List Catch} {b : List Admin} (h : codeDeep b = true) :
    codeDeep [.handler n cs b] = true := by
  simp [codeDeep, deep, h]

theorem codeDeep_frame1 {n : Nat} {fi : Frame} {b : List Admin} (h : codeDeep b = true) :
    codeDeep [.frame n fi b] = true := by
  simp [codeDeep, deep, h]

theorem deep_vals_app (vs : List Val) {l : List Admin} (h : codeDeep l = true) :
    codeDeep (vals vs ++ l) = true := codeDeep_app (codeDeep_vals vs) h

/-- **Core respects call-annotation equivalence**: a step from `c` is matched, from every
configuration equivalent to `c`, by a step to a configuration equivalent to the successor. -/
theorem step_respects {c c' : Config H} (h : Step P host c c') : Resp P host c c' := by
  induction h with
  | parametric h => exact resp_deep (parametric_deep h) (.parametric h)
  | numeric h => exact resp_deep (numeric_deep h) (.numeric h)
  | vector h => exact resp_deep (vector_deep h) (.vector h)
  | «variable» h => exact resp_deep (variable_deep h) (.variable h)
  | table h => exact resp_deep (table_deep h) (.table h)
  | memory h => exact resp_deep (memory_deep h) (.memory h)
  | reference h => exact resp_deep (reference_deep h) (.reference h)
  | aggregate h => exact resp_deep (aggregate_deep h) (.aggregate h)
  | ctxtInstrs _ hne ih => exact resp_ctxtInstrs hne ih
  | ctxtLabel _ ih => exact resp_ctxtLabel ih
  | ctxtHandler _ ih => exact resp_ctxtHandler ih
  | ctxtFrame _ ih => exact resp_ctxtFrame ih
  | block hbt hm => exact resp_deep (deep_vals_app _ rfl) (.block hbt hm)
  | loop hbt hm => exact resp_deep (deep_vals_app _ rfl) (.loop hbt hm)
  | ifTrue hc => exact resp_deep rfl (.ifTrue hc)
  | ifFalse => exact resp_deep rfl .ifFalse
  | labelVals => exact resp_deep (codeDeep_label1 (codeDeep_vals _)) .labelVals
  | brLabelZero hl hn =>
    exact resp_labelPrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => .brLabelZero hl hn
  | brLabelSucc hl => exact resp_labelPrefix (deep_vals_app _ rfl) fun _ => .brLabelSucc hl
  | brHandler => exact resp_handlerPrefix (deep_vals_app _ rfl) fun _ => .brHandler
  | brIfTrue hc => exact resp_deep rfl (.brIfTrue hc)
  | brIfFalse => exact resp_deep rfl .brIfFalse
  | brTableLt hi => exact resp_deep rfl (.brTableLt hi)
  | brTableGe hi => exact resp_deep rfl (.brTableGe hi)
  | brOnNullNull => exact resp_deep rfl .brOnNullNull
  | brOnNullAddr hv => exact resp_deep (codeDeep_two (deep_toAdmin _) rfl) (.brOnNullAddr hv)
  | brOnNonNullNull => exact resp_deep rfl .brOnNonNullNull
  | brOnNonNullAddr hv =>
    exact resp_deep (codeDeep_two (deep_toAdmin _) rfl) (.brOnNonNullAddr hv)
  | brOnCastSucceed h => exact resp_deep rfl (.brOnCastSucceed h)
  | brOnCastFail h => exact resp_deep rfl (.brOnCastFail h)
  | brOnCastFailSucceed h => exact resp_deep rfl (.brOnCastFailSucceed h)
  | brOnCastFailFail h => exact resp_deep rfl (.brOnCastFailFail h)
  | call hx hf => exact resp_deep rfl (.call hx hf)
  | callRefNull hc => exact resp_call (q := []) rfl rfl hc fun _ h => .callRefNull h
  | callRefFunc hc hf he hn hcode =>
    exact resp_call (codeDeep_vals _) rfl hc fun _ h => .callRefFunc h hf he hn hcode
  | callRefHost hc hf he hn hcode hhost =>
    exact resp_call (codeDeep_vals _) rfl hc fun _ h => .callRefHost h hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost =>
    exact resp_callDiv (codeDeep_vals _) rfl hc fun _ h => .callRefHostDiv h hf he hn hcode hhost
  | returnCall hx hf => exact resp_deep rfl (.returnCall hx hf)
  | returnCallRefLabel hc =>
    exact resp_labelPrefix (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep hc)))
      fun _ => .returnCallRefLabel hc
  | returnCallRefHandler hc =>
    exact resp_handlerPrefix (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep hc)))
      fun _ => .returnCallRefHandler hc
  | returnCallRefFrameNull hc =>
    exact resp_framePrefix (deep_vals_app _ (codeDeep_two rfl (isReturnCallRef_deep hc)))
      fun _ => .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn =>
    exact resp_framePrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _))
      (codeDeep_two rfl (isReturnCallRef_deep hc)))
      fun _ => .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact resp_deep rfl .callIndirect
  | returnCallIndirect => exact resp_deep rfl .returnCallIndirect
  | frameVals hn => exact resp_deep (codeDeep_frame1 (codeDeep_vals _)) (.frameVals hn)
  | returnFrame hn =>
    exact resp_framePrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => .returnFrame hn
  | returnLabel => exact resp_labelPrefix (deep_vals_app _ rfl) fun _ => .returnLabel
  | returnHandler => exact resp_handlerPrefix (deep_vals_app _ rfl) fun _ => .returnHandler
  | throw ht he hn => exact resp_deep (deep_vals_app _ rfl) (.throw ht he hn)
  | throwRefNull => exact resp_deep rfl .throwRefNull
  | throwRefInstrs hne =>
    exact resp_prefix (deep_vals_app _ rfl) fun _ h => .throwRefInstrs (hne.imp id h)
  | throwRefLabel => exact resp_deep rfl .throwRefLabel
  | throwRefFrame => exact resp_deep rfl .throwRefFrame
  | throwRefHandlerEmpty => exact resp_deep rfl .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact resp_deep rfl (.throwRefHandlerCatch he ht)
  | throwRefHandlerCatchRef he ht => exact resp_deep rfl (.throwRefHandlerCatchRef he ht)
  | throwRefHandlerCatchAll => exact resp_deep rfl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact resp_deep rfl .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact resp_deep rfl (.throwRefHandlerNext h)
  | tryTable hbt hm => exact resp_deep (deep_vals_app _ rfl) (.tryTable hbt hm)
  | handlerVals => exact resp_deep (codeDeep_handler1 (codeDeep_vals _)) .handlerVals
  | trapInstrs hne => exact resp_prefix (deep_vals_app _ rfl) fun _ h => .trapInstrs (hne.imp id h)
  | trapLabel => exact resp_deep rfl .trapLabel
  | trapHandler => exact resp_deep rfl .trapHandler
  | trapFrame => exact resp_deep rfl .trapFrame

end Silmaril.Wasm.SpecTec.Sim.Bwd
