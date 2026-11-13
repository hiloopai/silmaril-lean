module

public import Silmaril.Proofs.Wasm.FX.Logic.Runs

/-!
# The rules of the WasmFX weakest-precondition calculus

Every rule is a lemma about runs of `StepFX'` (soundness by construction), for every profile,
host relation and FX function table:

* structural: `WP.mono`, `WP.steps`, `WP.step`, `wp_ends` and the final forms (`wp_val`,
  `wp_br`, `wp_ret`, `wp_trap`, `wp_throwing`, `wp_suspend`, `wp_switch`);
* contexts: `wp_seq` (values below, code after), `wp_label`, `wp_frame`, and **`wp_handler`**
  (the handler rule); `wp_head`/`wp_heads` run a step or a run at the head of `us; c; rest`;
* the arms of the context rules are the lemmas `seq_ends`, `label_ends`, `frame_ends` and
  `handler_ends`: a final form inside the context, with the context's postcondition, gives the
  weakest precondition outside.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-! ## Structural rules -/

theorem WP.mono {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} {Q Q' : PostFX H}
    (h : WP P host fx s K f c Q) (hQ : ∀ s K f o, Q s K f o → Q' s K f o) :
    WP P host fx s K f c Q' :=
  let ⟨s', K', f', c', o, hr, he, hq⟩ := h
  ⟨s', K', f', c', o, hr, he, hQ _ _ _ _ hq⟩

theorem WP.steps {s s₁ : Store H} {K K₁ : Conts} {f f₁ : Frame} {c c₁ : List AdminFX}
    {Q : PostFX H} (hr : StepsFX' P host fx ⟨s, K, f, c⟩ ⟨s₁, K₁, f₁, c₁⟩)
    (h : WP P host fx s₁ K₁ f₁ c₁ Q) : WP P host fx s K f c Q :=
  let ⟨s', K', f', c', o, hr', he, hq⟩ := h
  ⟨s', K', f', c', o, hr.trans hr', he, hq⟩

theorem WP.step {s s₁ : Store H} {K K₁ : Conts} {f f₁ : Frame} {c c₁ : List AdminFX}
    {Q : PostFX H} (hs : StepFX' P host fx ⟨s, K, f, c⟩ ⟨s₁, K₁, f₁, c₁⟩)
    (h : WP P host fx s₁ K₁ f₁ c₁ Q) : WP P host fx s K f c Q :=
  WP.steps (.single hs) h

/-- A final form satisfying the postcondition. -/
theorem wp_ends {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} {Q : PostFX H}
    (o : OutcomeFX) (he : o.Ends c) (h : Q s K f o) : WP P host fx s K f c Q :=
  ⟨s, K, f, c, o, .refl, he, h⟩

theorem wp_val {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {Q : PostFX H}
    (h : Q s K f (.normal vs)) : WP P host fx s K f (fvals vs) Q :=
  wp_ends (.normal vs) rfl h

theorem wp_br {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {x : LabelIdx}
    {rest : List AdminFX} {Q : PostFX H} (h : Q s K f (.br x.toNat vs)) :
    WP P host fx s K f (fvals vs ++ .core (.plain (.br x)) :: rest) Q :=
  wp_ends (.br x.toNat vs) ⟨x, rest, rfl, rfl⟩ h

theorem wp_ret {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {rest : List AdminFX}
    {Q : PostFX H} (h : Q s K f (.ret vs)) :
    WP P host fx s K f (fvals vs ++ .core (.plain .return_) :: rest) Q :=
  wp_ends (.ret vs) ⟨rest, rfl⟩ h

theorem wp_trap {s : Store H} {K : Conts} {f : Frame} {Q : PostFX H} (h : Q s K f .trap) :
    WP P host fx s K f [.core .trap] Q :=
  wp_ends .trap rfl h

theorem wp_throwing {s : Store H} {K : Conts} {f : Frame} {a : Nat} {Q : PostFX H}
    (h : Q s K f (.throw a)) : WP P host fx s K f (cthrowing a) Q :=
  wp_ends (.throw a) rfl h

/-- `suspend x` is a final form: an unhandled effect in the empty context. -/
theorem wp_suspend {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {x : TagIdx}
    {Q : PostFX H} (h : Q s K f (.susp .hole vs x)) :
    WP P host fx s K f (fvals vs ++ [.fx (.suspend x)]) Q :=
  wp_ends (.susp .hole vs x) rfl h

/-- `switch ct x` is a final form: an unhandled effect in the empty context. -/
theorem wp_switch {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {k : Nat}
    {ct : TypeIdx} {x : TagIdx} {Q : PostFX H} (h : Q s K f (.swtch .hole vs k ct x)) :
    WP P host fx s K f (fvals vs ++ [.contRef k, .fx (.switch ct x)]) Q :=
  wp_ends (.swtch .hole vs k ct x) rfl h

/-- A step at the head of `us; c; rest`. -/
theorem wp_head (us : List FVal) (rest : List AdminFX) {s s₁ : Store H} {K K₁ : Conts}
    {f f₁ : Frame} {c c₁ : List AdminFX} {Q : PostFX H}
    (hs : StepFX' P host fx ⟨s, K, f, c⟩ ⟨s₁, K₁, f₁, c₁⟩)
    (h : WP P host fx s₁ K₁ f₁ (fvals us ++ c₁ ++ rest) Q) :
    WP P host fx s K f (fvals us ++ c ++ rest) Q :=
  WP.steps (step_ctx hs) h

/-- A run at the head of `us; c; rest`. -/
theorem wp_heads (us : List FVal) (rest : List AdminFX) {s s₁ : Store H} {K K₁ : Conts}
    {f f₁ : Frame} {c c₁ : List AdminFX} {Q : PostFX H}
    (hs : StepsFX' P host fx ⟨s, K, f, c⟩ ⟨s₁, K₁, f₁, c₁⟩)
    (h : WP P host fx s₁ K₁ f₁ (fvals us ++ c₁ ++ rest) Q) :
    WP P host fx s K f (fvals us ++ c ++ rest) Q :=
  WP.steps (steps_ctx hs) h

/-! ## Sequences -/

/-- A final form below `us` and before `rest`. -/
theorem seq_ends {us : List FVal} {rest : List AdminFX} (hne : us ≠ [] ∨ rest ≠ [])
    {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} {Q : PostFX H} :
    ∀ (o : OutcomeFX), o.Ends c → seqPost P host fx us rest Q s K f o →
      WP P host fx s K f (fvals us ++ c ++ rest) Q
  | .normal vs, he, hq => by
    rw [show c = fvals vs from he, ← fvals_app]
    exact hq
  | .br l vs, ⟨x, r, hx, he⟩, hq => by
    have e : fvals us ++ c ++ rest = fvals (us ++ vs) ++ .core (.plain (.br x)) :: (r ++ rest) := by
      simp only [he, fvals_app, List.append_assoc, List.cons_append]
    have hq' : Q s K f (.br x.toNat (us ++ vs)) := by rw [hx]; exact hq
    rw [e]
    exact wp_br hq'
  | .ret vs, ⟨r, he⟩, hq => by
    have e : fvals us ++ c ++ rest =
        fvals (us ++ vs) ++ .core (.plain .return_) :: (r ++ rest) := by
      simp only [he, fvals_app, List.append_assoc, List.cons_append]
    rw [e]
    exact wp_ret hq
  | .trap, he, hq => by
    rw [show c = [.core .trap] from he]
    exact WP.step (StepFX'.trapSeq hne) (wp_trap hq)
  | .throw a, he, hq => by
    rw [show c = cthrowing a from he]
    exact WP.step (StepFX'.throwSeq hne) (wp_throwing hq)
  | .susp E vs x, he, hq => wp_ends (.susp (.seq us E rest) vs x) (by rw [he]; rfl) hq
  | .swtch E vs k ct x, he, hq => wp_ends (.swtch (.seq us E rest) vs k ct x) (by rw [he]; rfl) hq

/-- **Sequencing** (values below, code after). -/
theorem wp_seq {us : List FVal} {rest : List AdminFX} (hne : us ≠ [] ∨ rest ≠ [])
    {s : Store H} {K : Conts} {f : Frame} {c : List AdminFX} {Q : PostFX H}
    (h : WP P host fx s K f c (seqPost P host fx us rest Q)) :
    WP P host fx s K f (fvals us ++ c ++ rest) Q :=
  let ⟨_, _, _, _, o, hr, he, hq⟩ := h
  WP.steps (steps_seq hne hr) (seq_ends hne o he hq)

/-- Sequencing with nothing below: `c₁` then `c₂`. -/
theorem wp_app {c₂ : List AdminFX} (hne : c₂ ≠ []) {s : Store H} {K : Conts} {f : Frame}
    {c₁ : List AdminFX} {Q : PostFX H}
    (h : WP P host fx s K f c₁ (seqPost P host fx [] c₂ Q)) :
    WP P host fx s K f (c₁ ++ c₂) Q :=
  wp_seq (us := []) (Or.inr hne) h

/-! ## Labels -/

/-- A final form inside a label. -/
theorem label_ends {n : Nat} {k : List InstrFX} {s : Store H} {K : Conts} {f : Frame}
    {c : List AdminFX} {Q : PostFX H} :
    ∀ (o : OutcomeFX), o.Ends c → labelPost P host fx n k Q s K f o →
      WP P host fx s K f [.label n k c] Q
  | .normal vs, he, hq => by
    rw [show c = fvals vs from he]
    exact WP.step StepFX'.labelVals (wp_val hq)
  | .br 0 vs, ⟨x, r, hx, he⟩, ⟨vs₁, vs₂, hv, hn, hw⟩ => by
    have e : c = fvals vs₁ ++ fvals vs₂ ++ [.core (.plain (.br x))] ++ r := by
      simp only [he, hv, fvals_app, List.append_assoc, List.singleton_append]
    rw [e]
    exact WP.step (StepFX'.brLabelZero hx hn) hw
  | .br (l + 1) vs, ⟨x, r, hx, he⟩, hq => by
    have e : c = fvals vs ++ [.core (.plain (.br x))] ++ r := by
      simp only [he, List.append_assoc, List.singleton_append]
    have hl : (labelPred x).toNat = l := by
      show x.toNat - 1 = l
      omega
    rw [e]
    exact WP.step (StepFX'.brLabelSucc (by omega)) (wp_ends (.br l vs) ⟨_, [], hl, rfl⟩ hq)
  | .ret vs, ⟨r, he⟩, hq => by
    have e : c = fvals vs ++ [.core (.plain .return_)] ++ r := by
      simp only [he, List.append_assoc, List.singleton_append]
    rw [e]
    exact WP.step StepFX'.returnLabel (wp_ends (.ret vs) ⟨[], rfl⟩ hq)
  | .trap, he, hq => by
    rw [show c = [.core .trap] from he]
    exact WP.step StepFX'.trapLabel (wp_trap hq)
  | .throw a, he, hq => by
    rw [show c = cthrowing a from he]
    exact WP.step StepFX'.throwLabel (wp_throwing hq)
  | .susp E vs x, he, hq => wp_ends (.susp (.label n k E) vs x) (by rw [he]; rfl) hq
  | .swtch E vs j ct x, he, hq =>
    wp_ends (.swtch (.label n k E) vs j ct x) (by rw [he]; rfl) hq

/-- **The label rule.** -/
theorem wp_label {n : Nat} {k : List InstrFX} {s : Store H} {K : Conts} {f : Frame}
    {c : List AdminFX} {Q : PostFX H} (h : WP P host fx s K f c (labelPost P host fx n k Q)) :
    WP P host fx s K f [.label n k c] Q :=
  let ⟨_, _, _, _, o, hr, he, hq⟩ := h
  WP.steps (steps_label hr) (label_ends o he hq)

/-! ## Function frames -/

/-- A final form inside a function frame, seen from the caller's frame `f`. -/
theorem frame_ends {n : Nat} (f : Frame) {s : Store H} {K : Conts} {F : Frame}
    {c : List AdminFX} {Q : PostFX H} :
    ∀ (o : OutcomeFX), o.Ends c → framePost n f Q s K F o →
      WP P host fx s K f [.frame n F c] Q
  | .normal vs, he, ⟨hn, hq⟩ => by
    rw [show c = fvals vs from he]
    exact WP.step (StepFX'.frameVals hn) (wp_val hq)
  | .br _ _, _, hq => hq.elim
  | .ret vs, ⟨r, he⟩, ⟨vs₁, vs₂, hv, hn, hq⟩ => by
    have e : c = fvals vs₁ ++ fvals vs₂ ++ [.core (.plain .return_)] ++ r := by
      simp only [he, hv, fvals_app, List.append_assoc, List.singleton_append]
    rw [e]
    exact WP.step (StepFX'.returnFrame hn) (wp_val hq)
  | .trap, he, hq => by
    rw [show c = [.core .trap] from he]
    exact WP.step StepFX'.trapFrame (wp_trap hq)
  | .throw a, he, hq => by
    rw [show c = cthrowing a from he]
    exact WP.step StepFX'.throwFrame (wp_throwing hq)
  | .susp E vs x, he, hq => wp_ends (.susp (.frame n F E) vs x) (by rw [he]; rfl) hq
  | .swtch E vs k ct x, he, hq =>
    wp_ends (.swtch (.frame n F E) vs k ct x) (by rw [he]; rfl) hq

/-- **The frame rule**: the body runs in the callee's frame `F`; the caller's frame `f` stays. -/
theorem wp_frame {n : Nat} {s : Store H} {K : Conts} {f F : Frame} {c : List AdminFX}
    {Q : PostFX H} (h : WP P host fx s K F c (framePost n f Q)) :
    WP P host fx s K f [.frame n F c] Q :=
  let ⟨_, _, _, _, o, hr, he, hq⟩ := h
  WP.steps (steps_frame f hr) (frame_ends f o he hq)

/-! ## Handlers -/

/-- A caught `suspend`: the branch to the clause's label with the payload and the new
continuation. -/
theorem handler_suspend {hs : List HClause} {s : Store H} {K : Conts} {f : Frame} {E : CtxV}
    {vs : List FVal} {x : TagIdx} {Q : PostFX H}
    (h : ∃ (ta : Nat) (ti : TagInst) (l : LabelIdx), s.tag? (E.frameAt f) x = some (ta, ti) ∧
      ¬ E.Handles ta ∧ hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) ∧
      Q s (K ++ [some ⟨E.plug⟩]) f (.br l.toNat (vs ++ [.cont K.length]))) :
    WP P host fx s K f [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))] Q :=
  let ⟨_, _, l, ht, hE, hc, hq⟩ := h
  have he : (OutcomeFX.br l.toNat (vs ++ [.cont K.length])).Ends
      (fvals vs ++ [.contRef K.length, .core (.plain (.br l))]) :=
    ⟨l, [], rfl, by rw [fvals_cont]; simp only [List.append_assoc, List.cons_append,
      List.nil_append]⟩
  WP.step (StepFX'.suspend ht hE hc) (wp_ends _ he hq)

/-- A caught `switch`: the target continuation runs under the same handler. -/
theorem handler_switch {hs : List HClause} {s : Store H} {K : Conts} {f : Frame} {E : CtxV}
    {vs : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx} {Q : PostFX H}
    (h : ∃ (C : ContFX) (ta : Nat) (ti : TagInst), K[k]? = some (some C) ∧
      s.tag? (E.frameAt f) x = some (ta, ti) ∧ ¬ E.Handles ta ∧
      hs.find? (fun c => c.tag == ta) = some (.onSwitch ta) ∧
      WP P host fx s (K.set k none ++ [some ⟨E.plug⟩]) f
        [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))] Q) :
    WP P host fx s K f [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))] Q :=
  let ⟨_, _, _, hk, ht, hE, hc, hw⟩ := h
  WP.step (StepFX'.switch hk ht hE hc) hw

/-- A final form inside a handler frame. -/
theorem handler_ends {hs : List HClause} {s : Store H} {K : Conts} {f : Frame}
    {c : List AdminFX} {Q : PostFX H} :
    ∀ (o : OutcomeFX), o.Ends c → handlerPost P host fx hs Q s K f o →
      WP P host fx s K f [.handler hs c] Q
  | .normal vs, he, hq => by
    rw [show c = fvals vs from he]
    exact WP.step StepFX'.handlerVals (wp_val hq)
  | .br l vs, ⟨x, r, hx, he⟩, hq => by
    have e : c = fvals vs ++ [.core (.plain (.br x))] ++ r := by
      simp only [he, List.append_assoc, List.singleton_append]
    rw [e]
    exact WP.step StepFX'.brHandler (wp_ends (.br l vs) ⟨x, [], hx, rfl⟩ hq)
  | .ret vs, ⟨r, he⟩, hq => by
    have e : c = fvals vs ++ [.core (.plain .return_)] ++ r := by
      simp only [he, List.append_assoc, List.singleton_append]
    rw [e]
    exact WP.step StepFX'.returnHandler (wp_ends (.ret vs) ⟨[], rfl⟩ hq)
  | .trap, he, hq => by
    rw [show c = [.core .trap] from he]
    exact WP.step StepFX'.trapHandler (wp_trap hq)
  | .throw a, he, hq => by
    rw [show c = cthrowing a from he]
    exact WP.step StepFX'.throwHandler (wp_throwing hq)
  | .susp E vs x, he, hq => by
    rw [show c = E.plug (fvals vs ++ [.fx (.suspend x)]) from he]
    exact hq.elim handler_suspend fun hf => wp_ends (.susp (.handler hs E) vs x) rfl hf
  | .swtch E vs k ct x, he, hq => by
    rw [show c = E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]) from he]
    exact hq.elim handler_switch fun hf => wp_ends (.swtch (.handler hs E) vs k ct x) rfl hf

/-- **The handler rule.** The code under `handler hs` runs with the handler's postcondition:
effects caught by the clauses continue as `suspend`/`switch` prescribe. -/
theorem wp_handler {hs : List HClause} {s : Store H} {K : Conts} {f : Frame}
    {c : List AdminFX} {Q : PostFX H} (h : WP P host fx s K f c (handlerPost P host fx hs Q)) :
    WP P host fx s K f [.handler hs c] Q :=
  let ⟨_, _, _, _, o, hr, he, hq⟩ := h
  WP.steps (steps_handler hr) (handler_ends o he hq)

end Silmaril.Wasm.FX.Logic
