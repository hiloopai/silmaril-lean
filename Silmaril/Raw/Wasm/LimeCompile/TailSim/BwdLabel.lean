module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdHead

/-!
# The backward simulation of the tail-call rewrite: labels and handlers

* `R.not_pend`: at the non-tail level (under a handler of the frame) a pair is never pending;
* `bwd_label`: a target step at a label head, for a pair that is not pending (so the label's body
  pair is not pending either): inner steps by the induction hypothesis, exits by the same rule
  on the source after its body reaches the same kernel;
* `bwd_handler`: a target step at a handler head.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem RCRPair.not_both {c c' : Admin} (h : RCRPair c c') (h' : c = c') : False :=
  Admin.IsCallRef.not_isReturnCallRef (h' ▸ RCRPair.isCallRef h) (RCRPair.isReturnCallRef h)

/-- **At the non-tail level a pair is never pending.** -/
theorem R.not_pend {x y : List Admin} (hp : PendR x y) : ¬ R false false x y := by
  induction hp with
  | @rcr V c c' x y hcc =>
    intro h
    have hc'v : c'.val? = none := Admin.val?_of_isCallRef (RCRPair.isCallRef hcc)
    have hcv : c.val? = none := Admin.val?_of_isReturnCallRef (RCRPair.isReturnCallRef hcc)
    obtain ⟨V₀, V₁, x₀, hV, hx, hh⟩ := R.tsplit hc'v h
    cases hh with
    | same _ _ =>
      simp only [List.append_nil] at hV
      subst hV
      obtain ⟨-, h2, -⟩ := vals_append_cons_inj hcv hc'v hx
      exact RCRPair.not_both hcc h2
    | label => exact (RCRPair.isCallRef hcc : (Admin.label _ _ _).IsCallRef)
    | handler => exact (RCRPair.isCallRef hcc : (Admin.handler _ _ _).IsCallRef)
    | seg hce _ =>
      obtain ⟨fi, B, rfl⟩ := CE.tgt_single hce
      exact (RCRPair.isCallRef hcc : (Admin.frame _ _ _).IsCallRef)
    | @call _ k vs a d _ _ _ _ =>
      rw [show ∀ z, vals V₀ ++ (vals vs ++ [Admin.ref (.func a), .callRefType d] ++ z) =
        vals (V₀ ++ (vs ++ [.ref (.func a)])) ++ .callRefType d :: z from
        fun z => by simp [vals, Val.toAdmin], ← hV] at hx
      obtain ⟨-, h2, -⟩ := vals_append_cons_inj hcv (val?_crt d) hx
      subst h2
      exact RCRPair.isReturnCallRef hcc
    | trap us x' ht =>
      rcases TA.head ht hc'v rfl with h1 | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ <;>
        subst h1 <;> exact RCRPair.isCallRef hcc
    | throw us x' ht =>
      rcases TT.head ht hc'v rfl with ⟨h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ <;>
        subst h1 <;> exact RCRPair.isCallRef hcc
  | @label V n cont cont' b b' x y _ ih =>
    intro h
    obtain ⟨V₀, V₁, x₀, hV, hx, hh⟩ := R.tsplit rfl h
    cases hh with
    | same hc _ => exact hc trivial
    | label _ hb _ =>
      simp only [List.append_nil] at hV
      subst hV
      obtain ⟨-, h2, -⟩ := vals_append_cons_inj rfl rfl hx
      simp only [Admin.label.injEq] at h2
      obtain ⟨-, -, rfl⟩ := h2
      exact ih hb
    | seg hce _ =>
      obtain ⟨fi, B, h1⟩ := CE.tgt_single hce
      cases h1
    | trap us x' ht =>
      have hx' : vals V ++ Admin.label n cont b :: x = vals (V₀ ++ us) ++ .trap :: x' := by
        rw [hx]; simp
      exact absurd (vals_append_cons_inj rfl rfl hx').2.1 (by simp)
    | @throw _ _ _ _ e us x' ht =>
      have hx' : vals V ++ Admin.label n cont b :: x =
          vals (V₀ ++ us ++ [.ref (.exn e)]) ++ .plain .throwRef :: x' := by
        rw [hx]
        simp [vals, Val.toAdmin, throwing]
      exact absurd (vals_append_cons_inj rfl rfl hx').2.1 (by simp)

/-- **A target step at a label head.** -/
theorem bwd_label {tl : Bool} {s t t' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont cont' : List Instr} {b b' x rest' y' : List Admin}
    (ih : BIH P host (codeSize (vals V ++ .label n cont' b' :: rest')))
    (hst : StoreRel FRel s t) (hcond : cont' = cont ∨ (tl = true ∧ cont' = tailL cont))
    (hb : R false tl b b') (hr : R false tl x rest') (hnp : ¬ PendR b b')
    (hTs : ContextTyped ⟨s, f, vals V ++ .label n cont b :: x⟩)
    (hTt : ContextTyped ⟨t, f, vals V ++ .label n cont' b' :: rest'⟩)
    (h : Step P host ⟨t, f, vals V ++ .label n cont' b' :: rest'⟩ ⟨t', f', y'⟩) :
    BM P host tl t' f' y' s f (vals V ++ .label n cont b :: x)
      (codeSize (vals V ++ .label n cont' b' :: rest')) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
  have e1 : vals ws ++ (vals us ++ is₂) ++ rest' = vals (ws ++ us) ++ is₂ ++ rest' := by simp
  rw [e1]
  generalize ws ++ us = W at *
  have e2 : ∀ (cn : List Instr) (bb rr : List Admin),
      vals W ++ Admin.label n cn bb :: rr = vals W ++ [.label n cn bb] ++ rr := by intros; simp
  rw [e2] at hTs hTt ih ⊢
  clear hs
  cases hred with
  | @ctxt t' f' _ b₂' hs₁ =>
    obtain ⟨s', b₂, hm, hst', hR'⟩ := ih (LawfulCodeRank.label_body_lt (vals W) rest' n cont' b')
      hst hb hnp (ContextTyped.label hTs) (ContextTyped.label hTt) hs₁
    refine ⟨s', vals W ++ [.label n cont b₂] ++ x, ?_, hst',
      by simpa using R.valPre (R.label (n := n) hcond hR' hr) W⟩
    rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid (trans_label hT) W x)
    · exact Or.inr ⟨rfl, rfl, rfl, by simpa using LawfulCodeRank.label_lt (vals W) rest' n cont' hlt⟩
  | values vs =>
    rw [R.vals_tinv hb]
    refine BM.of_trans (.single (step_mid .labelVals W x)) hst ?_
    exact by simpa using R.valPre (R.append hr (R.refl false tl (vals vs))) W
  | @brZero vs₁ vs l rest₁ hl hn =>
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := .plain (.br l)) (V := vs₁ ++ vs) (rest' := rest₁)
      (.inl trivial) (by simpa using hb)
    have hstep := step_mid (Step.brLabelZero (P := P) (host := host) (s := s) (f := f)
      (cont := cont) (vs' := vs₁) (rest := x') hl hn) W x
    refine BM.of_trans (.single (by simpa using hstep)) hst ?_
    simpa using R.valPre (R.append hr (R.valPre (R.cont (fw := false) hcond) vs)) W
  | @brSucc vs l rest₁ hl =>
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := .plain (.br l)) (V := vs) (rest' := rest₁)
      (.inl trivial) (by simpa using hb)
    have hstep := step_mid (Step.brLabelSucc (P := P) (host := host) (s := s) (f := f) (n := n)
      (cont := cont) (vs := vs) (rest := x') hl) W x
    refine BM.of_trans (.single (by simpa using hstep)) hst ?_
    have hm := R.valPre (R.append hr (R.refl false tl (vals vs ++ [.plain (.br (labelPred l))]))) W
    simp only [List.append_assoc, List.cons_append] at hm ⊢
    exact hm
  | @return_ vs rest₁ =>
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := .plain .return_) (V := vs) (rest' := rest₁)
      (.inl trivial) (by simpa using hb)
    have hstep := step_mid (Step.returnLabel (P := P) (host := host) (s := s) (f := f) (n := n)
      (cont := cont) (vs := vs) (rest := x')) W x
    refine BM.of_trans (.single (by simpa using hstep)) hst ?_
    have hm := R.valPre (R.append hr (R.refl false tl (vals vs ++ [.plain .return_]))) W
    simp only [List.append_assoc, List.cons_append] at hm ⊢
    exact hm
  | @returnCallRef vs c rest₁ hc =>
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := c) (V := vs) (rest' := rest₁) (.inr hc)
      (by simpa using hb)
    have hstep := step_mid (Step.returnCallRefLabel (P := P) (host := host) (s := s) (f := f)
      (k := n) (cont := cont) (vs := vs) (rest := x') hc) W x
    refine BM.of_trans (.single (by simpa using hstep)) hst ?_
    have hm := R.valPre (R.append hr (R.refl false tl (vals vs ++ [c]))) W
    simp only [List.append_assoc, List.cons_append] at hm ⊢
    exact hm
  | throwRef a =>
    obtain ⟨us, x', rfl⟩ := R.throw_tinv (V := []) (rest' := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun : Steps P host ⟨s, f, vals W ++ [.label n cont (vals us ++ throwing a ++ x')] ++ x⟩
        ⟨s, f, vals W ++ [.label n cont (throwing a)] ++ x⟩ :=
      Steps.ctxtInstrs (Steps.label (disc_throw a s f us x'))
    have hstep := step_mid (Step.throwRefLabel (P := P) (host := host) (s := s) (f := f) (n := n)
      (cont := cont) (a := a)) W x
    exact BM.of_trans (Relation.TransGen.tail' hrun hstep) hst
      (by simpa using R.valPre (R.append hr (R.refl false tl (throwing a))) W)
  | trap =>
    obtain ⟨us, x', rfl⟩ := R.trap_tinv (V := []) (rest' := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun : Steps P host ⟨s, f, vals W ++ [.label n cont (vals us ++ .trap :: x')] ++ x⟩
        ⟨s, f, vals W ++ [.label n cont [.trap]] ++ x⟩ :=
      Steps.ctxtInstrs (Steps.label (disc_trap s f us x'))
    have hstep := step_mid (Step.trapLabel (P := P) (host := host) (s := s) (f := f) (n := n)
      (cont := cont)) W x
    exact BM.of_trans (Relation.TransGen.tail' hrun hstep) hst
      (by simpa using R.valPre (R.append hr (R.refl false tl [.trap])) W)

/-- **A target step at a handler head.** -/
theorem bwd_handler {tl : Bool} {s t t' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {b b' x rest' y' : List Admin}
    (ih : BIH P host (codeSize (vals V ++ .handler n cs b' :: rest')))
    (hst : StoreRel FRel s t) (hb : R false false b b') (hr : R false tl x rest')
    (hTs : ContextTyped ⟨s, f, vals V ++ .handler n cs b :: x⟩)
    (hTt : ContextTyped ⟨t, f, vals V ++ .handler n cs b' :: rest'⟩)
    (h : Step P host ⟨t, f, vals V ++ .handler n cs b' :: rest'⟩ ⟨t', f', y'⟩) :
    BM P host tl t' f' y' s f (vals V ++ .handler n cs b :: x)
      (codeSize (vals V ++ .handler n cs b' :: rest')) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is₂, hinv, rfl⟩ := Step.handler_inv hs
  have e1 : vals ws ++ (vals us ++ is₂) ++ rest' = vals (ws ++ us) ++ is₂ ++ rest' := by simp
  rw [e1]
  generalize ws ++ us = W at *
  have e2 : ∀ (bb rr : List Admin),
      vals W ++ Admin.handler n cs bb :: rr = vals W ++ [.handler n cs bb] ++ rr := by intros; simp
  rw [e2] at hTs hTt ih ⊢
  clear hs
  rcases hinv with ⟨b₂', hs₁, rfl⟩ | ⟨hs', hf', vs, rfl, rfl⟩ |
      ⟨hs', hf', vs, k, rest₁, hk, rfl, rfl⟩ | ⟨hk, hk0⟩
  · obtain ⟨s', b₂, hm, hst', hR'⟩ := ih (Closure.codeSize_handler_body_lt W rest' n cs b')
      hst hb (fun hp => R.not_pend hp hb) (ContextTyped.handler hTs) (ContextTyped.handler hTt) hs₁
    refine ⟨s', vals W ++ [.handler n cs b₂] ++ x, ?_, hst',
      by simpa using R.valPre (R.handler (n := n) (cs := cs) hR' hr) W⟩
    rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid (trans_handler hT) W x)
    · exact Or.inr ⟨rfl, rfl, rfl, by simpa using LawfulCodeRank.handler_lt (vals W) rest' n cs hlt⟩
  · subst t' f'
    rw [R.vals_tinv hb]
    refine BM.of_trans (.single (step_mid .handlerVals W x)) hst ?_
    simpa using R.valPre (R.append hr (R.refl false tl (vals vs))) W
  · subst t' f'
    have hk' : TKernel (match k with | [c] => c | _ => .trap) ∧
        ∃ c, k = [c] := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact ⟨.inl trivial, _, rfl⟩
      · exact ⟨.inl trivial, _, rfl⟩
      · exact ⟨.inr hc, _, rfl⟩
    obtain ⟨hkk, c, rfl⟩ := hk'
    obtain ⟨x', rfl, -⟩ := R.kernel_tinv (k := c) (V := vs) (rest' := rest₁) hkk (by simpa using hb)
    have hstep : Step P host ⟨s, f, [.handler n cs (vals vs ++ c :: x')]⟩ ⟨s, f, vals vs ++ [c]⟩ := by
      rcases hk with ⟨l, hl⟩ | hl | ⟨c', hc, hl⟩ <;>
        simp only [List.cons.injEq, and_true] at hl <;> subst hl
      · simpa using Step.brHandler (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs)
          (vs := vs) (rest := x')
      · simpa using Step.returnHandler (P := P) (host := host) (s := s) (f := f) (n := n)
          (cs := cs) (vs := vs) (rest := x')
      · simpa using Step.returnCallRefHandler (P := P) (host := host) (s := s) (f := f) (k := n)
          (cs := cs) (vs := vs) (rest := x') hc
    refine BM.of_trans (.single (step_mid hstep W x)) hst ?_
    simpa using R.valPre (R.append hr (R.refl false tl (vals vs ++ [c]))) W
  · obtain ⟨ht', hf', hstep⟩ := handler_kernel hk hk0
    subst t' f'
    have hrun : Steps P host ⟨s, f, [.handler n cs b]⟩ ⟨s, f, [.handler n cs b']⟩ := by
      rcases hk with rfl | ⟨a, rfl⟩
      · obtain ⟨us, x', rfl⟩ := R.trap_tinv (V := []) (rest' := []) (by simpa [Sim.vals_nil'] using hb)
        exact Steps.handler (disc_trap s f us x')
      · obtain ⟨us, x', rfl⟩ := R.throw_tinv (V := []) (rest' := [])
          (by simpa [Sim.vals_nil'] using hb)
        exact Steps.handler (disc_throw a s f us x')
    have hex : t.exns = s.exns := (StoreRel.exns_eq hst).symm
    have hT := Relation.TransGen.tail' hrun (hstep s hex)
    exact BM.of_trans (trans_mid hT W x) hst
      (by simpa using R.valPre (R.append hr (R.refl false tl is₂)) W)

end Silmaril.Raw.Wasm.LimeCompile.TailSim
