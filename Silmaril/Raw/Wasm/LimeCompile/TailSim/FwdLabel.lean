module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdHead
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv

/-!
# The forward simulation of the tail-call rewrite: labels and handlers

* `fwd_label`: a step at a label head. Inner steps by the induction hypothesis; `label-vals`,
  `br`, `return`, traps and throws as the same rule on the target (after the target's body
  reaches the same trap or throw); a `return_call_ref` leaving the label is the same step if the
  target has the same kernel, and otherwise **the source bubbles alone** and the pair becomes a
  bubbled pending tail call (`R.bub`), the target stuttering;
* `handler_kernel`: the `trap-handler` and `throw_ref-handler-*` rules read only the store's
  exceptions, so they are taken on any store with the same exceptions;
* `fwd_handler`: a step at a handler head (its body is at the non-tail level, where no pending
  tail call exists, so every exit is the same step).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- Identical code between a value prefix and related suffixes. -/
theorem R.mid {tl : Bool} {rest y : List Admin} (hr : R true tl rest y) (W : List Val)
    (z : List Admin) : R true tl (vals W ++ z ++ rest) (vals W ++ z ++ y) := by
  simpa using R.valPre (R.append hr (R.refl true tl z)) W

theorem codeSize_unlabel (V vs : List Val) (n : Nat) (cont : List Instr) (c : Admin)
    (rest₁ rest : List Admin) :
    codeSize (vals V ++ (vals vs ++ [c]) ++ rest) <
      codeSize (vals V ++ [.label n cont (vals vs ++ [c] ++ rest₁)] ++ rest) := by
  apply LawfulCodeRank.context_lt (vals V) rest
  have h1 := Closure.codeSize_label_body n cont (vals vs ++ [c] ++ rest₁)
  have h2 := codeSize_le_of_infix (vals vs ++ [c]) rest₁ []
  simp only [List.append_nil] at h2
  omega

/-- **A step at a label head.** -/
theorem fwd_label {tl : Bool} {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont cont' : List Instr} {b b' rest y x' : List Admin}
    (ih : FIH P host (codeSize (vals V ++ .label n cont b :: rest)))
    (hst : StoreRel FRel s t) (hcond : cont' = cont ∨ (tl = true ∧ cont' = tailL cont))
    (hb : R true tl b b') (hr : R true tl rest y)
    (hTs : ContextTyped ⟨s, f, vals V ++ .label n cont b :: rest⟩)
    (hTt : ContextTyped ⟨t, f, vals V ++ .label n cont' b' :: y⟩)
    (h : Step P host ⟨s, f, vals V ++ .label n cont b :: rest⟩ ⟨s', f', x'⟩) :
    FM P host tl s' f' x' t f (vals V ++ .label n cont' b' :: y)
      (codeSize (vals V ++ .label n cont b :: rest)) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
  have e1 : vals ws ++ (vals us ++ is₂) ++ rest = vals (ws ++ us) ++ is₂ ++ rest := by simp
  rw [e1]
  generalize ws ++ us = W at *
  have e2 : vals W ++ Admin.label n cont b :: rest = vals W ++ [.label n cont b] ++ rest := by simp
  have e3 : vals W ++ Admin.label n cont' b' :: y = vals W ++ [.label n cont' b'] ++ y := by simp
  rw [e2] at hTs ih ⊢
  rw [e3] at hTt ⊢
  clear hs
  cases hred with
  | @ctxt _ _ _ b₂ hs₁ =>
    obtain ⟨t', b₂', hm, hst', hR'⟩ := ih (LawfulCodeRank.label_body_lt (vals W) rest n cont b)
      hst hb (ContextTyped.label hTs) (ContextTyped.label hTt) hs₁
    refine ⟨t', vals W ++ [.label n cont' b₂'] ++ y, ?_, hst',
      by simpa using R.valPre (R.label (n := n) hcond hR' hr) W⟩
    rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid (trans_label hT) W y)
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.label_lt (vals W) rest n cont hlt⟩
  | values vs =>
    rw [R.vals_inv hb]
    refine FM.of_trans (.single (step_mid .labelVals W y)) hst ?_
    exact R.mid hr W _
  | @brZero vs₁ vs l rest₁ hl hn =>
    have hb' : R true tl (vals (vs₁ ++ vs) ++ .plain (.br l) :: rest₁) b' := by simpa using hb
    obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain (.br l)) trivial hb'
    have hstep := step_mid (Step.brLabelZero (P := P) (host := host) (s := t) (f := f) (cont := cont')
      (vs' := vs₁) (rest := y') hl hn) W y
    refine FM.of_trans (.single (by simpa using hstep)) hst ?_
    simpa using R.valPre (R.append hr (R.valPre (R.cont (fw := true) hcond) vs)) W
  | @brSucc vs l rest₁ hl =>
    obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain (.br l)) (V := vs) (rest := rest₁) trivial
      (by simpa using hb)
    have hstep := step_mid (Step.brLabelSucc (P := P) (host := host) (s := t) (f := f) (n := n)
      (cont := cont') (vs := vs) (rest := y') hl) W y
    refine FM.of_trans (.single (by simpa using hstep)) hst ?_
    have hm := R.mid hr W (vals vs ++ [.plain (.br (labelPred l))])
    simp only [List.append_assoc, List.cons_append] at hm ⊢
    exact hm
  | @return_ vs rest₁ =>
    obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain .return_) (V := vs) (rest := rest₁) trivial
      (by simpa using hb)
    have hstep := step_mid (Step.returnLabel (P := P) (host := host) (s := t) (f := f) (n := n)
      (cont := cont') (vs := vs) (rest := y')) W y
    refine FM.of_trans (.single (by simpa using hstep)) hst ?_
    have hm := R.mid hr W (vals vs ++ [.plain .return_])
    simp only [List.append_assoc, List.cons_append] at hm ⊢
    exact hm
  | @returnCallRef vs c rest₁ hc =>
    have hb₁ : R true tl (vals vs ++ c :: rest₁) b' := by simpa using hb
    obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := R.split (Admin.val?_of_isReturnCallRef hc) hb₁
    cases hh with
    | @same _ _ _ y₁ _ _ =>
      have hstep := step_mid (Step.returnCallRefLabel (P := P) (host := host) (s := t) (f := f)
        (k := n) (cont := cont') (vs := V₀) (rest := y₁) hc) W y
      refine FM.of_trans (.single (by simpa using hstep)) hst ?_
      have hm := R.mid hr W (vals V₀ ++ [c])
      simp only [List.append_assoc, List.cons_append, List.append_nil]
        at hm ⊢
      exact hm
    | @instr i _ y₁ _ =>
      have hti : tailI i = [i] := by
        cases i <;> simp_all [Admin.IsReturnCallRef, Silmaril.Wasm.LimeCompile.Tail.tailI]
      rw [hti]
      have hstep := step_mid (Step.returnCallRefLabel (P := P) (host := host) (s := t) (f := f)
        (k := n) (cont := cont') (vs := V₀) (rest := y₁) hc) W y
      refine FM.of_trans (.single (by simpa using hstep)) hst ?_
      have hm := R.mid hr W (vals V₀ ++ [.plain i])
      simp only [List.append_assoc, List.cons_append, List.append_nil]
        at hm ⊢
      exact hm
    | @rcr _ c' _ y₁ hcc _ =>
      refine FM.of_stutter ?_ hst ?_
      · simpa using codeSize_unlabel W V₀ n cont c rest₁ rest
      · have := R.bub (U := W) (ws := V₀) (c := c) (X := rest)
          (B := vals W ++ [.label n cont' (vals V₀ ++ c' :: .plain .return_ :: y₁)] ++ y)
          ⟨W, n, cont', .hole, y, c', y₁, hcc, by simp [NCtx.fill]⟩
        simpa using this
    | @bub ws₀ _ B U X hp =>
      refine FM.of_stutter ?_ hst ?_
      · simpa using codeSize_unlabel W (V₀ ++ (U ++ ws₀)) n cont c rest₁ rest
      · obtain ⟨V₂, n₂, cont₂, N, L₂, c', Y, hcc, rfl⟩ := hp
        have := R.bub (U := W ++ V₀ ++ U) (ws := ws₀) (c := c) (X := rest)
          (B := vals W ++ [.label n cont' (vals V₀ ++ (vals V₂ ++
            .label n₂ cont₂ (N.fill (vals ws₀ ++ c' :: .plain .return_ :: Y)) :: L₂))] ++ y)
          ⟨W, n, cont', .label (V₀ ++ V₂) n₂ cont₂ N L₂, y, c', Y, hcc, by simp [NCtx.fill]⟩
        simpa using this
    | label => exact hc.elim
    | handler => exact hc.elim
    | frame => exact hc.elim
    | call => exact hc.elim
    | trap => exact hc.elim
    | throw => exact hc.elim
  | throwRef a =>
    have hT := R.throw_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun : Steps P host ⟨t, f, vals W ++ [.label n cont' b'] ++ y⟩
        ⟨t, f, vals W ++ [.label n cont' (throwing a)] ++ y⟩ :=
      Steps.ctxtInstrs (Steps.label (TT.run hT))
    have hstep := step_mid (Step.throwRefLabel (P := P) (host := host) (s := t) (f := f) (n := n)
      (cont := cont') (a := a)) W y
    exact FM.of_trans (Relation.TransGen.tail' hrun hstep) hst
      (R.mid hr W _)
  | trap =>
    have hT := R.trap_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)
    have hrun : Steps P host ⟨t, f, vals W ++ [.label n cont' b'] ++ y⟩
        ⟨t, f, vals W ++ [.label n cont' [.trap]] ++ y⟩ :=
      Steps.ctxtInstrs (Steps.label (TA.run hT))
    have hstep := step_mid (Step.trapLabel (P := P) (host := host) (s := t) (f := f) (n := n)
      (cont := cont')) W y
    exact FM.of_trans (Relation.TransGen.tail' hrun hstep) hst
      (R.mid hr W _)

/-! ## Handlers -/

theorem kernel_not_vals {b : List Admin} (hb : b = [.trap] ∨ ∃ a, b = throwing a)
    {vs : List Val} (h : b = vals vs) : False := by
  rcases hb with rfl | ⟨a, rfl⟩
  · have hm : Admin.trap ∈ vals vs := by rw [← h]; simp
    obtain ⟨w, hw⟩ := PC.mem_vals hm
    rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw
  · have hm : Admin.plain .throwRef ∈ vals vs := by rw [← h]; simp [throwing]
    obtain ⟨w, hw⟩ := PC.mem_vals hm
    rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hw

theorem kernel_not_exit {b : List Admin} (hb : b = [.trap] ∨ ∃ a, b = throwing a)
    {vs : List Val} {k : Admin} (hk : k.val? = none) (hk' : k ≠ .trap)
    (hk'' : k ≠ .plain .throwRef) {rest : List Admin} (h : b = vals vs ++ k :: rest) : False := by
  rcases hb with rfl | ⟨a, rfl⟩
  · have := vals_append_cons_inj (vs := []) (ws := vs) val?_trap hk (by simpa [Sim.vals_nil'] using h)
    exact hk' this.2.1.symm
  · have := vals_append_cons_inj (vs := [.ref (.exn a)]) (ws := vs) val?_throwRef hk
      (by simpa [throwing, vals, Val.toAdmin] using h)
    exact hk'' this.2.1.symm

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The kernel rules of a handler** read only the store's exceptions. -/
theorem handler_kernel_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (n : Nat) (cs : List Catch) (b : List Admin), c.code = [.handler n cs b] →
      (b = [.trap] ∨ ∃ a, b = throwing a) →
      c'.store = c.store ∧ c'.frame = c.frame ∧ ∀ t : Store H, c.store.exns = t.exns →
        Step P host ⟨t, c.frame, [.handler n cs b]⟩ ⟨t, c.frame, c'.code⟩ := by
  induction h with
  | parametric hp =>
    intro n cs b hc _
    exact (ParametricStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | numeric hp =>
    intro n cs b hc _
    exact (NumericStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | vector hp =>
    intro n cs b hc _
    exact (VectorStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | «variable» hp =>
    intro n cs b hc _
    exact (VariableStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | table hp =>
    intro n cs b hc _
    exact (TableStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | memory hp =>
    intro n cs b hc _
    exact (MemoryStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | reference hp =>
    intro n cs b hc _
    exact (RefStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | aggregate hp =>
    intro n cs b hc _
    exact (AggregateStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro n cs b hc _
    exfalso
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, e, es₁, he, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc
    have hc' : vals (vs₀ ++ vs₁) ++ e :: (es₁ ++ rest) = vals [] ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp [Sim.vals_nil']
    obtain ⟨h1, -, h3⟩ := vals_append_cons_inj he rfl hc'
    obtain ⟨-, rfl⟩ := List.append_eq_nil_iff.mp h3
    have := List.append_eq_nil_iff.mp h1
    rcases hne with hne | hne
    · exact hne this.1
    · exact hne rfl
  | @trapInstrs _ _ vs₀ rest hne =>
    intro n cs b hc _
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals [] ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp [Sim.vals_nil']
    exact absurd (vals_append_cons_inj val?_trap rfl hc').2.1 (by simp)
  | @throwRefInstrs _ _ vs₀ x rest hne =>
    intro n cs b hc _
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals [] ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    exact absurd (vals_append_cons_inj val?_throwRef rfl hc').2.1 (by simp)
  | @ctxtHandler s₀ s₁ f₀ f₁ n₀ cs₀ is₀ is₁ hs _ =>
    intro n cs b hc hb
    exfalso
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    rcases hb with rfl | ⟨a, rfl⟩
    · obtain ⟨-, -, p, w, q, hu, hw, -⟩ := Step.trap_redex_aux hs [] (by simp [Sim.vals_nil'])
      have := congrArg List.length hu
      simp at this
      exact hw (List.eq_nil_of_length_eq_zero (by omega))
    · obtain ⟨-, -, hcase⟩ := Step.throwRef_redex_aux hs [.ref (.exn a)]
        (by simp [throwing, vals, Val.toAdmin])
      rcases hcase with ⟨p, w, q, a', hu, hw, -⟩ | ⟨u, u', hu, -⟩
      · have := congrArg List.length hu
        simp at this
        exact hw (List.eq_nil_of_length_eq_zero (by omega))
      · have := congrArg List.getLast? hu
        simp at this
  | handlerVals =>
    intro n cs b hc hb
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact (kernel_not_vals hb rfl).elim
  | @brHandler _ _ _ _ vs l rest =>
    intro n cs b hc hb
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact (kernel_not_exit (k := .plain (.br l)) (vs := vs) (rest := rest) hb rfl (by simp) (by simp)
      (by simp)).elim
  | @returnHandler _ _ _ _ vs rest =>
    intro n cs b hc hb
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact (kernel_not_exit (k := .plain .return_) (vs := vs) (rest := rest) hb rfl (by simp)
      (by simp) (by simp)).elim
  | @returnCallRefHandler _ _ _ _ vs c rest hc₀ =>
    intro n cs b hc hb
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact (kernel_not_exit (k := c) (vs := vs) (rest := rest) hb (Admin.val?_of_isReturnCallRef hc₀)
      (fun h => by subst h; exact hc₀) (fun h => by subst h; exact hc₀) (by simp)).elim
  | trapHandler =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t _ => .trapHandler⟩
  | throwRefHandlerEmpty =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t _ => .throwRefHandlerEmpty⟩
  | throwRefHandlerCatch he ht =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t hex => .throwRefHandlerCatch (by rw [← hex]; exact he) ht⟩
  | throwRefHandlerCatchRef he ht =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t hex => .throwRefHandlerCatchRef (by rw [← hex]; exact he) ht⟩
  | throwRefHandlerCatchAll =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t _ => .throwRefHandlerCatchAll⟩
  | throwRefHandlerCatchAllRef =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t _ => .throwRefHandlerCatchAllRef⟩
  | throwRefHandlerNext hn =>
    intro n cs b hc _
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨rfl, rfl, fun t hex => .throwRefHandlerNext
      (by rwa [← catchMatches_congr hex])⟩
  | _ =>
    intro n cs b hc _
    first
      | (have hl := congrArg List.getLast? hc
         simp [constI32] at hl
         done)
      | (have hl := congrArg List.getLast? hc
         simp at hl
         subst hl
         simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])

theorem handler_kernel {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {b is' : List Admin} (hb : b = [.trap] ∨ ∃ a, b = throwing a)
    (h : Step P host ⟨s, f, [.handler n cs b]⟩ ⟨s', f', is'⟩) :
    s' = s ∧ f' = f ∧ ∀ t : Store H, s.exns = t.exns →
      Step P host ⟨t, f, [.handler n cs b]⟩ ⟨t, f, is'⟩ :=
  handler_kernel_aux h n cs b rfl hb

/-- **A step at a handler head.** -/
theorem fwd_handler {tl : Bool} {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {b b' rest y x' : List Admin}
    (ih : FIH P host (codeSize (vals V ++ .handler n cs b :: rest)))
    (hst : StoreRel FRel s t) (hb : R true false b b') (hr : R true tl rest y)
    (hTs : ContextTyped ⟨s, f, vals V ++ .handler n cs b :: rest⟩)
    (hTt : ContextTyped ⟨t, f, vals V ++ .handler n cs b' :: y⟩)
    (h : Step P host ⟨s, f, vals V ++ .handler n cs b :: rest⟩ ⟨s', f', x'⟩) :
    FM P host tl s' f' x' t f (vals V ++ .handler n cs b' :: y)
      (codeSize (vals V ++ .handler n cs b :: rest)) := by
  rcases Step.split_head rfl h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is₂, hinv, rfl⟩ := Step.handler_inv hs
  have e1 : vals ws ++ (vals us ++ is₂) ++ rest = vals (ws ++ us) ++ is₂ ++ rest := by simp
  rw [e1]
  generalize ws ++ us = W at *
  have e2 : vals W ++ Admin.handler n cs b :: rest = vals W ++ [.handler n cs b] ++ rest := by simp
  have e3 : vals W ++ Admin.handler n cs b' :: y = vals W ++ [.handler n cs b'] ++ y := by simp
  rw [e2] at hTs ih ⊢
  rw [e3] at hTt ⊢
  clear hs
  rcases hinv with ⟨b₂, hs₁, rfl⟩ | ⟨hs', hf', vs, rfl, rfl⟩ |
      ⟨hs', hf', vs, k, rest₁, hk, rfl, rfl⟩ | ⟨hk, hk0⟩
  · obtain ⟨t', b₂', hm, hst', hR'⟩ := ih (Closure.codeSize_handler_body_lt W rest n cs b)
      hst hb (ContextTyped.handler hTs) (ContextTyped.handler hTt) hs₁
    refine ⟨t', vals W ++ [.handler n cs b₂'] ++ y, ?_, hst',
      by simpa using R.valPre (R.handler (n := n) (cs := cs) hR' hr) W⟩
    rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid (trans_handler hT) W y)
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.handler_lt (vals W) rest n cs hlt⟩
  · subst s' f'
    rw [R.vals_inv hb]
    refine FM.of_trans (.single (step_mid .handlerVals W y)) hst ?_
    exact R.mid hr W _
  · -- `br`, `return` and `return_call_ref` leave the handler: the same step
    subst s' f'
    have hb' : ∃ y', b' = vals vs ++ k ++ y' := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain (.br l)) trivial (by simpa using hb)
        exact ⟨y', by simp⟩
      · obtain ⟨y', rfl, -⟩ := R.kernel_inv (k := .plain .return_) trivial (by simpa using hb)
        exact ⟨y', by simp⟩
      · obtain ⟨V₀, V₁, y₀, hV, rfl, hh⟩ := R.split (Admin.val?_of_isReturnCallRef hc)
          (by simpa using hb)
        cases hh with
        | @same _ _ _ y₁ _ _ =>
          refine ⟨y₁, ?_⟩
          simp only [List.append_nil] at hV
          subst hV
          simp
        | label => exact hc.elim
        | handler => exact hc.elim
        | frame => exact hc.elim
        | call => exact hc.elim
        | trap => exact hc.elim
        | throw => exact hc.elim
    obtain ⟨y', rfl⟩ := hb'
    have hstep : Step P host ⟨t, f, [.handler n cs (vals vs ++ k ++ y')]⟩ ⟨t, f, vals vs ++ k⟩ := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact .brHandler
      · exact .returnHandler
      · exact .returnCallRefHandler hc
    exact FM.of_trans (.single (step_mid hstep W y)) hst
      (R.mid hr W _)
  · -- `trap-handler` and `throw_ref-handler-*`: the target's body reaches the same kernel
    obtain ⟨hs', hf', hstep⟩ := handler_kernel hk hk0
    subst s' f'
    have hrun : Steps P host ⟨t, f, [.handler n cs b']⟩ ⟨t, f, [.handler n cs b]⟩ := by
      rcases hk with rfl | ⟨a, rfl⟩
      · exact Steps.handler (TA.run (R.trap_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)))
      · exact Steps.handler (TT.run (R.throw_inv (V := []) (rest := []) (by simpa [Sim.vals_nil'] using hb)))
    have hex : s.exns = t.exns := StoreRel.exns_eq hst
    have hT := Relation.TransGen.tail' hrun (hstep t hex)
    exact FM.of_trans (trans_mid hT W y) hst (R.mid hr W _)

end Silmaril.Raw.Wasm.LimeCompile.TailSim
