module

public import Silmaril.Wasm.Execution.Core.Sim.TypedKernelNormalization

@[expose] public section

/-! # Runtime contexts with kernel-prefix-aware typed normalization

The target body retains its typing in its original active context. Values,
branches, returns, traps and exceptions therefore use `TypedKernelFacts` rather
than requiring an untyped value law. Computational body steps still use the
supplied induction hypothesis, with the original source rank.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics

variable {H : Type}
local notation "noHost" => (fun _ _ _ _ => False)
variable {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

omit [LawfulCodeRank rank] in
/-- A related body whose left side exits by `br`, `return` or `return_call_ref`
runs on the right to the same exit after the same values. -/
theorem kernel_body_exit (hB : TypedKernelFacts P F BI B) {s t : Store H} {f : Frame} {b b' : List Admin}
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b') {us : List Val}
    {k j : List Admin} (typed : ContextTyped ⟨t, f, b'⟩) (hk : Exit k) (hnk : ¬ (k = [.trap] ∨ ∃ a, k = throwing a))
    (hx : b = vals us ++ k ++ j) :
    ∃ (t' : Store H) (j' : List Admin), Steps P noHost ⟨t, f, b'⟩ ⟨t', f, vals us ++ k ++ j'⟩ ∧
      StoreRel F s t' := by
  obtain ⟨t', us', j', h', hst', hor⟩ :=
    kernel_exit_lift hB (AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb) hst (f := f) [] (by simpa using typed) hk hx
  rcases hor with rfl | hc
  · exact ⟨t', j', steps_congr h' (by simp) (by simp), hst'⟩
  · exact (hnk hc).elim

omit [LawfulCodeRank rank] in
/-- A related body whose left side is exactly `trap` or a thrown exception runs on
the right to exactly that kernel. -/
theorem kernel_body_kernel (hB : TypedKernelFacts P F BI B) {s t : Store H} {f : Frame}
    {b b' k : List Admin} (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (typed : ContextTyped ⟨t, f, b'⟩) (hk : k = [.trap] ∨ ∃ a, k = throwing a) (hbk : b = k) :
    ∃ t' : Store H, Steps P noHost ⟨t, f, b'⟩ ⟨t', f, k⟩ ∧ StoreRel F s t' := by
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  have hk' : Exit k := by
    rcases hk with rfl | ⟨a, rfl⟩
    exacts [Exit.trap, Exit.throw a]
  obtain ⟨t', us', j', h', hst', -⟩ := kernel_exit_lift hB hsegs hst (f := f) [] (by simpa using typed) hk' (us := [])
    (j := []) (by simp [hbk])
  have h'' : Steps P noHost ⟨t, f, b'⟩ ⟨t', f, vals us' ++ k ++ j'⟩ :=
    steps_congr h' (by simp) (by simp)
  refine ⟨t', ?_, hst'⟩
  by_cases hne : us' ≠ [] ∨ j' ≠ []
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact h''.tail (Step.trapInstrs hne)
    · exact h''.tail (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals_nil'] using h''

set_option linter.unusedVariables false in
/-- A step at a `LABEL` head: the inner step by the induction hypothesis, or a
bubbling rule matched after `exit_lift` of the related body. -/
theorem kernel_label_case_of_body (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedKernelFacts P F BI B) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cont cont' : List Instr}
    {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P noHost ⟨s, f, b⟩ c' →
      RankedMatched rank P noHost F BI B c' ⟨t, f, b'⟩ (rank b))
    (hst : StoreRel F s t) (hcont : InstrsRel BI cont cont')
    (hb : AdminsRel BI (WithCuts B) b b') (hL : AdminsRel BI (WithCuts B) L L')
    (typed : ContextTyped ⟨t, f, b'⟩)
    (h : Step P noHost ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P noHost F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩
      (rank (vals V ++ [.label n cont b] ++ L)) := by
  have hlab : (Admin.label n cont b).val? = none := rfl
  rw [show vals V ++ [.label n cont b] ++ L = vals V ++ Admin.label n cont b :: L by simp] at h
  rcases Step.split_head hlab h with ⟨ws, us, is', hVU, hst', rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is'', hr, rfl⟩ := Step.label_inv hst'
  rw [show vals ws ++ (vals us ++ is'') ++ L = vals V ++ is'' ++ L by rw [hVU]; simp]
  clear hst' h
  cases hr with
  | ctxt hs =>
    obtain ⟨⟨t₂, g, b₂⟩, hd, hst₂, hg, hb₂⟩ :=
      ih hs
    refine ⟨⟨t₂, g, vals V ++ [.label n cont' b₂] ++ L'⟩, ?_, hst₂, hg,
      ((AdminsRel.vals V).append
        (AdminsRel.cons (AdminRel.label n hcont hb₂) AdminsRel.nil)).append hL⟩
    rcases hd with hT | ⟨heq, hlt⟩
    · exact Or.inl (transGen_ctx (transGen_label hT n cont') V L')
    · cases heq
      exact Or.inr ⟨rfl, LawfulCodeRank.label_lt (vals V) L n cont hlt⟩
  | values vs =>
    obtain ⟨t', hrun, hst'⟩ := kernel_run_vals hB (AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb)
      (by simp) (f := f) [] hst (by simpa using typed)
    have hrun' : Steps P noHost ⟨t, f, b'⟩ ⟨t', f, vals vs⟩ :=
      steps_congr hrun (by simp) (by simp)
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, vals vs⟩ :=
      Relation.TransGen.tail' (steps_label hrun' n cont') Step.labelVals
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @brZero vs₀ vs l rest hl hn =>
    obtain ⟨t', j', hrun, hst'⟩ := kernel_body_exit hB hst hb (f := f) typed (Exit.br l)
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs₀ ++ vs) (j := rest) (by simp)
    rw [vals_append] at hrun
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ expression cont'⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.brLabelZero hl hn)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl,
      ((AdminsRel.vals V).append ((AdminsRel.vals vs).append (AdminsRel.src hcont))).append hL⟩
  | @brSucc vs l rest hl =>
    obtain ⟨t', j', hrun, hst'⟩ := kernel_body_exit hB hst hb (f := f) typed (Exit.br l)
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [.plain (.br (labelPred l))]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.brLabelSucc hl)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @returnCallRef vs c rest hrc =>
    obtain ⟨t', j', hrun, hst'⟩ := kernel_body_exit hB hst hb (f := f) typed (Exit.returnCallRef hrc)
      (by
        rintro (h | ⟨a, h⟩) <;> simp [throwing] at h
        subst h
        simp [Admin.IsReturnCallRef] at hrc) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [c]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.returnCallRefLabel hrc)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @return_ vs rest =>
    obtain ⟨t', j', hrun, hst'⟩ := kernel_body_exit hB hst hb (f := f) typed Exit.return_
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [.plain .return_]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.returnLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | throwRef a =>
    obtain ⟨t', hrun, hst'⟩ := kernel_body_kernel hB hst hb (f := f) typed (Or.inr ⟨a, rfl⟩) rfl
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, throwing a⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.throwRefLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | trap =>
    obtain ⟨t', hrun, hst'⟩ := kernel_body_kernel hB hst hb (f := f) typed (Or.inl rfl) rfl
    have T : Relation.TransGen (Step P noHost) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, [.trap]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.trapLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩

/-- A step at a `HANDLER` head. -/
theorem kernel_handler_case_of_body (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedKernelFacts P F BI B) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cs : List Catch} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P noHost ⟨s, f, b⟩ c' →
      RankedMatched rank P noHost F BI B c' ⟨t, f, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (typed : ContextTyped ⟨t, f, b'⟩)
    (h : Step P noHost ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P noHost F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩
      (rank (vals V ++ [.handler n cs b] ++ L)) := by
  have hha : (Admin.handler n cs b).val? = none := rfl
  rw [show vals V ++ [.handler n cs b] ++ L = vals V ++ .handler n cs b :: L by simp] at h
  rcases Step.split_head hha h with ⟨ws, us, is', rfl, hst', rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  rotate_left
  · cases hc
  · cases hc
  obtain ⟨is'', hinv, rfl⟩ := Step.handler_inv hst'
  rw [show vals ws ++ (vals us ++ is'') ++ L = vals (ws ++ us) ++ is'' ++ L by simp]
  generalize ws ++ us = W at ⊢
  rcases hinv with ⟨b₁, hstep, rfl⟩ | ⟨hs', hf', vs, rfl, rfl⟩ |
      ⟨hs', hf', vs, k, rest, hk, rfl, rfl⟩ | ⟨hk, hk0⟩
  · -- `ctxt-handler`: the induction hypothesis on the body
    obtain ⟨⟨t₂, f₂, y₂⟩, hm, hst₂, hf₂, hy₂⟩ :=
      ih hstep
    dsimp only at hf₂ hst₂ hy₂ hm
    subst hf₂
    refine ⟨⟨t₂, f', vals W ++ [.handler n cs y₂] ++ L'⟩, ?_, hst₂, rfl,
      ((AdminsRel.vals W).append (AdminsRel.cons (.handler n cs hy₂) .nil)).append hL⟩
    rcases hm with ht | ⟨heq, hlt⟩
    · obtain ⟨⟨t₃, f₃, y₃⟩, hs₃, hl₃⟩ := Relation.TransGen.tail'_iff.mp ht
      exact Or.inl (.tail' (wrap_steps W L' n cs hs₃) (wrap_step W L' n cs (Step.ctxtHandler hl₃)))
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact Or.inr ⟨rfl, LawfulCodeRank.handler_lt (vals W) L n cs hlt⟩
  · -- `handler-vals`
    subst s' f'
    obtain ⟨t₁, hrun, hst₁⟩ := AdminsRel.kernel_values_lift hB (f := f) (vs := []) (us := vs) hst hb (by simpa using typed) rfl
    refine ⟨⟨t₁, f, vals W ++ vals vs ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      (steps_congr hrun (by simp) (by simp))) (wrap_step W L' n cs
        .handlerVals)), hst₁, rfl, ((AdminsRel.vals W).append (AdminsRel.vals vs)).append hL⟩
  · -- `br`/`return`/`return_call_ref` through the handler
    subst s' f'
    have hex : Exit k := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact .br l
      · exact .return_
      · exact .returnCallRef hc
    obtain ⟨t₁, ws', j', hrun, hst₁, hws⟩ := AdminsRel.kernel_exit_lift hB (f := f) (vs := []) (us := vs)
      (j := rest) hst hb (by simpa using typed) hex (by simp)
    have hws' : ws' = vs := by
      rcases hws with h' | h' | ⟨a, h'⟩
      · exact h'
      all_goals exfalso; rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩ <;>
        simp_all [throwing, Admin.IsReturnCallRef]
    rw [hws'] at hrun
    have hbub : Step P noHost ⟨t₁, f, [.handler n cs (vals vs ++ k ++ j')]⟩
        ⟨t₁, f, vals vs ++ k⟩ := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact .brHandler
      · exact .returnHandler
      · exact .returnCallRefHandler hc
    refine ⟨⟨t₁, f, vals W ++ (vals vs ++ k) ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      (steps_congr hrun (by simp) rfl)) (wrap_step W L' n cs hbub)), hst₁, rfl,
      (AdminsRel.refl _).append hL⟩
  · -- `trap-handler` and the `throw_ref-handler-*` rules: same catch clauses, related stores
    have hex : Exit b := by rcases hk with rfl | ⟨a, rfl⟩; exacts [.trap, .throw a]
    obtain ⟨t₁, ws', j', hrun, hst₁, -⟩ := AdminsRel.kernel_exit_lift hB (f := f) (vs := []) (us := [])
      (k := b) (j := []) hst hb (by simpa using typed) hex (by simp)
    obtain ⟨t', es'', hst', hst₂, hres⟩ :=
      Step.match_storeRel (B := WithCuts B) hF hhost hk0 t₁ hst₁
    dsimp only at hst' hst₂ hres
    refine ⟨⟨t', f', vals W ++ es'' ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      ((steps_congr hrun (by simp) rfl).trans
        (steps_kernel hk ws' j'))) (wrap_step W L' n cs hst')), hst₂, rfl,
      ((AdminsRel.vals W).append hres).append hL⟩

omit [LawfulCodeRank rank] in
/-- The tail-call bubbling through a `FRAME` (`return_call_ref-frame-*`): the
related body is lifted to the same `return_call_ref` with the same arguments. -/
theorem kernel_tail_case (hB : TypedKernelFacts P F BI B) {s t : Store H} {f fi : Frame}
    {k : Nat} {b b' es' : List Admin} (hst : StoreRel F s t)
    (hb : AdminsRel BI (WithCuts B) b b')
    (typed : ContextTyped ⟨t, fi, b'⟩)
    (hexit : ∃ (vs : List Val) (c : Admin) (rest : List Admin), c.IsReturnCallRef ∧
      b = vals vs ++ [c] ++ rest)
    (h : Step P noHost ⟨s, f, [.frame k fi b]⟩ ⟨s, f, es'⟩) :
    ∃ t', Relation.TransGen (Step P noHost) ⟨t, f, [.frame k fi b']⟩ ⟨t', f, es'⟩ ∧
      StoreRel F s t' := by
  obtain ⟨vs, c, rest, hc, rfl⟩ := hexit
  have hcv : c.val? = none := Admin.val?_of_isReturnCallRef hc
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  -- the right body reaches the same `return_call_ref` after the same values
  obtain ⟨t', us', j', hrun, hst', hor⟩ := kernel_exit_lift hB hsegs hst (f := fi) [] (by simpa using typed)
    (Exit.returnCallRef hc) (us := vs) (j := rest) rfl
  obtain rfl : us' = vs := by
    rcases hor with h | h | ⟨a, h⟩
    · exact h
    · simp only [List.cons.injEq, and_true] at h; subst h; exact hc.elim
    · simp [throwing] at h
  have hrun' : Steps P noHost ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ [c] ++ j'⟩ :=
    steps_congr hrun (by simp) (by simp)
  obtain ⟨is₀, his, hfr⟩ := Step.frame_redex_aux h [] k fi (vals us' ++ [c] ++ rest) rfl
  dsimp only at his hfr
  rw [vals_nil', List.nil_append] at his
  subst his
  generalize hbd : vals us' ++ [c] ++ rest = bb at hfr
  have hbd' : vals us' ++ c :: rest = bb := by rw [← hbd]; simp
  cases hfr with
  | ctxt hs =>
    exfalso
    rw [← hbd'] at hs
    rcases Step.split_head hcv hs with ⟨ws, us, is', -, hs', -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Step.returnCallRef_stuck_aux hs' us c hc rfl
    · exact hc
    · exact hc
  | values hn =>
    exfalso
    have := congrArg (List.all · Admin.isVal) hbd'
    simp [Admin.isVal, hcv] at this
  | ret hn =>
    rename_i vs₁ vs₂ rest₂
    exfalso
    have e : vals us' ++ c :: rest = vals (vs₁ ++ vs₂) ++ Admin.plain .return_ :: rest₂ := by
      rw [hbd']; simp
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc
  | callNull hc₂ =>
    rename_i vs₂ c₂ rest₂
    have e : vals us' ++ c :: rest = vals (vs₂ ++ [.ref .null]) ++ c₂ :: rest₂ := by
      rw [hbd']; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj hcv (Admin.val?_of_isReturnCallRef hc₂) e
    refine ⟨t', exit_frame hrun' ?_, hst'⟩
    have := Step.returnCallRefFrameNull (P := P) (host := noHost) (s := t') (f := f) (fi := fi)
      (k := k) (vs := vs₂) (rest := j') hc
    simpa [vals, Val.toAdmin] using this
  | callAddr hc₂ hf he hn =>
    rename_i vs₁ vs₂ a c₂ rest₂ fn ps rs
    have e : vals us' ++ c :: rest = vals (vs₁ ++ vs₂ ++ [.ref (.func a)]) ++ c₂ :: rest₂ := by
      rw [hbd']; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, -⟩ := vals_append_cons_inj hcv (Admin.val?_of_isReturnCallRef hc₂) e
    obtain ⟨fn', hf', hty⟩ := hst'.func_type hf
    refine ⟨t', exit_frame hrun' ?_, hst'⟩
    have := Step.returnCallRefFrameAddr (P := P) (host := noHost) (s := t') (f := f) (fi := fi)
      (k := k) (vs' := vs₁) (vs := vs₂) (rest := j') hc hf' (hty ▸ he) hn
    simpa [vals, Val.toAdmin] using this
  | throw =>
    rename_i a
    exfalso
    have e : vals us' ++ c :: rest = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      rw [hbd']; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc
  | trap =>
    exfalso
    have e : vals us' ++ c :: rest = vals [] ++ Admin.trap :: [] := by
      rw [hbd']; simp
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hcv rfl e
    exact hc

/-- A `FRAME` redex step, matched on the right. -/
theorem kernel_frame_redex_case_of_body (hB : TypedKernelFacts P F BI B) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' is₀ : List Admin}
    (ih : ∀ {c' : Config H}, Step P noHost ⟨s, fi, b⟩ c' →
      RankedMatched rank P noHost F BI B c' ⟨t, fi, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (typed : ContextTyped ⟨t, fi, b'⟩)
    (hfr : FrameRedex P noHost s f n fi b s' f' is₀) :
    RankedMatched rank P noHost F BI B ⟨s', f', vals V ++ is₀ ++ L⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  cases hfr with
  | ctxt hs =>
    obtain ⟨d', hm, hrel⟩ := ih hs
    obtain ⟨t', g, b₂⟩ := d'
    obtain ⟨hst', hfg, hb₂⟩ := hrel
    dsimp only at hst' hfg hb₂ hm
    subst hfg
    refine ⟨⟨t', f, vals V ++ [.frame n _ b₂] ++ L'⟩, ?_, hst', rfl,
      ((AdminsRel.vals V).append (.cons (.frame n _ hb₂) .nil)).append hL⟩
    rcases hm with hT | ⟨heq, hlt⟩
    · exact Or.inl (transGen_ctx (transGen_frame hT) V L')
    · simp only [Config.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact Or.inr ⟨rfl, LawfulCodeRank.frame_lt (vals V) L n _ hlt⟩
  | values hn =>
    rename_i vs
    obtain ⟨t', hrun, hst'⟩ := kernel_run_vals hB hsegs (by simp) (f := fi) [] hst (by simpa using typed)
    have hrun' : Steps P noHost ⟨t, fi, b'⟩ ⟨t', fi, vals vs⟩ :=
      steps_congr hrun (by simp) (by simp)
    exact ⟨⟨t', f, vals V ++ vals vs ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame hrun' (Step.frameVals hn)) V L'), hst', rfl,
      (AdminsRel.refl _).append hL⟩
  | ret hn =>
    rename_i vs₁ vs rest
    obtain ⟨t', us', j', hrun, hst', hor⟩ := kernel_exit_lift hB hsegs hst (f := fi) [] (by simpa using typed) Exit.return_
      (us := vs₁ ++ vs) (j := rest) (by simp)
    obtain rfl : us' = vs₁ ++ vs := by
      rcases hor with h | h | ⟨a, h⟩
      · exact h
      · simp at h
      · simp [throwing] at h
    have hrun' : Steps P noHost ⟨t, fi, b'⟩
        ⟨t', fi, vals vs₁ ++ vals vs ++ [.plain .return_] ++ j'⟩ :=
      steps_congr hrun (by simp) (by simp)
    exact ⟨⟨t', f, vals V ++ vals vs ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame hrun' (Step.returnFrame hn)) V L'), hst', rfl,
      (AdminsRel.refl _).append hL⟩
  | callNull hc =>
    rename_i vs c rest
    obtain ⟨t', hT, hst'⟩ := kernel_tail_case hB hst hb typed
      ⟨vs ++ [.ref .null], c, rest, hc, by simp [vals, Val.toAdmin]⟩
      (Step.returnCallRefFrameNull hc)
    exact ⟨_, Or.inl (transGen_ctx hT V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | callAddr hc hf he hn =>
    rename_i vs₁ vs a c rest fn ps rs
    obtain ⟨t', hT, hst'⟩ := kernel_tail_case hB hst hb typed
      ⟨vs₁ ++ vs ++ [.ref (.func a)], c, rest, hc, by simp [vals, Val.toAdmin]⟩
      (Step.returnCallRefFrameAddr hc hf he hn)
    exact ⟨_, Or.inl (transGen_ctx hT V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | throw =>
    rename_i a
    obtain ⟨t', us', j', hrun, hst', -⟩ := kernel_exit_lift hB hsegs hst (f := fi) [] (by simpa using typed) (Exit.throw a)
      (us := []) (j := []) (by simp)
    have hrun' : Steps P noHost ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ throwing a ++ j'⟩ :=
      steps_congr hrun (by simp) (by simp)
    exact ⟨⟨t', f, vals V ++ throwing a ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame (steps_discard (Or.inr ⟨a, rfl⟩) hrun')
        Step.throwRefFrame) V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | trap =>
    obtain ⟨t', us', j', hrun, hst', -⟩ := kernel_exit_lift hB hsegs hst (f := fi) [] (by simpa using typed) Exit.trap
      (us := []) (j := []) (by simp)
    have hrun' : Steps P noHost ⟨t, fi, b'⟩ ⟨t', fi, vals us' ++ [.trap] ++ j'⟩ :=
      steps_congr hrun (by simp) (by simp)
    exact ⟨⟨t', f, vals V ++ [.trap] ++ L'⟩,
      Or.inl (transGen_ctx (exit_frame (steps_discard (Or.inl rfl) hrun')
        Step.trapFrame) V L'), hst', rfl, (AdminsRel.refl _).append hL⟩

theorem kernel_frame_case_of_body (_hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (_hhost : HostRespects F noHost) (hB : TypedKernelFacts P F BI B) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {fi : Frame} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P noHost ⟨s, fi, b⟩ c' →
      RankedMatched rank P noHost F BI B c' ⟨t, fi, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (typed : ContextTyped ⟨t, fi, b'⟩)
    (h : Step P noHost ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P noHost F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (rank (vals V ++ [.frame n fi b] ++ L)) := by
  have ha : (Admin.frame n fi b).val? = none := rfl
  rw [show vals V ++ [.frame n fi b] ++ L = vals V ++ .frame n fi b :: L by simp] at h
  rcases Step.split_head ha h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is₀, his, hfr⟩ := Step.frame_redex_aux hs us n fi b rfl
    dsimp only at his hfr
    subst his hV
    have e : vals ws ++ (vals us ++ is₀) ++ L = vals (ws ++ us) ++ is₀ ++ L := by simp
    rw [e]
    exact kernel_frame_redex_case_of_body hB ih hst hb hL typed hfr
  · cases hc
  · cases hc

end Closure

end Silmaril.Wasm.Execution.Core.Sim
