module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # Closure proof: `LABEL` heads

`label_case`: a step at `val* (LABEL_n{cont} b) L`. `Step.label_inv` inverts the
step to a reduction of the `LABEL` redex (`LabelRed`) under the value prefix.
`ctxt-label` is matched by the induction hypothesis `StepIH` (the body is strictly
smaller), lifted with `Step.ctxtLabel` and context lifting; the bubbling rules
(`label-vals`, `br-label-zero`, `br-label-succ`, `return-label`,
`return_call_ref-label`, `trap-label`, `throw_ref-label`) after `Closure.run_vals`
or `Closure.exit_lift` on the related body (`body_exit`, `body_kernel`); `br`-zero
continues with `InstrsRel`-related `cont` (`AdminsRel.src`). -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

/-! ## Inversion of `LABEL` steps -/

/-- The reductions of a `LABEL` redex `LABEL_n{cont} b` (`ctxt-label` and the
bubbling rules). -/
inductive LabelRed (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (n : Nat)
    (cont : List Instr) : List Admin → Store H → Frame → List Admin → Prop where
  | ctxt {s' : Store H} {f' : Frame} {b b' : List Admin} :
      Step P host ⟨s, f, b⟩ ⟨s', f', b'⟩ → LabelRed P host s f n cont b s' f' [.label n cont b']
  | values (vs : List Val) : LabelRed P host s f n cont (vals vs) s f (vals vs)
  | brZero {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} : l.toNat = 0 →
      vs.length = n →
      LabelRed P host s f n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) s f
        (vals vs ++ expression cont)
  | brSucc {vs : List Val} {l : LabelIdx} {rest : List Admin} : 0 < l.toNat →
      LabelRed P host s f n cont (vals vs ++ [.plain (.br l)] ++ rest) s f
        (vals vs ++ [.plain (.br (labelPred l))])
  | returnCallRef {vs : List Val} {c : Admin} {rest : List Admin} : c.IsReturnCallRef →
      LabelRed P host s f n cont (vals vs ++ [c] ++ rest) s f (vals vs ++ [c])
  | return_ {vs : List Val} {rest : List Admin} :
      LabelRed P host s f n cont (vals vs ++ [.plain .return_] ++ rest) s f
        (vals vs ++ [.plain .return_])
  | throwRef (a : Nat) : LabelRed P host s f n cont (throwing a) s f (throwing a)
  | trap : LabelRed P host s f n cont [.trap] s f [.trap]

theorem label_single_eq {us : List Val} {n n' : Nat} {cont cont' : List Instr}
    {b b' : List Admin} (h : [Admin.label n cont b] = vals us ++ [.label n' cont' b']) :
    us = [] ∧ n = n' ∧ cont = cont' ∧ b = b' := by
  cases us with
  | nil =>
    simp [vals_nil'] at h
    exact ⟨rfl, h⟩
  | cons v us =>
    have := congrArg List.length h
    simp at this

set_option linter.unusedSimpArgs false in
theorem Step.label_inv_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (n : Nat) (cont : List Instr) (b : List Admin),
      c.code = vals us ++ [.label n cont b] →
      ∃ is', LabelRed P host c.store c.frame n cont b c'.store c'.frame is' ∧
        c'.code = vals us ++ is' := by
  induction h with
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs _ ih =>
    intro us n cont b hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, a, es₁, ha, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc
    have hc' : vals (vs₀ ++ vs₁) ++ a :: (es₁ ++ rest) =
        vals us ++ Admin.label n cont b :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj ha rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨is', hr, he⟩ := ih vs₁ n cont b rfl
    refine ⟨is', hr, ?_⟩
    dsimp only at he ⊢
    rw [he]
    simp
  | ctxtLabel hs _ =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .ctxt hs, by simp [vals_nil']⟩
  | labelVals =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .values _, by simp [vals_nil']⟩
  | brLabelZero hl hn =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .brZero hl hn, by simp [vals_nil']⟩
  | brLabelSucc hl =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .brSucc hl, by simp [vals_nil']⟩
  | returnCallRefLabel hrc =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .returnCallRef hrc, by simp [vals_nil']⟩
  | returnLabel =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .return_, by simp [vals_nil']⟩
  | throwRefLabel =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .throwRef _, by simp [vals_nil']⟩
  | trapLabel =>
    intro us n cont b hc
    obtain ⟨rfl, rfl, rfl, rfl⟩ := label_single_eq hc
    exact ⟨_, .trap, by simp [vals_nil']⟩
  | @trapInstrs _ _ vs₀ rest _ =>
    intro us n cont b hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.label n cont b :: [] := by
      rw [← hc]; simp
    obtain ⟨-, h2, -⟩ := vals_append_cons_inj val?_trap rfl hc'
    cases h2
  | @throwRefInstrs _ _ vs₀ x rest _ =>
    intro us n cont b hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.label n cont b :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, h2, -⟩ := vals_append_cons_inj val?_throwRef rfl hc'
    cases h2
  | parametric hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | numeric hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | vector hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | «variable» hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | table hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | memory hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32, store8, load8u] at hl
  | reference hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | aggregate hp =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | _ =>
    intro us n cont b hc
    have hl := congrArg List.getLast? hc
    simp [constI32] at hl
    all_goals (subst hl; simp [Admin.IsCallRef, Admin.IsReturnCallRef] at *)

/-- **`LABEL` inversion.** A step of `val* (LABEL_n{cont} b)` is a reduction of the
`LABEL` redex, under the value prefix. -/
theorem Step.label_inv {s s' : Store H} {f f' : Frame} {us : List Val} {n : Nat}
    {cont : List Instr} {b es' : List Admin}
    (h : Step P host ⟨s, f, vals us ++ [.label n cont b]⟩ ⟨s', f', es'⟩) :
    ∃ is', LabelRed P host s f n cont b s' f' is' ∧ es' = vals us ++ is' :=
  Step.label_inv_aux h us n cont b rfl

/-! ## Lifting runs through contexts -/

theorem transGen_map (g : Config H → Config H)
    (hg : ∀ {c d : Config H}, Step P host c d → Step P host (g c) (g d)) {c d : Config H}
    (h : Relation.TransGen (Step P host) c d) : Relation.TransGen (Step P host) (g c) (g d) := by
  induction h with
  | single hs => exact .single (hg hs)
  | tail _ hs ih => exact ih.tail (hg hs)

theorem steps_map (g : Config H → Config H)
    (hg : ∀ {c d : Config H}, Step P host c d → Step P host (g c) (g d)) {c d : Config H}
    (h : Steps P host c d) : Steps P host (g c) (g d) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hg hs)

/-- A run of `a` is a run of `val* a L`. -/
theorem transGen_ctx {t t' : Store H} {f f' : Frame} {a a' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, f, a⟩ ⟨t', f', a'⟩) (V : List Val) (L : List Admin) :
    Relation.TransGen (Step P host) ⟨t, f, vals V ++ a ++ L⟩ ⟨t', f', vals V ++ a' ++ L⟩ :=
  transGen_map (fun c => ⟨c.store, c.frame, vals V ++ c.code ++ L⟩)
    (fun {c d} hs => by
      obtain ⟨_, _, _⟩ := c
      obtain ⟨_, _, _⟩ := d
      exact Step.append_right (Step.vals_left hs V) L) h

/-- A run of `b` is a run of `LABEL_n{cont} b`. -/
theorem steps_label {t t' : Store H} {f f' : Frame} {b b' : List Admin}
    (h : Steps P host ⟨t, f, b⟩ ⟨t', f', b'⟩) (n : Nat) (cont : List Instr) :
    Steps P host ⟨t, f, [.label n cont b]⟩ ⟨t', f', [.label n cont b']⟩ :=
  steps_map (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (fun {c d} hs => by
      obtain ⟨_, _, _⟩ := c
      obtain ⟨_, _, _⟩ := d
      exact Step.ctxtLabel hs) h

/-- A nonempty run of `b` is a nonempty run of `LABEL_n{cont} b`. -/
theorem transGen_label {t t' : Store H} {f f' : Frame} {b b' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, f, b⟩ ⟨t', f', b'⟩) (n : Nat) (cont : List Instr) :
    Relation.TransGen (Step P host) ⟨t, f, [.label n cont b]⟩ ⟨t', f', [.label n cont b']⟩ :=
  transGen_map (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (fun {c d} hs => by
      obtain ⟨_, _, _⟩ := c
      obtain ⟨_, _, _⟩ := d
      exact Step.ctxtLabel hs) h

/-! ## Sizes -/

theorem codeSize_label_body (n : Nat) (cont : List Instr) (b : List Admin) :
    codeSize b < codeSize [Admin.label n cont b] := by
  simp [codeSize]; omega

theorem codeSize_le_ctx (V : List Val) (x : List Admin) (L : List Admin) :
    codeSize x ≤ codeSize (vals V ++ x ++ L) := by
  have h1 := codeSize_append (vals V ++ x) L
  have h2 := codeSize_append (vals V) x
  have h3 := codeSize_pos (vals V)
  have h4 := codeSize_pos L
  omega

theorem codeSize_label_lt {n : Nat} {cont : List Instr} {b₁ b : List Admin}
    (h : codeSize b₁ < codeSize b) (V : List Val) (L : List Admin) :
    codeSize (vals V ++ [.label n cont b₁] ++ L) < codeSize (vals V ++ [.label n cont b] ++ L) := by
  have h1 := codeSize_append (vals V ++ [.label n cont b₁]) L
  have h2 := codeSize_append (vals V) [.label n cont b₁]
  have h3 := codeSize_append (vals V ++ [.label n cont b]) L
  have h4 := codeSize_append (vals V) [.label n cont b]
  have h5 : codeSize [Admin.label n cont b₁] < codeSize [Admin.label n cont b] := by
    simp [codeSize] at h ⊢; omega
  omega

/-! ## Exits of a related body -/

omit [LawfulCodeRank rank] in
/-- A related body whose left side exits by `br`, `return` or `return_call_ref`
runs on the right to the same exit after the same values. -/
theorem body_exit (hB : BaseFacts P host F BI B rank) {s t : Store H} {f : Frame} {b b' : List Admin}
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b') {us : List Val}
    {k j : List Admin} (hk : Exit k) (hnk : ¬ (k = [.trap] ∨ ∃ a, k = throwing a))
    (hx : b = vals us ++ k ++ j) :
    ∃ (t' : Store H) (j' : List Admin), Steps P host ⟨t, f, b'⟩ ⟨t', f, vals us ++ k ++ j'⟩ ∧
      StoreRel F s t' := by
  obtain ⟨t', us', j', h', hst', hor⟩ :=
    exit_lift hB (AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb) hst (f := f) [] hk hx
  rcases hor with rfl | hc
  · exact ⟨t', j', steps_congr h' (by simp [vals_nil']) (by simp [vals_nil']), hst'⟩
  · exact (hnk hc).elim

omit [LawfulCodeRank rank] in
/-- A related body whose left side is exactly `trap` or a thrown exception runs on
the right to exactly that kernel. -/
theorem body_kernel (hB : BaseFacts P host F BI B rank) {s t : Store H} {f : Frame}
    {b b' k : List Admin} (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hk : k = [.trap] ∨ ∃ a, k = throwing a) (hbk : b = k) :
    ∃ t' : Store H, Steps P host ⟨t, f, b'⟩ ⟨t', f, k⟩ ∧ StoreRel F s t' := by
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb
  have hk' : Exit k := by
    rcases hk with rfl | ⟨a, rfl⟩
    exacts [Exit.trap, Exit.throw a]
  obtain ⟨t', us', j', h', hst', -⟩ := exit_lift hB hsegs hst (f := f) [] hk' (us := [])
    (j := []) (by simp [hbk, vals_nil'])
  have h'' : Steps P host ⟨t, f, b'⟩ ⟨t', f, vals us' ++ k ++ j'⟩ :=
    steps_congr h' (by simp [vals_nil']) (by simp [vals_nil'])
  refine ⟨t', ?_, hst'⟩
  by_cases hne : us' ≠ [] ∨ j' ≠ []
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact h''.tail (Step.trapInstrs hne)
    · exact h''.tail (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals_nil'] using h''

/-! ## The case -/

set_option linter.unusedVariables false in
/-- A step at a `LABEL` head: the inner step by the induction hypothesis, or a
bubbling rule matched after `exit_lift` of the related body. -/
theorem label_case_of_body (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseFacts P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cont cont' : List Instr}
    {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P host ⟨s, f, b⟩ c' →
      RankedMatched rank P host F BI B c' ⟨t, f, b'⟩ (rank b))
    (hst : StoreRel F s t) (hcont : InstrsRel BI cont cont')
    (hb : AdminsRel BI (WithCuts B) b b') (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩
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
    obtain ⟨t', hrun, hst'⟩ := run_vals hB (AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hb)
      (by simp) (f := f) [] hst
    have hrun' : Steps P host ⟨t, f, b'⟩ ⟨t', f, vals vs⟩ :=
      steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, vals vs⟩ :=
      Relation.TransGen.tail' (steps_label hrun' n cont') Step.labelVals
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @brZero vs₀ vs l rest hl hn =>
    obtain ⟨t', j', hrun, hst'⟩ := body_exit hB hst hb (f := f) (Exit.br l)
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs₀ ++ vs) (j := rest) (by simp)
    rw [vals_append] at hrun
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ expression cont'⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.brLabelZero hl hn)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl,
      ((AdminsRel.vals V).append ((AdminsRel.vals vs).append (AdminsRel.src hcont))).append hL⟩
  | @brSucc vs l rest hl =>
    obtain ⟨t', j', hrun, hst'⟩ := body_exit hB hst hb (f := f) (Exit.br l)
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [.plain (.br (labelPred l))]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.brLabelSucc hl)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @returnCallRef vs c rest hrc =>
    obtain ⟨t', j', hrun, hst'⟩ := body_exit hB hst hb (f := f) (Exit.returnCallRef hrc)
      (by
        rintro (h | ⟨a, h⟩) <;> simp [throwing] at h
        subst h
        simp [Admin.IsReturnCallRef] at hrc) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [c]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') (Step.returnCallRefLabel hrc)
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | @return_ vs rest =>
    obtain ⟨t', j', hrun, hst'⟩ := body_exit hB hst hb (f := f) Exit.return_
      (by rintro (h | ⟨a, h⟩) <;> simp [throwing] at h) (us := vs) (j := rest) rfl
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩
        ⟨t', f, vals vs ++ [.plain .return_]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.returnLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | throwRef a =>
    obtain ⟨t', hrun, hst'⟩ := body_kernel hB hst hb (f := f) (Or.inr ⟨a, rfl⟩) rfl
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, throwing a⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.throwRefLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩
  | trap =>
    obtain ⟨t', hrun, hst'⟩ := body_kernel hB hst hb (f := f) (Or.inl rfl) rfl
    have T : Relation.TransGen (Step P host) ⟨t, f, [.label n cont' b']⟩ ⟨t', f, [.trap]⟩ :=
      Relation.TransGen.tail' (steps_label hrun n cont') Step.trapLabel
    exact ⟨_, Or.inl (transGen_ctx T V L'), hst', rfl, (AdminsRel.refl _).append hL⟩


/-- Compatibility form using the unrestricted rank induction hypothesis. -/
theorem label_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cont cont' : List Instr}
    {b b' L L' es' : List Admin}
    (ih : RankedStepIH rank P host F BI B (rank (vals V ++ [.label n cont b] ++ L)))
    (hst : StoreRel F s t) (hcont : InstrsRel BI cont cont')
    (hb : AdminsRel BI (WithCuts B) b b') (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩
      (rank (vals V ++ [.label n cont b] ++ L)) := by
  apply label_case_of_body hF hhost hB.toBaseFacts ?_ hst hcont hb hL h
  intro c' hs
  exact ih (c := ⟨s, f, b⟩) (d := ⟨t, f, b'⟩) (LawfulCodeRank.label_body_lt (vals V) L n cont b) ⟨hst, rfl, hb⟩ hs

end Closure

end Silmaril.Wasm.Execution.Core.Sim
