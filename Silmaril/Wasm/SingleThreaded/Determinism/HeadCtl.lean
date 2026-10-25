module

public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

/-! # Determinism of control head steps

Two control head steps at the same instruction, whose value arguments are
suffixes of one another, consume the same arguments and have joinable results.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

theorem p_nil_of_len {α : Type _} {a p b : List α} (hp : a = p ++ b)
    (h : a.length = b.length) : p = [] := by
  subst hp; simpa using h

theorem singleton_hp {α : Type _} {x y : α} {p : List α} (hp : [x] = p ++ [y]) :
    p = [] ∧ x = y := by
  rcases p with _ | ⟨a, p⟩
  · simpa using hp
  · simp at hp

theorem singleton_hp' {α : Type _} {x y : α} {p l : List α} (hp : [x] = p ++ (l ++ [y])) :
    p = [] ∧ l = [] ∧ x = y := by
  rw [← List.append_assoc] at hp
  obtain ⟨h1, rfl⟩ := singleton_hp hp
  simp only [List.append_eq_nil_iff] at h1
  exact ⟨h1.1, h1.2, rfl⟩

theorem last_hp {α : Type _} {x y : α} {p l₁ l₂ : List α} (hp : l₁ ++ [x] = p ++ (l₂ ++ [y])) :
    l₁ = p ++ l₂ ∧ x = y := by
  rw [← List.append_assoc] at hp
  exact append_singleton_inj.mp hp

theorem suffix_len {α : Type _} {a b c d : List α} (h : a ++ b = c ++ d)
    (hl : b.length = d.length) : a = c ∧ b = d :=
  List.append_inj' h hl

theorem Step.fnv_good {P : Profile} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (h : Step P noHost ⟨s, f, code⟩ c) :
    ∀ e rest, (fnv code).2 = e :: rest → ¬ Blocked e := by
  intro e rest hf
  exact not_step_blocked h (W := (fnv code).1) (by rw [← hf])

open Lean Meta Elab Tactic in
/-- Add `val? = none` facts for every `IsReturnCallRef`/`IsCallRef` hypothesis. -/
elab "vn_all" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let t ← instantiateMVars ldecl.type
      if t.isAppOfArity ``Silmaril.Wasm.Execution.Core.Admin.IsReturnCallRef 1 then
        let pf ← mkAppM ``Silmaril.Wasm.SingleThreaded.Det.IsReturnCallRef.val_none #[ldecl.toExpr]
        let (_, g') ← g.note `hvn pf
        g := g'
      else if t.isAppOfArity ``Silmaril.Wasm.Execution.Core.Admin.IsCallRef 1 then
        let pf ← mkAppM ``Silmaril.Wasm.SingleThreaded.Det.IsCallRef.val_none #[ldecl.toExpr]
        let (_, g') ← g.note `hvn pf
        g := g'
    replaceMainGoal [g]

theorem ctxt_label_join {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f f₁ f₂ : Frame} {n : Nat} {cont : List Instr} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.label n cont is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Join (DStep o) c₁ c₂)
    (h₁ : DStep o ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : DStep o ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (DStep o) ⟨s₁, f₁, [.label n cont is₁]⟩ ⟨s₂, f₂, [.label n cont is₂]⟩ :=
  ⟨by simpa using hp, Join.map (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩)
    (lift_label n cont) (ih s f is _ _ (by simp; omega) h₁ h₂)⟩

theorem ctxt_handler_join {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f f₁ f₂ : Frame} {n : Nat} {cs : List Catch} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.handler n cs is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Join (DStep o) c₁ c₂)
    (h₁ : DStep o ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : DStep o ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (DStep o) ⟨s₁, f₁, [.handler n cs is₁]⟩ ⟨s₂, f₂, [.handler n cs is₂]⟩ :=
  ⟨by simpa using hp, Join.map (fun c => ⟨c.store, c.frame, [.handler n cs c.code]⟩)
    (lift_handler n cs) (ih s f is _ _ (by simp; omega) h₁ h₂)⟩

theorem ctxt_frame_join {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f fi fi₁ fi₂ : Frame} {n : Nat} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.frame n fi is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Join (DStep o) c₁ c₂)
    (h₁ : DStep o ⟨s, fi, is⟩ ⟨s₁, fi₁, is₁⟩) (h₂ : DStep o ⟨s, fi, is⟩ ⟨s₂, fi₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (DStep o) ⟨s₁, f, [.frame n fi₁ is₁]⟩ ⟨s₂, f, [.frame n fi₂ is₂]⟩ :=
  ⟨by simpa using hp, Join.map (fun c => ⟨c.store, f, [.frame n c.frame c.code]⟩)
    (lift_frame n f) (ih s fi is _ _ (by simp; omega) h₁ h₂)⟩

set_option hygiene false in
/-- An inner step of a context rule at a blocked or finished body is impossible. -/
macro "ctl_step" : tactic => `(tactic| (
  exfalso
  have hg := Step.fnv_good ‹Step _ _ _ _›
  simp (disch := first | assumption | rfl) [fnv_cons_of_none, Blocked, List.append_assoc,
    List.cons_append, List.singleton_append, Admin.IsReturnCallRef] at hg
  try exact hg (IsReturnCallRef.blocked ‹_›)
  done))

set_option hygiene false in
/-- Compare two body decompositions. -/
macro "ctl_body" : tactic => `(tactic| (
  fnv_all
  simp (disch := first | assumption | rfl) [fnv_cons_of_none, List.append_assoc,
    List.cons_append, List.singleton_append] at hfnv
  try simp [Admin.IsReturnCallRef] at *
  done))

theorem IsReturnCallRef.cases {c : Admin} (h : c.IsReturnCallRef) :
    (∃ x, c = .plain (.returnCallRef x)) ∨ (∃ d, c = .returnCallRefType d) := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsReturnCallRef] at h
  · cases i <;> simp at h; exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem IsCallRef.cases {c : Admin} (h : c.IsCallRef) :
    (∃ x, c = .plain (.callRef x)) ∨ (∃ d, c = .callRefType d) := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
  · cases i <;> simp at h; exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

open Lean Meta Elab Tactic in
/-- Split one `IsReturnCallRef c`/`IsCallRef c` hypothesis on a variable `c`. -/
elab "rcr_step" : tactic => withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let t ← instantiateMVars ldecl.type
    let isR := t.isAppOfArity ``Silmaril.Wasm.Execution.Core.Admin.IsReturnCallRef 1
    let isC := t.isAppOfArity ``Silmaril.Wasm.Execution.Core.Admin.IsCallRef 1
    if (isR || isC) && t.appArg!.isFVar then
      let g ← getMainGoal
      let g ← g.rename ldecl.fvarId `hrcr_tmp
      replaceMainGoal [g]
      let h := mkIdent `hrcr_tmp
      let e := mkIdent `hrcr_eq
      if isR then
        evalTactic (← `(tactic| ((obtain ⟨_, $e⟩ | ⟨_, $e⟩ :=
          Silmaril.Wasm.SingleThreaded.Det.IsReturnCallRef.cases $h) <;> subst $e <;> clear $h)))
      else
        evalTactic (← `(tactic| ((obtain ⟨_, $e⟩ | ⟨_, $e⟩ :=
          Silmaril.Wasm.SingleThreaded.Det.IsCallRef.cases $h) <;> subst $e <;> clear $h)))
      return
  throwError "rcr_step: nothing to split"

set_option hygiene false in
/-- Two rules on singleton arguments. -/
macro "ctl_single" : tactic => `(tactic| (
  obtain ⟨rfl, hx⟩ := singleton_hp hp
  cases hx
  first
  | exact ⟨rfl, Join.rfl'⟩
  | (exfalso; contradiction)
  | (exfalso; simp_all; done)))

set_option hygiene false in
/-- Two rules whose results agree once the body decompositions agree. -/
macro "ctl_same" : tactic => `(tactic| (
  fnv_all
  simp (disch := first | assumption | rfl) [fnv_cons_of_none, Admin.retToCall] at hfnv
  casesm* _ ∧ _
  subst_vars
  first
  | exact ⟨by simpa using hp, Join.rfl'⟩
  | (exfalso; omega)))

theorem frame_body_inj {A B : List Val} {x y : Val} {c d : Admin} {r t : List Admin}
    (hc : c.val? = none) (hd : d.val? = none)
    (h : vals A ++ [x.toAdmin, c] ++ r = vals B ++ [y.toAdmin, d] ++ t) :
    A = B ∧ x = y ∧ c = d ∧ r = t := by
  have e1 : vals A ++ [x.toAdmin, c] ++ r = vals (A ++ [x]) ++ c :: r := by simp
  have e2 : vals B ++ [y.toAdmin, d] ++ t = vals (B ++ [y]) ++ d :: t := by simp
  rw [e1, e2] at h
  obtain ⟨h1, rfl, rfl⟩ := Det.vals_append_cons_inj h hc hd
  obtain ⟨rfl, rfl⟩ := append_singleton_inj.mp h1
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem br_body_inj {A₁ A₂ B₁ B₂ : List Val} {e : Admin} {r t : List Admin}
    (he : e.val? = none) (h : vals A₁ ++ vals A₂ ++ [e] ++ r = vals B₁ ++ vals B₂ ++ [e] ++ t)
    (hn : A₂.length = B₂.length) : A₂ = B₂ := by
  have e1 : vals A₁ ++ vals A₂ ++ [e] ++ r = vals (A₁ ++ A₂) ++ e :: r := by simp
  have e2 : vals B₁ ++ vals B₂ ++ [e] ++ t = vals (B₁ ++ B₂) ++ e :: t := by simp
  rw [e1, e2] at h
  obtain ⟨h1, -, -⟩ := Det.vals_append_cons_inj h he he
  exact (List.append_inj' h1 hn).2

set_option hygiene false in
macro "ctl_vals" : tactic => `(tactic| (
  simp only [vals_inj] at *
  subst_vars
  exact ⟨by simpa using hp, Join.rfl'⟩))

set_option hygiene false in
macro "ctl_catch" : tactic => `(tactic| (
  exfalso
  apply ‹¬ CatchMatches _ _ _ _›
  first
  | exact trivial
  | (simp only [CatchMatches]; exact ⟨_, _, ‹_›, ‹_›, rfl⟩)))

set_option hygiene false in
macro "ctl_block" : tactic => `(tactic| (
  rename_i t₁ t₂ hb₁ t₁' t₂' hm₂ hb₂ hm₁
  rw [hb₁] at hb₂
  cases hb₂
  obtain rfl : p = [] := List.eq_nil_of_length_eq_zero (by simp at hm₁; omega)
  simp only [List.nil_append]
  exact ⟨trivial, Join.rfl'⟩))

set_option maxHeartbeats 0 in
theorem Head.det_ctl {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H} (hk : famOf e = .control)
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
      Join (DStep o) c₁ c₂)
    (h₁ : Head (Profile.deterministic o) s f args₁ e c₁)
    (h₂ : Head (Profile.deterministic o) s f args₂ e c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ Join (DStep o) c₁ c₂ := by
  have hc : ∀ {k : Fam}, famOf e = k → k ≠ .control → False := fun h hk' => hk' (h ▸ hk)
  cases h₁ <;> try fam_excl
  all_goals (cases h₂ <;> try fam_excl)
  all_goals (try hd_close)
  case ctxtLabel.ctxtLabel => exact ctxt_label_join ih ‹_› ‹_› hp
  case ctxtHandler.ctxtHandler => exact ctxt_handler_join ih ‹_› ‹_› hp
  case ctxtFrame.ctxtFrame => exact ctxt_frame_join ih ‹_› ‹_› hp
  all_goals (clear ih hc hk; vn_all; subst_vars)
  all_goals (repeat' rcr_step)
  all_goals (try ctl_single)
  all_goals (try ctl_step)
  all_goals (try ctl_body)
  all_goals (try ctl_same)
  all_goals (try ctl_vals)
  all_goals (try ctl_catch)
  case block.block => ctl_block
  case loop.loop => ctl_block
  case tryTable.tryTable => ctl_block
  case throw.throw =>
    rename_i ta₁ ti₁ ts₁ he₁ ht₁ ta₂ ti₂ ts₂ he₂ hn₂ ht₂ hn₁
    rw [ht₁] at ht₂
    cases ht₂
    cases Expand.det he₁ he₂
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero (by simp at hn₁; omega)
    simp only [List.nil_append]
    exact ⟨trivial, Join.rfl'⟩
  case call.call | returnCall.returnCall =>
    rename_i a₁ fi₁ hf₁ hx₁ a₂ fi₂ hf₂ hx₂
    rw [hx₁] at hx₂
    cases hx₂
    rw [hf₁] at hf₂
    cases hf₂
    exact ⟨by simpa using hp, Join.rfl'⟩
  case throwRefHandlerCatch.throwRefHandlerCatch | throwRefHandlerCatchRef.throwRefHandlerCatchRef =>
    rename_i e₁ he₁ ht₁ e₂ ht₂ he₂
    rw [he₁] at he₂
    cases he₂
    exact ⟨by simpa using hp, Join.rfl'⟩
  case brTableLt.brTableLt =>
    rename_i i₁ ls l' l₁ hi₁ i₂ l₂ hi₂
    obtain ⟨rfl, hx⟩ := singleton_hp hp
    cases hx
    rw [hi₁] at hi₂
    cases hi₂
    exact ⟨rfl, Join.rfl'⟩
  case brLabelZero.brLabelZero =>
    rename_i vs'₁ vs₁ l₁ r₁ hl₁ vs'₂ vs₂ l₂ r₂ hl₂ hn hb
    have h := congrArg fnv hb
    simp at h
    obtain ⟨h1, rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := List.append_inj' h1 hn.symm
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnFrame.returnFrame =>
    rename_i vs'₁ vs₁ r₁ vs'₂ vs₂ r₂ hn hb
    obtain rfl := br_body_inj rfl hb hn.symm
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnCallRefFrameAddr.returnCallRefFrameAddr.inl.inl |
      returnCallRefFrameAddr.returnCallRefFrameAddr.inr.inr =>
    rename_i vs'₁ vs₁ a₁ r₁ fn₁ ps₁ rs₁ hf₁ he₁ hn₁ vs'₂ vs₂ a₂ r₂ fn₂ ps₂ rs₂ hf₂ he₂ hn₂ w₁ hvn₁ w₂ hb
    simp only [← vals_append] at hb
    obtain ⟨h1, hx, hc, -⟩ :=
      frame_body_inj (x := .ref (.func a₁)) (y := .ref (.func a₂)) rfl rfl hb
    cases hx
    cases hc
    rw [hf₁] at hf₂
    cases hf₂
    cases Expand.det he₁ he₂
    obtain ⟨-, rfl⟩ := List.append_inj' h1 (hn₁.trans hn₂.symm)
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnCallRefFrameAddr.returnCallRefFrameNull.inl.inl |
      returnCallRefFrameAddr.returnCallRefFrameNull.inr.inr =>
    rename_i hb
    simp only [← vals_append] at hb
    obtain ⟨-, hx, -⟩ := frame_body_inj (x := .ref (.func _)) (y := .ref .null) rfl rfl hb
    cases hx
  case returnCallRefFrameNull.returnCallRefFrameAddr.inl.inl |
      returnCallRefFrameNull.returnCallRefFrameAddr.inr.inr =>
    rename_i hb
    simp only [← vals_append] at hb
    obtain ⟨-, hx, -⟩ := frame_body_inj (x := .ref .null) (y := .ref (.func _)) rfl rfl hb
    cases hx
  case callRefNull.callRefFunc.inl | callRefNull.callRefFunc.inr =>
    rw [← List.append_assoc] at hp
    obtain ⟨-, hx⟩ := singleton_hp hp
    cases hx
  case callRefFunc.callRefFunc.inl | callRefFunc.callRefFunc.inr =>
    rename_i vs₁ a₁ fi₁ ps₁ rs₁ code₁ hf₁ he₁ hn₁ hcode₁ vs₂ a₂ fi₂ ps₂ rs₂ code₂ hf₂ he₂ hn₂ hcode₂
      ha w hc hvn'
    rw [← List.append_assoc] at ha
    obtain ⟨h1, hx⟩ := append_singleton_inj.mp ha
    cases hx
    rw [hf₁] at hf₂
    cases hf₂
    cases Expand.det he₁ he₂
    rw [hcode₁] at hcode₂
    cases hcode₂
    subst h1
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero (by simp at hn₁; omega)
    simp only [List.nil_append]
    exact ⟨trivial, Join.rfl'⟩

end Silmaril.Wasm.SingleThreaded.Det
