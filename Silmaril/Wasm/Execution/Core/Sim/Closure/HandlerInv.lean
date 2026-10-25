module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

@[expose] public section

/-! # Inversion of a step at a `HANDLER` head

`Step.handler_inv`: a step of `val* (HANDLER_n{cs} b)` keeps the value prefix and
is `ctxt-handler`, `handler-vals`, a `br`/`return`/`return_call_ref` bubbling
(`br-handler`, `return-handler`, `return_call_ref-handler`), or a step of
`HANDLER_n{cs} b` whose body is `trap` or a thrown exception (`trap-handler`,
`throw_ref-handler-*`). The delegated step families never end in a `HANDLER`. -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem ParametricStep.getLast_ne_handler {is is' : List Admin} (h : ParametricStep is is')
    (n : Nat) (cs : List Catch) (b : List Admin) : is.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

theorem NumericStep.getLast_ne_handler {is is' : List Admin} (h : NumericStep P is is')
    (n : Nat) (cs : List Catch) (b : List Admin) : is.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp

theorem VectorStep.getLast_ne_handler {is is' : List Admin} (h : VectorStep P is is')
    (n : Nat) (cs : List Catch) (b : List Admin) : is.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

theorem VariableStep.getLast_ne_handler {c c' : Config H} (h : VariableStep c c')
    (n : Nat) (cs : List Catch) (b : List Admin) : c.code.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp

theorem TableStep.getLast_ne_handler {c c' : Config H} (h : TableStep P c c')
    (n : Nat) (cs : List Catch) (b : List Admin) : c.code.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

theorem MemoryStep.getLast_ne_handler {c c' : Config H} (h : MemoryStep P c c')
    (n : Nat) (cs : List Catch) (b : List Admin) : c.code.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

theorem RefStep.getLast_ne_handler {c c' : Config H} (h : RefStep c c')
    (n : Nat) (cs : List Catch) (b : List Admin) : c.code.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

theorem AggregateStep.getLast_ne_handler {c c' : Config H} (h : AggregateStep c c')
    (n : Nat) (cs : List Catch) (b : List Admin) : c.code.getLast? ≠ some (.handler n cs b) := by
  cases h <;> simp [constI32]

/-- A singleton is `val* y` only without values. -/
theorem singleton_eq_vals_append {x y : Admin} {us : List Val} (h : [x] = vals us ++ [y]) :
    us = [] ∧ x = y := by
  rcases us with _ | ⟨u, us⟩
  · simpa [vals_nil'] using h
  · rw [vals_cons', List.cons_append, List.cons.injEq] at h
    exact absurd h.2.symm (by simp)

/-- The shapes of a step at `HANDLER_n{cs} b`, producing `is'`. -/
def HandlerInv (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (n : Nat)
    (cs : List Catch) (b : List Admin) (s' : Store H) (f' : Frame) (is' : List Admin) : Prop :=
  (∃ b', Step P host ⟨s, f, b⟩ ⟨s', f', b'⟩ ∧ is' = [.handler n cs b']) ∨
  (s' = s ∧ f' = f ∧ ∃ vs : List Val, b = vals vs ∧ is' = vals vs) ∨
  (s' = s ∧ f' = f ∧ ∃ (vs : List Val) (k rest : List Admin),
    ((∃ l, k = [.plain (.br l)]) ∨ k = [.plain .return_] ∨
      ∃ c : Admin, c.IsReturnCallRef ∧ k = [c]) ∧
    b = vals vs ++ k ++ rest ∧ is' = vals vs ++ k) ∨
  ((b = [.trap] ∨ ∃ a, b = throwing a) ∧ Step P host ⟨s, f, [.handler n cs b]⟩ ⟨s', f', is'⟩)

set_option linter.unusedSimpArgs false in
theorem Step.handler_inv_aux {c c' : Config H} (h : Step P host c c') :
    Step P host c c' → ∀ (us : List Val) (n : Nat) (cs : List Catch) (b : List Admin),
      c.code = vals us ++ [.handler n cs b] →
      ∃ is', HandlerInv P host c.store c.frame n cs b c'.store c'.frame is' ∧
        c'.code = vals us ++ is' := by
  induction h with
  | parametric hp =>
    intro _ us n cs b hc
    exact (ParametricStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | numeric hp =>
    intro _ us n cs b hc
    exact (NumericStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | vector hp =>
    intro _ us n cs b hc
    exact (VectorStep.getLast_ne_handler hp n cs b (by dsimp only at hc; rw [hc]; simp)).elim
  | «variable» hp =>
    intro _ us n cs b hc
    exact (VariableStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | table hp =>
    intro _ us n cs b hc
    exact (TableStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | memory hp =>
    intro _ us n cs b hc
    exact (MemoryStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | reference hp =>
    intro _ us n cs b hc
    exact (RefStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | aggregate hp =>
    intro _ us n cs b hc
    exact (AggregateStep.getLast_ne_handler hp n cs b (by rw [hc]; simp)).elim
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro _ us n cs b hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, e, es₁, he, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc ⊢
    have hc' : vals (vs₀ ++ vs₁) ++ e :: (es₁ ++ rest) = vals us ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj he rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨is'', hinv, heq⟩ := ih hs vs₁ n cs b rfl
    exact ⟨is'', hinv, by dsimp only at heq; rw [heq]; simp⟩
  | @trapInstrs _ _ vs₀ rest hne =>
    intro _ us n cs b hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp
    exact absurd (vals_append_cons_inj val?_trap rfl hc').2.1 (by simp)
  | @throwRefInstrs _ _ vs₀ x rest hne =>
    intro _ us n cs b hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.handler n cs b :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    exact absurd (vals_append_cons_inj val?_throwRef rfl hc').2.1 (by simp)
  | @ctxtHandler _ _ _ _ _ _ _ is' hs _ =>
    intro _ us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inl ⟨is', hs, rfl⟩, by simp [vals_nil']⟩
  | handlerVals =>
    intro _ us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inl ⟨rfl, rfl, _, rfl, rfl⟩), by simp [vals_nil']⟩
  | brHandler =>
    intro _ us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, _, [.plain (.br _)], _, Or.inl ⟨_, rfl⟩, rfl,
      rfl⟩)), by simp [vals_nil']⟩
  | returnHandler =>
    intro _ us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, _, [.plain .return_], _, Or.inr (Or.inl rfl),
      rfl, rfl⟩)), by simp [vals_nil']⟩
  | returnCallRefHandler hc₀ =>
    intro _ us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, _, [_], _, Or.inr (Or.inr ⟨_, hc₀, rfl⟩),
      rfl, rfl⟩)), by simp [vals_nil']⟩
  | trapHandler =>
    intro h0 us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, h0⟩)), by simp [vals_nil']⟩
  | throwRefHandlerEmpty | throwRefHandlerCatch | throwRefHandlerCatchRef
  | throwRefHandlerCatchAll | throwRefHandlerCatchAllRef | throwRefHandlerNext =>
    intro h0 us n cs b hc
    obtain ⟨rfl, he⟩ := singleton_eq_vals_append hc
    cases he
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨_, rfl⟩, h0⟩)), by simp [vals_nil']⟩
  | _ =>
    intro _ us n cs b hc
    first
      | (obtain ⟨-, he⟩ := singleton_eq_vals_append hc; cases he; done)
      | (have hl := congrArg List.getLast? hc
         simp [constI32] at hl
         done)
      | (have hl := congrArg List.getLast? hc
         simp at hl
         subst hl
         simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])

/-- **Inversion at a `HANDLER` head.** -/
theorem Step.handler_inv {s s' : Store H} {f f' : Frame} {us : List Val} {n : Nat}
    {cs : List Catch} {b es' : List Admin}
    (h : Step P host ⟨s, f, vals us ++ [.handler n cs b]⟩ ⟨s', f', es'⟩) :
    ∃ is', HandlerInv P host s f n cs b s' f' is' ∧ es' = vals us ++ is' :=
  Step.handler_inv_aux h h us n cs b rfl

end Silmaril.Wasm.Execution.Core.Sim
