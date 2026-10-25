module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.HandlerInv
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift

@[expose] public section

/-! # Closure proof: `HANDLER` heads

`handler_case`: a step at `val* (HANDLER_n{cs} b) L`. Plan: `ctxt-handler` by
`StepIH`; the bubbling rules (`handler-vals`, `trap-handler`, the `throw_ref`
catch rules matching `cs`, `br`/`return`/`return_call_ref` through a handler)
after `Closure.exit_lift`; the catch clauses are identical on both sides. -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

theorem codeSize_handler_body_lt (V : List Val) (L : List Admin) (n : Nat) (cs : List Catch)
    (b : List Admin) : codeSize b < codeSize (vals V ++ [.handler n cs b] ++ L) := by
  have h1 := codeSize_append (vals V ++ [.handler n cs b]) L
  have h2 := codeSize_append (vals V) [.handler n cs b]
  have h3 := codeSize_cons (.handler n cs b) []
  have h4 := Admin.handler.sizeOf_spec n cs b
  have h5 := codeSize_pos (vals V)
  have h6 := codeSize_pos L
  have h7 := codeSize_pos []
  unfold codeSize at *
  omega

theorem codeSize_handler_lt (V : List Val) (L : List Admin) (n : Nat) (cs : List Catch)
    {b b₁ : List Admin} (h : codeSize b₁ < codeSize b) :
    codeSize (vals V ++ [.handler n cs b₁] ++ L) < codeSize (vals V ++ [.handler n cs b] ++ L) := by
  have h1 := codeSize_append (vals V ++ [.handler n cs b]) L
  have h2 := codeSize_append (vals V) [.handler n cs b]
  have h3 := codeSize_cons (.handler n cs b) []
  have h4 := Admin.handler.sizeOf_spec n cs b
  have h1' := codeSize_append (vals V ++ [.handler n cs b₁]) L
  have h2' := codeSize_append (vals V) [.handler n cs b₁]
  have h3' := codeSize_cons (.handler n cs b₁) []
  have h4' := Admin.handler.sizeOf_spec n cs b₁
  unfold codeSize at *
  omega

theorem steps_handler {c c' : Config H} (h : Steps P host c c') (n : Nat) (cs : List Catch) :
    Steps P host ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨c'.store, c'.frame, [.handler n cs c'.code]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    have lift : ∀ {a b : Config H}, Step P host a b →
        Step P host ⟨a.store, a.frame, [.handler n cs a.code]⟩
          ⟨b.store, b.frame, [.handler n cs b.code]⟩ := by
      intro a b hab
      obtain ⟨_, _, _⟩ := a
      obtain ⟨_, _, _⟩ := b
      exact Step.ctxtHandler hab
    exact ih.tail (lift hab)

/-- A run of a handler body, in a value prefix and before a suffix. -/
theorem wrap_steps {t t' : Store H} {f f' : Frame} {x y : List Admin} (V : List Val)
    (L : List Admin) (n : Nat) (cs : List Catch) (h : Steps P host ⟨t, f, x⟩ ⟨t', f', y⟩) :
    Steps P host ⟨t, f, vals V ++ [.handler n cs x] ++ L⟩
      ⟨t', f', vals V ++ [.handler n cs y] ++ L⟩ := by
  have h3 := Steps.append_right (Steps.vals_left (steps_handler h n cs) V) L
  dsimp only at h3
  exact h3

/-- A step of a handler redex, in a value prefix and before a suffix. -/
theorem wrap_step {t t' : Store H} {f f' : Frame} {x y : List Admin} (V : List Val)
    (L : List Admin) (n : Nat) (cs : List Catch)
    (h : Step P host ⟨t, f, [.handler n cs x]⟩ ⟨t', f', y⟩) :
    Step P host ⟨t, f, vals V ++ [.handler n cs x] ++ L⟩ ⟨t', f', vals V ++ y ++ L⟩ :=
  Step.append_right (Step.vals_left h V) L

/-- A `trap` or thrown-exception kernel discards the values and code around it. -/
theorem steps_kernel {t : Store H} {f : Frame} {k : List Admin}
    (hk : k = [.trap] ∨ ∃ a, k = throwing a) (ws : List Val) (j : List Admin) :
    Steps P host ⟨t, f, vals ws ++ k ++ j⟩ ⟨t, f, k⟩ := by
  by_cases hne : ws ≠ [] ∨ j ≠ []
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact .single (Step.trapInstrs hne)
    · exact .single (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals_nil'] using (Relation.ReflTransGen.refl : Steps P host ⟨t, f, k⟩ ⟨t, f, k⟩)

/-- A step at a `HANDLER` head. -/
theorem handler_case_of_body (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseFacts P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cs : List Catch} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P host ⟨s, f, b⟩ c' →
      RankedMatched rank P host F BI B c' ⟨t, f, b'⟩ (rank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩
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
    obtain ⟨t₁, hrun, hst₁⟩ := AdminsRel.values_lift hB (f := f) (vs := []) (us := vs) hst hb rfl
    refine ⟨⟨t₁, f, vals W ++ vals vs ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      (steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil']))) (wrap_step W L' n cs
        .handlerVals)), hst₁, rfl, ((AdminsRel.vals W).append (AdminsRel.vals vs)).append hL⟩
  · -- `br`/`return`/`return_call_ref` through the handler
    subst s' f'
    have hex : Exit k := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact .br l
      · exact .return_
      · exact .returnCallRef hc
    obtain ⟨t₁, ws', j', hrun, hst₁, hws⟩ := AdminsRel.exit_lift hB (f := f) (vs := []) (us := vs)
      (j := rest) hst hb hex (by simp [vals_nil'])
    have hws' : ws' = vs := by
      rcases hws with h' | h' | ⟨a, h'⟩
      · exact h'
      all_goals exfalso; rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩ <;>
        simp_all [throwing, Admin.IsReturnCallRef]
    rw [hws'] at hrun
    have hbub : Step P host ⟨t₁, f, [.handler n cs (vals vs ++ k ++ j')]⟩
        ⟨t₁, f, vals vs ++ k⟩ := by
      rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
      · exact .brHandler
      · exact .returnHandler
      · exact .returnCallRefHandler hc
    refine ⟨⟨t₁, f, vals W ++ (vals vs ++ k) ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      (steps_congr hrun (by simp [vals_nil']) rfl)) (wrap_step W L' n cs hbub)), hst₁, rfl,
      (AdminsRel.refl _).append hL⟩
  · -- `trap-handler` and the `throw_ref-handler-*` rules: same catch clauses, related stores
    have hex : Exit b := by rcases hk with rfl | ⟨a, rfl⟩; exacts [.trap, .throw a]
    obtain ⟨t₁, ws', j', hrun, hst₁, -⟩ := AdminsRel.exit_lift hB (f := f) (vs := []) (us := [])
      (k := b) (j := []) hst hb hex (by simp [vals_nil'])
    obtain ⟨t', es'', hst', hst₂, hres⟩ :=
      Step.match_storeRel (B := WithCuts B) hF hhost hk0 t₁ hst₁
    dsimp only at hst' hst₂ hres
    refine ⟨⟨t', f', vals W ++ es'' ++ L'⟩, Or.inl (.tail' (wrap_steps W L' n cs
      ((steps_congr hrun (by simp [vals_nil']) rfl).trans
        (steps_kernel hk ws' j'))) (wrap_step W L' n cs hst')), hst₂, rfl,
      ((AdminsRel.vals W).append hres).append hL⟩


/-- Compatibility form using the unrestricted rank induction hypothesis. -/
theorem handler_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {s t s' : Store H}
    {f f' : Frame} {V : List Val} {n : Nat} {cs : List Catch} {b b' L L' es' : List Admin}
    (ih : RankedStepIH rank P host F BI B (rank (vals V ++ [.handler n cs b] ++ L)))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩
      (rank (vals V ++ [.handler n cs b] ++ L)) := by
  apply handler_case_of_body hF hhost hB.toBaseFacts ?_ hst hb hL h
  intro c' hs
  exact ih (c := ⟨s, f, b⟩) (d := ⟨t, f, b'⟩) (LawfulCodeRank.handler_body_lt (vals V) L n cs b) ⟨hst, rfl, hb⟩ hs

end Closure

end Silmaril.Wasm.Execution.Core.Sim
