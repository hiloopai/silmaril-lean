module

public import Silmaril.Wasm.Binaryen.InlReverseCallerControl

@[expose] public section

/-! # Chosen caller bubbles with decreasing administrative stutters

Caller trap and exception relations deliberately forget unreachable suffixes.
A selected target bubble therefore either discards actual original code, or
strictly decreases the target code while the original has already finished
that discard. No positive original step is claimed in the latter case.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem LG.trap_prefix_right {E : List (Option Val)} {original rest : List Admin}
    {vs : List Val} (related : LG p E original (vals vs ++ .trap :: rest)) :
    ∃ oldRest, original = vals vs ++ .trap :: oldRest := by
  rcases LG.vals_cons_inv_right rfl related with ordinary | pending | trapped | thrown
  · obtain ⟨oldHead, oldRest, shape, head, _⟩ := ordinary
    cases head
    exact ⟨oldRest, shape⟩
  · obtain ⟨impossible, _⟩ := pending
    cases impossible
  · exact trapped.2
  · obtain ⟨impossible, _⟩ := thrown
    cases impossible

theorem LG.throw_prefix_right {E : List (Option Val)} {original rest : List Admin}
    {vs : List Val} (related : LG p E original (vals vs ++ .plain .throwRef :: rest)) :
    ∃ oldRest, original = vals vs ++ .plain .throwRef :: oldRest := by
  rcases LG.vals_cons_inv_right rfl related with ordinary | pending | trapped | thrown
  · obtain ⟨oldHead, oldRest, shape, head, _⟩ := ordinary
    obtain ⟨instruction, rfl, translated⟩ := AG.plain_inv_right head
    have same := IR.eq_of_nonstruct_right translated (by simp [StructE])
    exact ⟨oldRest, by rw [same] at shape; exact shape⟩
  · obtain ⟨impossible, _⟩ := pending
    cases impossible
  · obtain ⟨impossible, _⟩ := trapped
    cases impossible
  · exact thrown.2

theorem LG.bubble_prefix_right {E : List (Option Val)} {original kernel rest : List Admin}
    {vs : List Val} (bubble : Det.IsBubble kernel)
    (related : LG p E original (vals vs ++ kernel ++ rest)) :
    ∃ oldRest, original = vals vs ++ kernel ++ oldRest := by
  rcases bubble with rfl | ⟨address, rfl⟩
  · simpa using LG.trap_prefix_right (by simpa using related)
  · have shape : vals vs ++ [Admin.ref (.exn address), .plain .throwRef] ++ rest =
        vals (vs ++ [.ref (.exn address)]) ++ .plain .throwRef :: rest := by simp [vals, Val.toAdmin]
    rw [shape] at related
    obtain ⟨oldRest, originalShape⟩ := LG.throw_prefix_right related
    exact ⟨oldRest, by simpa [vals, Val.toAdmin] using originalShape⟩

theorem LG.bubble_dead_suffix {E : List (Option Val)} {kernel oldRest newRest : List Admin}
    (bubble : Det.IsBubble kernel) : LG p E (kernel ++ oldRest) (kernel ++ newRest) := by
  rcases bubble with rfl | ⟨address, rfl⟩
  · exact .trapT
  · exact .val rfl .throwT

/-- A chosen target bubble makes actual original progress whenever the
original still has anything to discard. Otherwise its actual code rank drops. -/
theorem reverse_caller_bubble {s t : Store H} {fo : Frame} {E : List (Option Val)}
    {pp q : List Val} {kernel discarded rest original : List Admin}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (bubble : Det.IsBubble kernel) (nonempty : q ≠ [] ∨ discarded ≠ [])
    (related : LG p E original (vals (pp ++ q) ++ kernel ++ (discarded ++ rest))) :
    ReverseProgress p P .g ⟨s, fo, original⟩
      ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals (pp ++ q) ++ kernel ++ (discarded ++ rest)⟩
      ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals pp ++ kernel ++ rest⟩ := by
  obtain ⟨oldRest, rfl⟩ := LG.bubble_prefix_right bubble related
  have runtime : MR p .g ⟨s, fo, vals pp ++ kernel⟩
      ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals pp ++ kernel ++ rest⟩ :=
    ⟨moduleEq, locals, E, extra, rfl, by
      simpa using LG.vals_append pp (LG.bubble_dead_suffix (oldRest := []) bubble)⟩
  by_cases progress : q ≠ [] ∨ oldRest ≠ []
  · exact .inl (ReverseMatch.of_steps
      (.single (Det.Bubble.toStep ⟨pp, q, kernel, oldRest, [], by simp,
        bubble, progress, by simp⟩)) runtime stores)
  · have emptyQ : q = [] := by tauto
    have emptyRest : oldRest = [] := by tauto
    subst q oldRest
    refine .inr ⟨_, .done _, by simpa using runtime, stores, ?_⟩
    have discardedNonempty : discarded ≠ [] := nonempty.resolve_left (by simp)
    have positive := aszs_pos discardedNonempty
    simp only [List.append_nil, aszs_append, aszs_vals]
    omega

end Silmaril.Wasm.Binaryen.InlR
