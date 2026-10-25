module

public import Silmaril.Wasm.Binaryen.InlUnwrapRecursiveValues

@[expose] public section

/-! # Recursive typed trap normalization for unwrap

A bare side whose first non-value is a trap normalizes its original side to
exactly that observable trap. Recursive block and running-label phases may
discard different value prefixes; their terminal trap and store/frame agree.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {R : List Instr} {H : Type} {P : Profile}

private theorem split_trap {x y : List Admin} {us : List Val} {j : List Admin}
    (shape : x ++ y = vals us ++ Admin.trap :: j) :
    (∃ u w : List Val, x = vals u ∧ y = vals w ++ Admin.trap :: j ∧ us = u ++ w) ∨
      (∃ rest : List Admin, x = vals us ++ Admin.trap :: rest ∧ j = rest ++ y) := by
  induction us generalizing x with
  | nil =>
    cases x with
    | nil => exact Or.inl ⟨[], [], rfl, shape, rfl⟩
    | cons a x =>
      obtain ⟨rfl, result⟩ := List.cons.inj shape
      exact Or.inr ⟨x, rfl, result.symm⟩
  | cons v us ih =>
    cases x with
    | nil => exact Or.inl ⟨[], v :: us, rfl, shape, rfl⟩
    | cons a x =>
      obtain ⟨rfl, result⟩ := List.cons.inj shape
      rcases ih result with ⟨u, w, rfl, tail, rfl⟩ | ⟨rest, rfl, tail⟩
      · exact Or.inl ⟨v :: u, w, rfl, tail, rfl⟩
      · exact Or.inr ⟨rest, rfl, tail⟩

/-- Normalize the complete recursive unwrap relation at a trap boundary. This
includes running wrappers and folding phases, uses only original ambient
typing, and preserves the exact original store and frame. -/
theorem UL.typed_trap_reverse :
    ∀ {x y : List Admin}, UL R x y →
    ∀ {s : Store H} {f : Frame} {vs us : List Val} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals us ++ Admin.trap :: rest →
      Steps P Det.noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, [.trap]⟩
  | _, _, .nil, _, _, _, us, rest, _, shape => by
    have mem : Admin.trap ∈ vals us ++ Admin.trap :: rest := by simp
    rw [← shape] at mem
    cases mem
  | _, _, (@UL.cons _ a b os ns head tail), s, f, vs, us, rest, typed, shape => by
    cases us with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      cases head
      simpa only [List.append_assoc, List.singleton_append] using
        Closure.steps_kernel (P := P) (host := Det.noHost) (t := s) (f := f)
          (Or.inl rfl) vs os
    | cons v us =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := UA.eq_of_val_right head
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using UL.typed_trap_reverse tail typed' tailShape
  | _, _, (@UL.site _ bt os ns tail), s, f, vs, us, rest, typed, shape => by
    rcases split_trap shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyTrap, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := UL.typed_trap_reverse tail typedTail tailShape
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have mem : Admin.trap ∈ expression R := by rw [bodyTrap]; simp
      simp [expression] at mem
  | _, _, (@UL.run _ n X X' os ns body safe tail), s, f, vs, us, rest, typed, shape => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_trap shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyTrap, _⟩
    · have inside := UL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P Det.noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := UL.typed_trap_reverse tail typedTail tailShape
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have inside := UL.typed_trap_reverse body (vs := []) typedBody bodyTrap
      have inside' : Steps P Det.noHost ⟨s, f, X⟩ ⟨s, f, [.trap]⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have first := Steps.append_right (Steps.vals_left (Closure.steps_label inside' n []) vs) os
      refine (Closure.steps_congr first (by simp) rfl).trans ?_
      simpa only [Execution.Core.vals_nil', List.nil_append, List.append_nil] using
        label_kernel_run (P := P) (host := Det.noHost) (s := s) (f := f)
          (n := n) (cont := []) (pre := vs) (inner := [])
          (rest := []) (suffix := os) (Or.inl rfl)
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg Det.fnv shape
    simp [Det.fnv, Admin.val?] at first
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg Det.fnv shape
    simp [Det.fnv, Admin.val?] at first
  | _, _, .foldLabel _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg Det.fnv shape
    simp [Det.fnv, Admin.val?] at first
  | _, _, (@UL.foldExit _ n ws K J os ns kernel tail), s, f, vs, us, rest, typed, shape => by
    rcases kernel with rfl | ⟨a, rfl⟩
    · simpa only [List.append_assoc, List.singleton_append] using
        label_kernel_run (P := P) (host := Det.noHost) (s := s) (f := f)
          (n := n) (cont := []) (pre := vs) (inner := ws)
          (rest := J) (suffix := os) (Or.inl rfl)
    · have first := congrArg Det.fnv shape
      simp [Det.fnv, Admin.val?] at first

end Silmaril.Wasm.Binaryen.Unwrap
