module

public import Silmaril.Wasm.Binaryen.InlUnwrapOperandBoundary
public import Silmaril.Wasm.Binaryen.InlUnwrapRecursiveTrap

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type}

/-- A typed throw_ref has its exception-reference operand inside the fragment. -/
theorem _root_.Silmaril.Wasm.Execution.Core.Sim.ContextTyped.throwRef_arity {s : Store H} {f : Frame} {vs : List Val}
    {rest : List Admin}
    (typed : ContextTyped ⟨s, f, vals vs ++ .plain .throwRef :: rest⟩) :
    1 ≤ vs.length := by
  apply typed.fragment.active_arity
  intro C it ha
  cases ha with
  | plain hi =>
    cases hi with
    | throwRef _ => simp
    | _ => rename_i impossible; cases impossible
  | throwRefInits _ => simp

private theorem split_active {x y : List Admin} {us : List Val} {e : Admin} {j : List Admin}
    (shape : x ++ y = vals us ++ e :: j) :
    (∃ u w : List Val, x = vals u ∧ y = vals w ++ e :: j ∧ us = u ++ w) ∨
      (∃ rest : List Admin, x = vals us ++ e :: rest ∧ j = rest ++ y) := by
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

/-- The actual exception operand cannot come from outside an original running
wrapper, even though the recursively transformed body is not assumed typed. -/
theorem UL.typed_throwRef_bound :
    ∀ {x y : List Admin}, UL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner : List Val} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ .plain .throwRef :: rest →
      1 ≤ (vs ++ inner).length
  | _, _, .nil, _, _, _, inner, _, _, shape => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, Admin.val?] at all
  | _, _, (@UL.cons _ a b os ns related tail), s, f, vs, inner, rest, typed, shape => by
    cases inner with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      cases related with
      | plain relation =>
        cases relation
        simpa using typed.throwRef_arity
    | cons v inner =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := UA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [List.append_assoc, List.singleton_append] using
        UL.typed_throwRef_bound tail typed' tailShape
  | _, _, (@UL.site _ bt os ns tail), s, f, vs, inner, rest, typed, shape => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := .spec true) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using UL.typed_throwRef_bound tail typedTail tailShape
    · obtain ⟨blockPre, blockArgs, ps, rs, stack, _, _, entry, _⟩ :=
        ContextTyped.block_entry (P := .spec true) (rest := os) (by simpa using typed)
      have typedBody : ContextTyped
          ⟨s, f, vals (blockArgs ++ inner) ++ .plain .throwRef :: insideRest⟩ := by
        have after : ContextTyped
            ⟨s, f, vals blockPre ++ [.label rs.length [] (vals blockArgs ++ expression R)] ++ os⟩ :=
          typed.step (by simpa only [List.append_assoc, List.singleton_append] using entry)
        have body : ContextTyped ⟨s, f, vals blockArgs ++ expression R⟩ := ContextTyped.label after
        simpa only [bodyActive, vals_append, List.append_assoc] using body
      have bound := typedBody.throwRef_arity
      have lengths := congrArg List.length stack
      simp only [List.length_append] at bound lengths ⊢
      omega
  | _, _, (@UL.run _ n X X' os ns body safe tail), s, f, vs, inner, rest, typed, shape => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have inside := UL.typed_values_reverse (P := .spec true) body (vs := []) typedBody bodyValues
      have inside' : Steps (.spec true) noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using UL.typed_throwRef_bound tail typedTail tailShape
    · have bound := UL.typed_throwRef_bound body (vs := [])
        (by simpa using typedBody) bodyActive
      simp only [List.nil_append, List.length_append] at bound ⊢
      omega
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldLabel _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, (@UL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, rest, typed, shape => by
    rcases kernel with rfl | ⟨a, rfl⟩
    · have first := congrArg fnv shape
      simp [fnv, Admin.val?] at first
    · have shape' : vals [.ref (.exn a)] ++ .plain .throwRef :: ns =
          vals inner ++ .plain .throwRef :: rest := by
        simpa [throwing, vals, Val.toAdmin] using shape
      obtain ⟨operandsShape, _, _⟩ := Sim.vals_append_cons_inj val?_throwRef val?_throwRef shape'
      subst inner
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private theorem last_operand {front values out : List Val} {operand : Val}
    (shape : front ++ values = out ++ [operand]) (bound : 1 ≤ values.length) :
    ∃ prefixValues, values = prefixValues ++ [operand] := by
  cases values using List.reverseRecOn with
  | nil => simp at bound
  | append_singleton initial last =>
    have lastEq := congrArg List.getLast? shape
    simp at lastEq
    subst last
    exact ⟨initial, rfl⟩

variable {P : Profile}

/-- Normalize an actual exception kernel through the full recursive relation.
The throw operand is proven to lie inside each original runtime boundary. -/
theorem UL.typed_throw_reverse :
    ∀ {x y : List Admin}, UL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner us : List Val} {a : Nat} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ .plain .throwRef :: rest →
      vs ++ inner = us ++ [.ref (.exn a)] →
      Steps P noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, throwing a⟩
  | _, _, .nil, _, _, _, inner, _, _, _, _, shape, _ => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, Admin.val?] at all
  | _, _, (@UL.cons _ a b os ns related tail), s, f, vs, inner, us, exn, rest,
      typed, shape, operands => by
    cases inner with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      cases related with
      | plain relation =>
        cases relation
        have stack : vs = us ++ [.ref (.exn exn)] := by simpa using operands
        simpa [stack, vals_append, throwing, Val.toAdmin] using
          Closure.steps_kernel (P := P) (host := noHost) (t := s) (f := f)
            (Or.inr ⟨exn, rfl⟩) us os
    | cons v inner =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := UA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using
        UL.typed_throw_reverse tail typed' tailShape
          (by simpa only [List.append_assoc, List.singleton_append] using operands)
  | _, _, (@UL.site _ bt os ns tail), s, f, vs, inner, us, exn, rest,
      typed, shape, operands => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := UL.typed_throw_reverse tail typedTail tailShape
        (by simpa only [List.append_assoc] using operands)
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · obtain ⟨blockPre, blockArgs, ps, rs, stack, resolved, arity, entry, _⟩ :=
        ContextTyped.block_entry (P := P) (rest := os) (by simpa using typed)
      have typedBody : ContextTyped
          ⟨s, f, vals (blockArgs ++ inner) ++ .plain .throwRef :: insideRest⟩ := by
        have after : ContextTyped
            ⟨s, f, vals blockPre ++ [.label rs.length [] (vals blockArgs ++ expression R)] ++ os⟩ :=
          typed.step (by simpa only [List.append_assoc, List.singleton_append] using entry)
        have body : ContextTyped ⟨s, f, vals blockArgs ++ expression R⟩ := ContextTyped.label after
        simpa only [bodyActive, vals_append, List.append_assoc] using body
      obtain ⟨innerPre, innerOperands⟩ := last_operand
        (front := blockPre) (values := blockArgs ++ inner)
        (out := us) (operand := .ref (.exn exn))
        (by simpa only [stack, List.append_assoc] using operands) typedBody.throwRef_arity
      have kernelShape : vals blockArgs ++ expression R =
          vals innerPre ++ throwing exn ++ insideRest := by
        rw [bodyActive]
        calc
          vals blockArgs ++ (vals inner ++ .plain .throwRef :: insideRest) =
              vals (blockArgs ++ inner) ++ .plain .throwRef :: insideRest := by simp
          _ = _ := by rw [innerOperands]; simp [throwing, vals_append, Val.toAdmin]
      simpa only [stack, List.append_assoc, List.singleton_append] using
        block_kernel_run (P := P) (host := noHost) (s := s) (f := f)
          (pre := blockPre) (args := blockArgs) (inner := innerPre)
          (rest := insideRest) (suffix := os) resolved arity (Or.inr ⟨exn, rfl⟩) kernelShape
  | _, _, (@UL.run _ n X X' os ns body safe tail), s, f, vs, inner, us, exn, rest,
      typed, shape, operands => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have inside := UL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := UL.typed_throw_reverse tail typedTail tailShape
        (by simpa only [List.append_assoc] using operands)
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have bound := UL.typed_throwRef_bound body (vs := [])
        (by simpa using typedBody) bodyActive
      obtain ⟨innerPre, innerOperands⟩ := last_operand operands (by simpa using bound)
      have inside := UL.typed_throw_reverse body (vs := [])
        (by simpa using typedBody) bodyActive (by simpa using innerOperands)
      have inside' : Steps P noHost ⟨s, f, X⟩ ⟨s, f, throwing exn⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have first := Steps.append_right (Steps.vals_left (Closure.steps_label inside' n []) vs) os
      refine (Closure.steps_congr first (by simp) rfl).trans ?_
      simpa only [Execution.Core.vals_nil', List.nil_append, List.append_nil] using
        label_kernel_run (P := P) (host := noHost) (s := s) (f := f)
          (n := n) (cont := []) (pre := vs) (inner := [])
          (rest := []) (suffix := os) (Or.inr ⟨exn, rfl⟩)
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, _, _, _, shape, _ => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, _, _, _, shape, _ => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldLabel _ _ _ _, _, _, _, _, _, _, _, _, shape, _ => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, (@UL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, us, exn, rest,
      typed, shape, operands => by
    rcases kernel with rfl | ⟨other, rfl⟩
    · have first := congrArg fnv shape
      simp [fnv, Admin.val?] at first
    · have shape' : vals [.ref (.exn other)] ++ .plain .throwRef :: ns =
          vals inner ++ .plain .throwRef :: rest := by
        simpa [throwing, vals, Val.toAdmin] using shape
      obtain ⟨operandsShape, _, _⟩ := Sim.vals_append_cons_inj val?_throwRef val?_throwRef shape'
      subst inner
      have last := congrArg List.getLast? operands
      simp at last
      subst other
      simpa only [List.append_assoc, List.singleton_append] using
        label_kernel_run (P := P) (host := noHost) (s := s) (f := f)
          (n := n) (cont := []) (pre := vs) (inner := ws)
          (rest := J) (suffix := os) (Or.inr ⟨exn, rfl⟩)

/-- Exception normalization in the primitive typed-facts input shape, where
the exception reference may initially appear in the explicit ambient prefix. -/
theorem UL.typed_throw_exit_reverse {x y : List Admin} (related : UL R x y)
    {s : Store H} {f : Frame} {vs us : List Val} {a : Nat} {rest : List Admin}
    (typed : ContextTyped ⟨s, f, vals vs ++ x⟩)
    (shape : vals vs ++ y = vals us ++ throwing a ++ rest) :
    Steps P noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, throwing a⟩ := by
  have active : y.all Admin.isVal = false := by
    have all := congrArg (List.all · Admin.isVal) shape
    simpa [throwing, Admin.isVal, Admin.val?] using all
  obtain ⟨inner, e, tail, he, bodyShape⟩ := exists_head_of_not_all active
  have headShape : vals (vs ++ inner) ++ e :: tail =
      vals (us ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
    simpa [bodyShape, throwing, vals_append, Val.toAdmin] using shape
  obtain ⟨operands, hhead, htail⟩ := Sim.vals_append_cons_inj he val?_throwRef headShape
  subst e tail
  exact UL.typed_throw_reverse related typed bodyShape operands

/-- The complete kernel observation is exact through every recursive unwrap
phase, while arbitrary value prefixes and continuations may be discarded. -/
theorem UL.typed_kernel_exit_reverse {x y : List Admin} (related : UL R x y)
    {s : Store H} {f : Frame} {vs us : List Val} {k rest : List Admin}
    (typed : ContextTyped ⟨s, f, vals vs ++ x⟩)
    (kernel : k = [.trap] ∨ ∃ a, k = throwing a)
    (shape : vals vs ++ y = vals us ++ k ++ rest) :
    Steps P noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, k⟩ := by
  rcases kernel with rfl | ⟨a, rfl⟩
  · have active : y.all Admin.isVal = false := by
      have all := congrArg (List.all · Admin.isVal) shape
      simpa [Admin.isVal, Admin.val?] using all
    obtain ⟨inner, e, tail, he, bodyShape⟩ := exists_head_of_not_all active
    have headShape : vals (vs ++ inner) ++ e :: tail = vals us ++ Admin.trap :: rest := by
      simpa only [bodyShape, vals_append, List.append_assoc, List.singleton_append] using shape
    obtain ⟨_, hhead, htail⟩ := Sim.vals_append_cons_inj he val?_trap headShape
    subst e tail
    exact UL.typed_trap_reverse related typed bodyShape
  · exact UL.typed_throw_exit_reverse related typed shape

end Silmaril.Wasm.Binaryen.Unwrap
