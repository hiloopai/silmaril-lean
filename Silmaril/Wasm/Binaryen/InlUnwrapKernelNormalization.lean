module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelRel

@[expose] public section

/-! # Typed normalization of recursive kernel-expanded unwrap phases

Kernel cuts can occur below any runtime context or inserted wrapper. The
original side supplies all typing; branch/return prefixes remain exact, and
trap/exception observations retain their original store and frame.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}

/-- Escape freedom is preserved by every actual finite normalization trace. -/
theorem NoEsc.steps {host : HostSemantics H} {c d : Config H}
    (safe : NoEsc c.code) (run : Steps P host c d) : NoEsc d.code := by
  induction run with
  | refl => exact safe
  | tail _ step ih => exact ih.step step

/-- The first active head of a kernel cut identifies its exact kernel operand. -/
theorem kernel_cut_head {x y : List Admin} (discard : ExitCut y x)
    {inner : List Val} {e : Admin} {rest : List Admin}
    (shape : y = vals inner ++ e :: rest) (he : e.val? = none) :
    ∃ ws k j, x = vals ws ++ k ++ j ∧
      ((k = [.trap] ∧ e = .trap) ∨
        ∃ a, k = throwing a ∧ e = .plain .throwRef ∧
          ∃ u, inner = u ++ [.ref (.exn a)]) := by
  obtain ⟨us, ws, k, ys, xs, kernel, rfl, rfl⟩ := discard
  refine ⟨ws, k, xs, rfl, ?_⟩
  rcases kernel with rfl | ⟨a, rfl⟩
  · obtain ⟨_, head, _⟩ := Sim.vals_append_cons_inj val?_trap he
      (by simpa only [List.append_assoc, List.singleton_append] using shape)
    exact Or.inl ⟨rfl, head.symm⟩
  · have activeShape : vals (us ++ [.ref (.exn a)]) ++ .plain .throwRef :: ys =
        vals inner ++ e :: rest := by
      simpa [throwing, vals_append, Val.toAdmin] using shape
    obtain ⟨operands, head, _⟩ := Sim.vals_append_cons_inj val?_throwRef he activeShape
    exact Or.inr ⟨a, rfl, head.symm, us, operands.symm⟩

/-- Structural unwrap pairs preserve whether an administrative head is a value. -/
theorem KUA.val?_eq {a b : Admin} (related : KUA R a b) : a.val? = b.val? := by
  cases related with
  | plain related => cases related <;> rfl
  | _ => rfl

/-- A value on the bare side has exactly the same original value head. -/
theorem KUA.eq_of_val_right {a : Admin} {v : Val} (related : KUA R a v.toAdmin) :
    a = v.toAdmin := by
  apply Admin.eq_of_val?
  rw [KUA.val?_eq related, Admin.val?_toAdmin]

private theorem split_values {x y : List Admin} {us : List Val}
    (shape : x ++ y = vals us) :
    ∃ u v : List Val, x = vals u ∧ y = vals v ∧ us = u ++ v := by
  have all : (x ++ y).all Admin.isVal = true := by rw [shape]; simp
  rw [List.all_append, Bool.and_eq_true] at all
  obtain ⟨u, rfl⟩ := exists_vals_of_all all.1
  obtain ⟨v, rfl⟩ := exists_vals_of_all all.2
  exact ⟨u, v, rfl, rfl, Execution.Core.Sim.vals_injective (by simpa using shape.symm)⟩

/-- Normalize every target-only block/running-label phase when the transformed
side is already values. This recursion decreases relation depth rather than
claiming that stripping a target wrapper decreases the source code rank. -/
theorem KUL.typed_values_reverse :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {s : Store H} {f : Frame} {vs us : List Val},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals us →
      Steps P Det.noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, vals vs ++ vals us⟩
  | _, _, .nil, _, _, _, _, _, values => by rw [← values]
  | _, _, (@KUL.cons _ a b os ns head tail), s, f, vs, us, typed, values => by
    cases us with
    | nil => cases values
    | cons v us =>
      simp only [vals_cons'] at values
      obtain ⟨rfl, rfl⟩ := List.cons.inj values
      obtain rfl := KUA.eq_of_val_right head
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using KUL.typed_values_reverse tail typed' rfl
  | _, _, (@KUL.site _ bt os ns tail), s, f, vs, us, typed, values => by
    obtain ⟨u, v, bodyValues, tailValues, rfl⟩ := split_values values
    have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
      apply ContextTyped.suffix
      simpa only [List.append_assoc, List.singleton_append] using typed
    have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
    have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
      have after := typed.steps (Closure.steps_congr first (by simp) rfl)
      simpa only [vals_append, List.append_assoc] using after
    have last := KUL.typed_values_reverse tail typedTail tailValues
    refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_
    · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · simpa only [vals_append, List.append_assoc] using last
  | _, _, (@KUL.run _ n X X' os ns body safe tail), s, f, vs, us, typed, values => by
    obtain ⟨u, v, bodyValues, tailValues, rfl⟩ := split_values values
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    have inside := KUL.typed_values_reverse body (vs := []) typedBody bodyValues
    have inside' : Steps P Det.noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
      simpa only [Execution.Core.vals_nil', List.nil_append] using inside
    have complete := (Closure.steps_label inside' n []).tail Step.labelVals
    have first := Steps.append_right (Steps.vals_left complete vs) os
    have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
      have after := typed.steps (Closure.steps_congr first (by simp) rfl)
      simpa only [vals_append, List.append_assoc] using after
    have last := KUL.typed_values_reverse tail typedTail tailValues
    refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_
    · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · simpa only [vals_append, List.append_assoc] using last
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldLabel _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldExit kernel _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    rcases kernel with rfl | ⟨a, rfl⟩
    · simp [Admin.isVal, Admin.val?] at all
    · simp [Admin.isVal, Admin.val?] at all

  | _, _, .cut discard, _, _, _, _, _, values => by
    have active := Closure.exitCut_not_all discard
    rw [values] at active
    simp at active

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
theorem KUL.typed_trap_reverse :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {s : Store H} {f : Frame} {vs us : List Val} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals us ++ Admin.trap :: rest →
      Steps P Det.noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, [.trap]⟩
  | _, _, .nil, _, _, _, us, rest, _, shape => by
    have mem : Admin.trap ∈ vals us ++ Admin.trap :: rest := by simp
    rw [← shape] at mem
    cases mem
  | _, _, (@KUL.cons _ a b os ns head tail), s, f, vs, us, rest, typed, shape => by
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
      obtain rfl := KUA.eq_of_val_right head
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using KUL.typed_trap_reverse tail typed' tailShape
  | _, _, (@KUL.site _ bt os ns tail), s, f, vs, us, rest, typed, shape => by
    rcases split_trap shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyTrap, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := KUL.typed_trap_reverse tail typedTail tailShape
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have mem : Admin.trap ∈ expression R := by rw [bodyTrap]; simp
      simp [expression] at mem
  | _, _, (@KUL.run _ n X X' os ns body safe tail), s, f, vs, us, rest, typed, shape => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_trap shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyTrap, _⟩
    · have inside := KUL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P Det.noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := KUL.typed_trap_reverse tail typedTail tailShape
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have inside := KUL.typed_trap_reverse body (vs := []) typedBody bodyTrap
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
  | _, _, .foldLabel _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg Det.fnv shape
    simp [Det.fnv, Admin.val?] at first
  | _, _, (@KUL.foldExit _ n ws K J os ns kernel tail), s, f, vs, us, rest, typed, shape => by
    rcases kernel with rfl | ⟨a, rfl⟩
    · simpa only [List.append_assoc, List.singleton_append] using
        label_kernel_run (P := P) (host := Det.noHost) (s := s) (f := f)
          (n := n) (cont := []) (pre := vs) (inner := ws)
          (rest := J) (suffix := os) (Or.inl rfl)
    · have first := congrArg Det.fnv shape
      simp [Det.fnv, Admin.val?] at first

  | _, _, .cut discard, s, f, vs, us, rest, _, shape => by
    obtain ⟨ws, k, j, originalShape, kernel⟩ := kernel_cut_head discard shape rfl
    rcases kernel with ⟨rfl, _⟩ | ⟨a, _, impossible, _⟩
    · simpa only [originalShape, vals_append, List.append_assoc] using
        Closure.steps_kernel (P := P) (host := Det.noHost) (t := s) (f := f)
          (Or.inl rfl) (vs ++ ws) j
    · cases impossible

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
theorem KUL.typed_throwRef_bound :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner : List Val} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ .plain .throwRef :: rest →
      1 ≤ (vs ++ inner).length
  | _, _, .nil, _, _, _, inner, _, _, shape => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, Admin.val?] at all
  | _, _, (@KUL.cons _ a b os ns related tail), s, f, vs, inner, rest, typed, shape => by
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
      obtain rfl := KUA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [List.append_assoc, List.singleton_append] using
        KUL.typed_throwRef_bound tail typed' tailShape
  | _, _, (@KUL.site _ bt os ns tail), s, f, vs, inner, rest, typed, shape => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := .spec true) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using KUL.typed_throwRef_bound tail typedTail tailShape
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
  | _, _, (@KUL.run _ n X X' os ns body safe tail), s, f, vs, inner, rest, typed, shape => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have inside := KUL.typed_values_reverse (P := .spec true) body (vs := []) typedBody bodyValues
      have inside' : Steps (.spec true) noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using KUL.typed_throwRef_bound tail typedTail tailShape
    · have bound := KUL.typed_throwRef_bound body (vs := [])
        (by simpa using typedBody) bodyActive
      simp only [List.nil_append, List.length_append] at bound ⊢
      omega
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, .foldLabel _ _ _, _, _, _, _, _, _, shape => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, (@KUL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, rest, typed, shape => by
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

  | _, _, .cut discard, s, f, vs, inner, rest, _, shape => by
    obtain ⟨_, _, _, _, kernel⟩ := kernel_cut_head discard shape rfl
    rcases kernel with ⟨_, impossible⟩ | ⟨a, _, _, u, rfl⟩
    · cases impossible
    · simp only [List.length_append, List.length_singleton]
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


/-- Normalize an actual exception kernel through the full recursive relation.
The throw operand is proven to lie inside each original runtime boundary. -/
theorem KUL.typed_throw_reverse :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner us : List Val} {a : Nat} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ .plain .throwRef :: rest →
      vs ++ inner = us ++ [.ref (.exn a)] →
      Steps P noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, throwing a⟩
  | _, _, .nil, _, _, _, inner, _, _, _, _, shape, _ => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, Admin.val?] at all
  | _, _, (@KUL.cons _ a b os ns related tail), s, f, vs, inner, us, exn, rest,
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
      obtain rfl := KUA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using
        KUL.typed_throw_reverse tail typed' tailShape
          (by simpa only [List.append_assoc, List.singleton_append] using operands)
  | _, _, (@KUL.site _ bt os ns tail), s, f, vs, inner, us, exn, rest,
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
      have last := KUL.typed_throw_reverse tail typedTail tailShape
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
  | _, _, (@KUL.run _ n X X' os ns body safe tail), s, f, vs, inner, us, exn, rest,
      typed, shape, operands => by
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have inside := KUL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      have last := KUL.typed_throw_reverse tail typedTail tailShape
        (by simpa only [List.append_assoc] using operands)
      refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ last
      simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · have bound := KUL.typed_throwRef_bound body (vs := [])
        (by simpa using typedBody) bodyActive
      obtain ⟨innerPre, innerOperands⟩ := last_operand operands (by simpa using bound)
      have inside := KUL.typed_throw_reverse body (vs := [])
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
  | _, _, .foldLabel _ _ _, _, _, _, _, _, _, _, _, shape, _ => by
    have first := congrArg fnv shape
    simp [fnv, Admin.val?] at first
  | _, _, (@KUL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, us, exn, rest,
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

  | _, _, .cut discard, s, f, vs, inner, us, exn, rest, _, shape, operands => by
    obtain ⟨ws, k, j, originalShape, kernel⟩ := kernel_cut_head discard shape rfl
    rcases kernel with ⟨_, impossible⟩ | ⟨a, rfl, _, u, rfl⟩
    · cases impossible
    · have last := congrArg List.getLast? operands
      simp at last
      subst a
      simpa only [originalShape, vals_append, List.append_assoc] using
        Closure.steps_kernel (P := P) (host := noHost) (t := s) (f := f)
          (Or.inr ⟨exn, rfl⟩) (vs ++ ws) j

/-- Exception normalization in the primitive typed-facts input shape, where
the exception reference may initially appear in the explicit ambient prefix. -/
theorem KUL.typed_throw_exit_reverse {x y : List Admin} (related : KUL R x y)
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
  exact KUL.typed_throw_reverse related typed bodyShape operands

/-- The complete kernel observation is exact through every recursive unwrap
phase, while arbitrary value prefixes and continuations may be discarded. -/
theorem KUL.typed_kernel_exit_reverse {x y : List Admin} (related : KUL R x y)
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
    exact KUL.typed_trap_reverse related typed bodyShape
  · exact KUL.typed_throw_exit_reverse related typed shape

private theorem region_noEsc (budget : ∃ S, ∀ i ∈ R, InstrB budU S i)
    (labels : instrsLabels R = []) : NoEsc (expression R) := by
  obtain ⟨S, budget⟩ := budget
  refine ⟨⟨S, ?_⟩, ?_⟩
  · rw [AdmsB_expression]
    exact budget
  · simp [labels]

private theorem NoEsc.no_blocked {X : List Admin} {vs : List Val} {e : Admin}
    {rest : List Admin} (safe : NoEsc X) (blocked : Blocked e)
    (shape : X = vals vs ++ e :: rest) : False := by
  rcases blocked with ⟨l, rfl⟩ | rfl | call
  · exact safe.no_br shape
  · exact safe.no_return shape
  · exact safe.no_retCall call shape

private theorem KUA.eq_of_blocked_right {a b : Admin} (related : KUA R a b)
    (blocked : Blocked b) : a = b := by
  cases related with
  | plain related =>
    cases related with
    | flat => rfl
    | _ => simp [Blocked, Admin.IsReturnCallRef] at blocked
  | retCallRef => rfl
  | _ => simp [Blocked, Admin.IsReturnCallRef] at blocked

/-- Branch/return/tail-call exits normalize with their exact values. The real
region guards rule out exits that an original running wrapper would catch. -/
theorem KUL.typed_blocked_exit_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = []) :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner : List Val} {e : Admin} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ e :: rest →
      e.val? = none → Blocked e →
      ∃ tail, Steps P noHost ⟨s, f, vals vs ++ x⟩
        ⟨s, f, vals (vs ++ inner) ++ e :: tail⟩
  | _, _, .nil, _, _, _, inner, _, _, _, shape, he, _ => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, he] at all
  | _, _, (@KUL.cons _ a b os ns related tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    cases inner with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      have run : Steps P noHost ⟨s, f, vals vs ++ a :: os⟩
          ⟨s, f, vals vs ++ a :: os⟩ := .refl
      obtain rfl := KUA.eq_of_blocked_right related blocked
      exact ⟨os, by simpa only [List.append_nil] using run⟩
    | cons v inner =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := KUA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      obtain ⟨j, run⟩ := KUL.typed_blocked_exit_reverse budget labels tail typed' tailShape he blocked
      refine ⟨j, ?_⟩
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using run
  | _, _, (@KUL.site _ bt os ns tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      obtain ⟨j, last⟩ := KUL.typed_blocked_exit_reverse budget labels tail typedTail tailShape he blocked
      refine ⟨j, Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_⟩
      · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
      · simpa only [List.append_assoc] using last
    · exact ((region_noEsc budget labels).no_blocked blocked bodyActive).elim
  | _, _, (@KUL.run _ n X X' os ns body safe tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBody : ContextTyped ⟨s, f, X⟩ := by
        apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
        simpa only [List.append_assoc, List.singleton_append] using typed
      have inside := KUL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      obtain ⟨j, last⟩ := KUL.typed_blocked_exit_reverse budget labels tail typedTail tailShape he blocked
      refine ⟨j, Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_⟩
      · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
      · simpa only [List.append_assoc] using last
    · have typedBody : ContextTyped ⟨s, f, X⟩ := by
        apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
        simpa only [List.append_assoc, List.singleton_append] using typed
      obtain ⟨j, run⟩ := KUL.typed_blocked_exit_reverse budget labels body
        (vs := []) (by simpa using typedBody) bodyActive he blocked
      have safeAfter := safe.steps run
      exact (safeAfter.no_blocked (vs := inner) (rest := j) blocked (by simp)).elim
  | _, _, (@KUL.foldIf _ bt T T' E E' X os ns _ _ _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.if_ bt T' E')) rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@KUL.foldBlock _ bt T T' X os ns _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.block bt T')) rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@KUL.foldLabel _ n C C' Xa os ns _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .label n [] C') rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@KUL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    rcases kernel with rfl | ⟨a, rfl⟩
    · obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
        (vs := []) (a := .trap) rfl he shape
      subst e
      simp [Blocked, Admin.IsReturnCallRef] at blocked
    · have shape' : vals [.ref (.exn a)] ++ .plain .throwRef :: ns =
          vals inner ++ e :: rest := by simpa [throwing, vals, Val.toAdmin] using shape
      obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj val?_throwRef he shape'
      subst e
      simp [Blocked, Admin.IsReturnCallRef] at blocked

  | _, _, .cut discard, s, f, vs, inner, e, rest, _, shape, he, blocked => by
    obtain ⟨_, _, _, _, kernel⟩ := kernel_cut_head discard shape he
    rcases kernel with ⟨_, rfl⟩ | ⟨a, _, rfl, _⟩ <;>
      simp [Blocked, Admin.IsReturnCallRef] at blocked

/-- The blocked-exit law in the exact ambient-prefix shape used by base facts. -/
theorem KUL.typed_blocked_ambient_exit_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {x y : List Admin} (related : KUL R x y) {s : Store H} {f : Frame}
    {vs us : List Val} {e : Admin} {rest : List Admin}
    (typed : ContextTyped ⟨s, f, vals vs ++ x⟩)
    (he : e.val? = none) (blocked : Blocked e)
    (shape : vals vs ++ y = vals us ++ e :: rest) :
    ∃ tail, Steps P noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, vals us ++ e :: tail⟩ := by
  have active : y.all Admin.isVal = false := by
    have all := congrArg (List.all · Admin.isVal) shape
    simpa [Admin.isVal, he] using all
  obtain ⟨inner, a, tail, ha, bodyShape⟩ := exists_head_of_not_all active
  have headShape : vals (vs ++ inner) ++ a :: tail = vals us ++ e :: rest := by
    simpa only [bodyShape, vals_append, List.append_assoc] using shape
  obtain ⟨operands, hhead, htail⟩ := Sim.vals_append_cons_inj ha he headShape
  subst a tail
  obtain ⟨j, run⟩ := KUL.typed_blocked_exit_reverse budget labels related typed bodyShape he blocked
  exact ⟨j, by simpa only [operands] using run⟩

/-- Guarded reverse unwrap has the kernel-aware primitive normalization facts.
The target alone supplies typing; all original exact-prefix APIs stay intact. -/
theorem typed_kernel_expanded_facts_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    (F : FuncInst H → FuncInst H → Prop) :
    TypedKernelFacts P F (fun x y => UIL R y x) (fun x y => KUL R y x) where
  src := fun related => KUL.of_UIL related
  values := by
    intro s t f vs us x y stores related typed values
    exact ⟨t, KUL.typed_values_reverse related typed values, stores⟩
  exit := by
    intro s t f vs us x y k j stores related typed exit shape
    by_cases kernel : k = [.trap] ∨ ∃ a, k = throwing a
    · refine ⟨t, [], [], ?_, stores, Or.inr kernel⟩
      simpa only [Execution.Core.vals_nil', List.nil_append, List.append_nil] using
        KUL.typed_kernel_exit_reverse related typed kernel shape
    · obtain ⟨e, rfl, he, blocked⟩ :
        ∃ e : Admin, k = [e] ∧ e.val? = none ∧ Blocked e := by
        cases exit with
        | br l => exact ⟨_, rfl, rfl, Or.inl ⟨l, rfl⟩⟩
        | return_ => exact ⟨_, rfl, rfl, Or.inr (Or.inl rfl)⟩
        | returnCallRef call => exact ⟨_, rfl, Admin.val?_of_isReturnCallRef call,
            Or.inr (Or.inr call)⟩
        | trap => exact (kernel (Or.inl rfl)).elim
        | throw a => exact (kernel (Or.inr ⟨a, rfl⟩)).elim
      have activeShape : vals vs ++ x = vals us ++ e :: j := by
        simpa only [List.append_assoc, List.singleton_append] using shape
      obtain ⟨tail, run⟩ := KUL.typed_blocked_ambient_exit_reverse (P := P)
        budget labels related typed he blocked activeShape
      exact ⟨t, us, tail,
        by simpa only [List.append_assoc, List.singleton_append] using run, stores, Or.inl rfl⟩


end Silmaril.Wasm.Binaryen.Unwrap
