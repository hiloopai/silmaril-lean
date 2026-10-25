module

public import Silmaril.Wasm.Binaryen.InlUnwrapThrowBoundary
public import Silmaril.Wasm.Binaryen.InlUnwrapBudget
public import Silmaril.Wasm.Execution.Core.Sim.TypedKernelNormalization

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}

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

private theorem UA.eq_of_blocked_right {a b : Admin} (related : UA R a b)
    (blocked : Blocked b) : a = b := by
  cases related with
  | plain related =>
    cases related with
    | flat => rfl
    | _ => simp [Blocked, Admin.IsReturnCallRef] at blocked
  | retCallRef => rfl
  | _ => simp [Blocked, Admin.IsReturnCallRef] at blocked

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

/-- Branch/return/tail-call exits normalize with their exact values. The real
region guards rule out exits that an original running wrapper would catch. -/
theorem UL.typed_blocked_exit_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = []) :
    ∀ {x y : List Admin}, UL R x y →
    ∀ {s : Store H} {f : Frame} {vs inner : List Val} {e : Admin} {rest : List Admin},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals inner ++ e :: rest →
      e.val? = none → Blocked e →
      ∃ tail, Steps P noHost ⟨s, f, vals vs ++ x⟩
        ⟨s, f, vals (vs ++ inner) ++ e :: tail⟩
  | _, _, .nil, _, _, _, inner, _, _, _, shape, he, _ => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, he] at all
  | _, _, (@UL.cons _ a b os ns related tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    cases inner with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      have run : Steps P noHost ⟨s, f, vals vs ++ a :: os⟩
          ⟨s, f, vals vs ++ a :: os⟩ := .refl
      obtain rfl := UA.eq_of_blocked_right related blocked
      exact ⟨os, by simpa only [List.append_nil] using run⟩
    | cons v inner =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := UA.eq_of_val_right related
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      obtain ⟨j, run⟩ := UL.typed_blocked_exit_reverse budget labels tail typed' tailShape he blocked
      refine ⟨j, ?_⟩
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using run
  | _, _, (@UL.site _ bt os ns tail), s, f, vs, inner, e, rest,
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
      obtain ⟨j, last⟩ := UL.typed_blocked_exit_reverse budget labels tail typedTail tailShape he blocked
      refine ⟨j, Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_⟩
      · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
      · simpa only [List.append_assoc] using last
    · exact ((region_noEsc budget labels).no_blocked blocked bodyActive).elim
  | _, _, (@UL.run _ n X X' os ns body safe tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBody : ContextTyped ⟨s, f, X⟩ := by
        apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
        simpa only [List.append_assoc, List.singleton_append] using typed
      have inside := UL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      obtain ⟨j, last⟩ := UL.typed_blocked_exit_reverse budget labels tail typedTail tailShape he blocked
      refine ⟨j, Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_⟩
      · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
      · simpa only [List.append_assoc] using last
    · exact ((UL.noEsc budget labels body safe).no_blocked blocked bodyActive).elim
  | _, _, (@UL.foldIf _ bt T T' E E' X os ns _ _ _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.if_ bt T' E')) rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@UL.foldBlock _ bt T T' X os ns _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.block bt T')) rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@UL.foldLabel _ n C C' Xa os ns _ _ _ tail), s, f, vs, inner, e, rest,
      typed, shape, he, blocked => by
    obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .label n [] C') rfl he shape
    subst e
    simp [Blocked, Admin.IsReturnCallRef] at blocked
  | _, _, (@UL.foldExit _ n ws K J os ns kernel tail), s, f, vs, inner, e, rest,
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

/-- The blocked-exit law in the exact ambient-prefix shape used by base facts. -/
theorem UL.typed_blocked_ambient_exit_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {x y : List Admin} (related : UL R x y) {s : Store H} {f : Frame}
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
  obtain ⟨j, run⟩ := UL.typed_blocked_exit_reverse budget labels related typed bodyShape he blocked
  exact ⟨j, by simpa only [operands] using run⟩

/-- Guarded reverse unwrap has the kernel-aware primitive normalization facts.
The target alone supplies typing; all original exact-prefix APIs stay intact. -/
theorem typed_kernel_facts_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    (F : FuncInst H → FuncInst H → Prop) :
    TypedKernelFacts P F (fun x y => UIL R y x) (fun x y => UL R y x) where
  src := fun related => UL.of_UIL related
  values := by
    intro s t f vs us x y stores related typed values
    exact ⟨t, UL.typed_values_reverse related typed values, stores⟩
  exit := by
    intro s t f vs us x y k j stores related typed exit shape
    by_cases kernel : k = [.trap] ∨ ∃ a, k = throwing a
    · refine ⟨t, [], [], ?_, stores, Or.inr kernel⟩
      simpa only [Execution.Core.vals_nil', List.nil_append, List.append_nil] using
        UL.typed_kernel_exit_reverse related typed kernel shape
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
      obtain ⟨tail, run⟩ := UL.typed_blocked_ambient_exit_reverse (P := P)
        budget labels related typed he blocked activeShape
      exact ⟨t, us, tail,
        by simpa only [List.append_assoc, List.singleton_append] using run, stores, Or.inl rfl⟩

end Silmaril.Wasm.Binaryen.Unwrap
