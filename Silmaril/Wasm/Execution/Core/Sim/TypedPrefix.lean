module

public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

/-! # Typed cancellation of an untouched operand-stack prefix

The inner fragment's actual typing supplies enough operands for the selected
head rule. Cancellation retains that rule and its numerical result instead of
re-running progress and choosing a potentially different numerical outcome.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

set_option hygiene false in
local macro "typed_family_arity" : tactic => `(tactic| (
  generalize shape : vals args ++ [e] = code at h
  cases h <;> (
    have last := congrArg List.getLast? shape
    simp at last
    subst e
    have length := congrArg List.length shape
    simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at length
    apply typed.active_arity
    intro C it ha
    have hi := ha.plain_inv_ne
    cases hi <;> rename_i hi <;> cases hi <;> simp_all)) )

/-- Parametric rules cannot borrow operands from outside a typed fragment. -/
theorem parametric_typed_arity {s : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest out : List Admin}
    (h : ParametricStep (vals args ++ [e]) out)
    (typed : FragmentTyped ⟨s, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- The bound includes every original floating-point choice at the same profile. -/
theorem numeric_typed_arity {s : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest out : List Admin}
    (h : NumericStep P (vals args ++ [e]) out)
    (typed : FragmentTyped ⟨s, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- SIMD and relaxed-SIMD rules retain their selected operands and result. -/
theorem vector_typed_arity {s : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest out : List Admin}
    (h : VectorStep P (vals args ++ [e]) out)
    (typed : FragmentTyped ⟨s, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- Local/global accesses respect the typed fragment's operand boundary. -/
theorem variable_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : VariableStep ⟨s, f, vals args ++ [e]⟩ next)
    (typed : FragmentTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- Table rules cannot consume an untouched earlier stack prefix. -/
theorem table_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : TableStep P ⟨s, f, vals args ++ [e]⟩ next)
    (typed : FragmentTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- Memory rules include the original grow success/failure choice. -/
theorem memory_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [e]⟩ next)
    (typed : FragmentTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- Reference rules retain the actual selected cast/test outcome. -/
theorem reference_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : RefStep ⟨s, f, vals args ++ [e]⟩ next)
    (typed : FragmentTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  typed_family_arity

/-- Arity extraction retains the active frame's real type table, needed by
instructions whose operand count depends on a referenced type. -/
theorem ContextTyped.active_arity_types {s : Store H} {f : Frame} {vs : List Val}
    {a : Admin} {rest : List Admin} {n : Nat}
    (h : ContextTyped ⟨s, f, vals vs ++ a :: rest⟩)
    (arity : ∀ C it, C.types = f.module.types → AdminOk s C a it →
      n ≤ it.params.length) : n ≤ vs.length := by
  have typed : ContextTyped ⟨s, f, vals vs ++ [a]⟩ :=
    ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using h)
  obtain ⟨C, ts, xs, _, hC, htypes, hcode⟩ := typed.fragment_types
  obtain ⟨mid, xs₁, _, hp, ht, _⟩ := AdminsOk.split hcode hC (vals vs) [a] rfl (by simp)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types ht
  have htypes₀ := congrArg (fun C : Context => C.types) (Context.initLocals_frameView C xs₁)
  have htypes' : (C.initLocals xs₁).types = f.module.types :=
    (show (C.initLocals xs₁).types = C.types by
      simpa only [Context.frameView] using htypes₀).trans htypes
  have h₁ := hv.length_eq
  have h₂ := hsub.length_eq
  have h₃ := hsub'.1.length_eq
  have h₄ := arity _ _ htypes' ha
  simp only [List.nil_append, List.length_append] at h₁ h₂ h₃ h₄
  omega

set_option linter.unnecessarySeqFocus false in
/-- GC aggregate rules include the type-dependent field count of struct.new. -/
theorem aggregate_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : AggregateStep ⟨s, f, vals args ++ [e]⟩ next)
    (typed : ContextTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  generalize shape : vals args ++ [e] = code at h
  cases h
  case structNew x d fs operands hd he hn hp =>
    have last := congrArg List.getLast? shape
    simp at last
    subst e
    have length := congrArg List.length shape
    simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at length
    apply typed.active_arity_types
    intro C it htypes ha
    have hi := ha.plain_inv_ne
    cases hi <;> rename_i hi <;> cases hi
    case structNew d' fs' hd' he' =>
      have same : C.type? x = f.type? x := by simp [Context.type?, Frame.type?, htypes]
      rw [same, hp] at he'
      cases he'
      cases Det.Expand.det hd hd'
      simp_all [Ty.length]
  all_goals
    have last := congrArg List.getLast? shape
    simp at last
    subst e
    have length := congrArg List.length shape
    simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at length
    apply typed.fragment.active_arity
    intro C it ha
    have hi := ha.plain_inv_ne
    cases hi <;> rename_i hi <;> cases hi <;> simp_all

/-- Non-control instructions are active non-values; constants belong to control
for decomposition purposes and therefore cannot satisfy this hypothesis. -/
theorem noncontrol_val_none {e : Admin} (h : Det.famOf e ≠ .control) :
    e.val? = none := by
  cases e with
  | plain i => cases i <;> simp_all [Det.famOf, Admin.val?]
  | _ => simp_all [Det.famOf]

/-- The selected non-control head consumes only operands in the typed fragment. -/
theorem head_typed_arity {s t : Store H} {f : Frame} {args vs : List Val}
    {e : Admin} {rest : List Admin} {next : Config H}
    (h : Det.Head P s f args e next) (noncontrol : Det.famOf e ≠ .control)
    (typed : ContextTyped ⟨t, f, vals vs ++ e :: rest⟩) : args.length ≤ vs.length := by
  have rel := h.fam_inv noncontrol
  generalize Det.famOf e = k at rel
  cases k with
  | parametric => obtain ⟨_, h, _⟩ := rel; exact parametric_typed_arity h typed.fragment
  | numeric => obtain ⟨_, h, _⟩ := rel; exact numeric_typed_arity h typed.fragment
  | vector => obtain ⟨_, h, _⟩ := rel; exact vector_typed_arity h typed.fragment
  | «variable» => exact variable_typed_arity rel typed.fragment
  | table => exact table_typed_arity rel typed.fragment
  | memory => exact memory_typed_arity rel typed.fragment
  | reference => exact reference_typed_arity rel typed.fragment
  | aggregate => exact aggregate_typed_arity rel typed
  | control => exact rel.elim

/-- Reuse the original chosen family rule at any host semantics. This conversion
does not invoke numerical determinism or select another permissible result. -/
theorem head_noncontrol_step {s : Store H} {f : Frame} {args : List Val}
    {e : Admin} {next : Config H} {host : HostSemantics H}
    (h : Det.Head P s f args e next) (noncontrol : Det.famOf e ≠ .control) :
    Step P host ⟨s, f, vals args ++ [e]⟩ next := by
  have rel := h.fam_inv noncontrol
  generalize Det.famOf e = k at rel
  cases k with
  | parametric => obtain ⟨_, chosen, hn⟩ := rel; cases hn; exact .parametric chosen
  | numeric => obtain ⟨_, chosen, hn⟩ := rel; cases hn; exact .numeric chosen
  | vector => obtain ⟨_, chosen, hn⟩ := rel; cases hn; exact .vector chosen
  | «variable» => exact .variable rel
  | table => exact .table rel
  | memory => exact .memory rel
  | reference => exact .reference rel
  | aggregate => exact .aggregate rel
  | control => exact rel.elim

private theorem split_within_suffix {pre inner outer args : List Val}
    (split : pre ++ inner = outer ++ args) (bound : args.length ≤ inner.length) :
    ∃ mid, inner = mid ++ args ∧ outer = pre ++ mid := by
  have suffix : ∃ mid, inner = mid ++ args := by
    rcases Det.append_eq_append_suffix split with ⟨mid, hm⟩ | ⟨extra, he⟩
    · exact ⟨mid, hm⟩
    · have lengths := congrArg List.length he
      have empty : extra = [] := by
        cases extra with
        | nil => rfl
        | cons a extra => simp only [List.length_append, List.length_cons] at lengths; omega
      subst extra
      exact ⟨[], by simpa using he.symm⟩
  obtain ⟨mid, hm⟩ := suffix
  refine ⟨mid, hm, ?_⟩
  rw [hm, ← List.append_assoc] at split
  exact (List.append_cancel_right split).symm

/-- An actual host-free step at a non-control head cancels an untouched operand
prefix when the inner fragment is typed in its original active context.

The result retains the same numerical profile, selected floating-point/SIMD
result, grow outcome, store update, and frame update. All eight non-control Core
families are covered, including type-dependent GC operand counts. -/
theorem Step.cancel_values_noncontrol {s t : Store H} {f : Frame}
    {pre inner : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals inner ++ e :: rest⟩)
    (noncontrol : Det.famOf e ≠ .control)
    (step : Step P Det.noHost ⟨s, f, vals (pre ++ inner) ++ e :: rest⟩ next) :
    ∃ nextInner, Step P Det.noHost ⟨s, f, vals inner ++ e :: rest⟩ nextInner ∧
      next = ⟨nextInner.store, nextInner.frame, vals pre ++ nextInner.code⟩ := by
  have notrap : e ≠ .trap := by rintro rfl; exact noncontrol rfl
  have nothrow : e ≠ .plain .throwRef := by rintro rfl; exact noncontrol rfl
  obtain ⟨outer, args, c₀, split, head, hn⟩ :=
    hostFree_head_inv (noncontrol_val_none noncontrol) notrap nothrow step
  obtain ⟨mid, hm, hp⟩ := split_within_suffix split (head_typed_arity head noncontrol typed)
  refine ⟨⟨c₀.store, c₀.frame, vals mid ++ c₀.code ++ rest⟩, ?_, ?_⟩
  · have lifted := Step.vals_left (head_noncontrol_step (host := Det.noHost) head noncontrol) mid
    have lifted' := Step.append_right lifted rest
    simpa [hm, List.append_assoc] using lifted'
  · simp [hn, hp, List.append_assoc]

end Silmaril.Wasm.Execution.Core.Sim
