module

public import Silmaril.Wasm.Binaryen.InlUnwrapRecursiveValues
public import Silmaril.Wasm.Execution.Core.Sim.TypedControlPrefix

@[expose] public section

/-! # Operand bounds from related original heads

Unwrap changes nested code, but retains each structural head's external operand
arity. The original head can therefore supply an operand bound without assuming
that the transformed body or its callees are typed.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}

theorem head_context_args_nil {s : Store H} {f : Frame} {args : List Val}
    {e : Admin} {next : Config H} (context : e.IsCtx) (head : Head P s f args e next) :
    args = [] := by
  have control : famOf e = .control := by cases e <;> simp_all [Admin.IsCtx, famOf]
  have hc : ∀ {k : Fam}, famOf e = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ control)
  cases e <;> try exact context.elim
  all_goals (cases head <;> try fam_excl)
  all_goals (simp_all [Admin.IsCallRef])

theorem head_block_bound {s t : Store H} {f : Frame} {args inner : List Val}
    {bt : BlockType} {body original : List Instr} {rest : List Admin} {next : Config H}
    (head : Head P s f args (.plain (.block bt body)) next)
    (typed : ContextTyped ⟨t, f, vals inner ++ .plain (.block bt original) :: rest⟩) :
    args.length ≤ inner.length := by
  have hc : ∀ {k : Fam}, famOf (.plain (.block bt body)) = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ rfl)
  cases head <;> try fam_excl
  all_goals try { simp_all [Admin.IsCallRef] }
  rename_i ps rs arity resolved
  apply typed.active_arity_types
  intro C it types ha
  cases ha with
  | plain hi =>
    cases hi with
    | block signature _ =>
      obtain ⟨ps', rs', resolved', plen, _⟩ := blockType_of_types types signature
      rw [resolved] at resolved'
      cases resolved'
      exact Nat.le_of_eq (arity.trans plen)
    | _ => rename_i h; cases h

private theorem head_loop_bound {s t : Store H} {f : Frame} {args inner : List Val}
    {bt : BlockType} {body original : List Instr} {rest : List Admin} {next : Config H}
    (head : Head P s f args (.plain (.loop bt body)) next)
    (typed : ContextTyped ⟨t, f, vals inner ++ .plain (.loop bt original) :: rest⟩) :
    args.length ≤ inner.length := by
  have hc : ∀ {k : Fam}, famOf (.plain (.loop bt body)) = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ rfl)
  cases head <;> try fam_excl
  all_goals try { simp_all [Admin.IsCallRef] }
  rename_i ps rs arity resolved
  apply typed.active_arity_types
  intro C it types ha
  cases ha with
  | plain hi =>
    cases hi with
    | loop signature _ =>
      obtain ⟨ps', rs', resolved', plen, _⟩ := blockType_of_types types signature
      rw [resolved] at resolved'
      cases resolved'
      exact Nat.le_of_eq (arity.trans plen)
    | _ => rename_i h; cases h

theorem head_if_bound {s t : Store H} {f : Frame} {args inner : List Val}
    {bt : BlockType} {left right originalLeft originalRight : List Instr}
    {rest : List Admin} {next : Config H}
    (head : Head P s f args (.plain (.if_ bt left right)) next)
    (typed : ContextTyped
      ⟨t, f, vals inner ++ .plain (.if_ bt originalLeft originalRight) :: rest⟩) :
    args.length ≤ inner.length := by
  have hc : ∀ {k : Fam}, famOf (.plain (.if_ bt left right)) = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ rfl)
  cases head <;> try fam_excl
  all_goals try { simp_all [Admin.IsCallRef] }
  all_goals
    apply typed.fragment.active_arity
    intro C it ha
    have hi := ha.plain_inv_ne
    cases hi <;> rename_i hi <;> cases hi <;> simp_all
  all_goals omega

private theorem head_try_bound {s t : Store H} {f : Frame} {args inner : List Val}
    {bt : BlockType} {cs : List Catch} {body original : List Instr}
    {rest : List Admin} {next : Config H}
    (head : Head P s f args (.plain (.tryTable bt cs body)) next)
    (typed : ContextTyped ⟨t, f, vals inner ++ .plain (.tryTable bt cs original) :: rest⟩) :
    args.length ≤ inner.length := by
  have hc : ∀ {k : Fam}, famOf (.plain (.tryTable bt cs body)) = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ rfl)
  cases head <;> try fam_excl
  all_goals try { simp_all [Admin.IsCallRef] }
  rename_i ps rs arity resolved
  apply typed.active_arity_types
  intro C it types ha
  cases ha with
  | plain hi =>
    cases hi with
    | tryTable signature _ _ =>
      obtain ⟨ps', rs', resolved', plen, _⟩ := blockType_of_types types signature
      rw [resolved] at resolved'
      cases resolved'
      exact Nat.le_of_eq (arity.trans plen)
    | _ => rename_i h; cases h

/-- A structural pair is either literally the same head, or every selected
bare head consumes no more operands than the original typed head provides. -/
theorem UA.head_operand_bound {a b : Admin} (related : UA R a b) :
    a = b ∨ ∀ {s t : Store H} {f : Frame} {args inner : List Val}
      {rest : List Admin} {next : Config H},
      Head P s f args b next → ContextTyped ⟨t, f, vals inner ++ a :: rest⟩ →
        args.length ≤ inner.length := by
  cases related with
  | plain related =>
    cases related with
    | flat => exact Or.inl rfl
    | block _ => exact Or.inr head_block_bound
    | loop _ => exact Or.inr head_loop_bound
    | if_ _ _ => exact Or.inr head_if_bound
    | tryTable _ => exact Or.inr head_try_bound
  | label _ _ =>
    right
    intro s t f args inner rest next head _
    rw [head_context_args_nil (by trivial) head]
    exact Nat.zero_le _
  | handler _ =>
    right
    intro s t f args inner rest next head _
    rw [head_context_args_nil (by trivial) head]
    exact Nat.zero_le _
  | frame _ =>
    right
    intro s t f args inner rest next head _
    rw [head_context_args_nil (by trivial) head]
    exact Nat.zero_le _
  | _ => exact Or.inl rfl

private theorem split_within_suffix {pre inner outer args : List Val}
    (split : pre ++ inner = outer ++ args) (bound : args.length ≤ inner.length) :
    ∃ mid, inner = mid ++ args ∧ outer = pre ++ mid := by
  have suffix : ∃ mid, inner = mid ++ args := by
    rcases append_eq_append_suffix split with ⟨mid, hm⟩ | ⟨extra, he⟩
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

/-- Cancel an untouched operand prefix using only the related original head's
actual typing. Source/target continuations and nested bodies may differ. The
selected source step, numerical result, store update and frame update remain
exactly the same; no transformed typing assumption is introduced. -/
theorem UA.cancel_values_active {s : Store H} {f : Frame}
    {pre inner : List Val} {a b : Admin} {sourceRest targetRest : List Admin}
    {next : Config H} (related : UA R a b)
    (typed : ContextTyped ⟨s, f, vals inner ++ a :: targetRest⟩)
    (he : b.val? = none) (notrap : b ≠ .trap) (nothrow : b ≠ .plain .throwRef)
    (step : Step P noHost ⟨s, f, vals (pre ++ inner) ++ b :: sourceRest⟩ next) :
    ∃ nextInner, Step P noHost ⟨s, f, vals inner ++ b :: sourceRest⟩ nextInner ∧
      next = ⟨nextInner.store, nextInner.frame, vals pre ++ nextInner.code⟩ := by
  rcases related.head_operand_bound (H := H) (P := P) with rfl | bound
  · have typedOne : ContextTyped ⟨s, f, vals inner ++ [a]⟩ := by
      apply ContextTyped.suffix (rest := targetRest)
      simpa only [List.append_assoc, List.singleton_append] using typed
    obtain ⟨innerNext, innerStep, result⟩ := Step.cancel_instrs_active
      (tail := []) (suffix := sourceRest) typedOne he notrap nothrow (by simpa using step)
    refine ⟨⟨innerNext.store, innerNext.frame, innerNext.code ++ sourceRest⟩, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append, List.append_nil] using
        Step.append_right innerStep sourceRest
    · simpa only [List.append_assoc] using result
  · obtain ⟨outer, args, c₀, split, head, result⟩ :=
      hostFree_head_inv he notrap nothrow step
    obtain ⟨mid, hm, hp⟩ := split_within_suffix split (bound head typed)
    refine ⟨⟨c₀.store, c₀.frame, vals mid ++ c₀.code ++ sourceRest⟩, ?_, ?_⟩
    · have lifted := Step.append_right (Step.vals_left head.toStep mid) sourceRest
      simpa [hm, List.append_assoc] using lifted
    · simp [result, hp, List.append_assoc]

end Silmaril.Wasm.Binaryen.Unwrap
