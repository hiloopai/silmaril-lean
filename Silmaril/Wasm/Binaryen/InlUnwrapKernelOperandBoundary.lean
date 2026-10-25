module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelNormalization
public import Silmaril.Wasm.Execution.Core.Sim.TypedControlStoreArity

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}

/-- A related structural head either is identical or has an operand bound from
only the original typed side, even when the function implementations differ. -/
theorem KUA.head_operand_bound {a b : Admin} (related : KUA R a b) :
    a = b ∨ ∀ {s t : Store H} {f : Frame} {args inner : List Val}
      {rest : List Admin} {next : Config H},
      Head P s f args b next → ContextTyped ⟨t, f, vals inner ++ a :: rest⟩ →
        args.length ≤ inner.length := by
  cases related with
  | plain h => exact UA.head_operand_bound (UA.plain h)
  | label _ _ | handler _ | frame _ =>
    right
    intro s t f args inner rest next head _
    rw [head_context_args_nil (by trivial) head]
    exact Nat.zero_le _
  | _ => exact Or.inl rfl

private theorem selected_head_bound {s : Store H} {f : Frame}
    {pre inner outer args : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨s, f, vals inner ++ e :: rest⟩)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (head : Head P s f args e next) (split : pre ++ inner = outer ++ args) :
    args.length ≤ inner.length := by
  by_cases control : famOf e = .control
  · have selected := Step.append_right (Step.vals_left head.toStep outer) rest
    have sourceEq : vals outer ++ (vals args ++ [e]) ++ rest =
        vals (pre ++ inner) ++ e :: rest := by
      calc _ = vals (outer ++ args) ++ e :: rest := by simp
        _ = _ := by rw [← split]
    rw [sourceEq] at selected
    obtain ⟨innerNext, innerStep, _⟩ :=
      Step.cancel_values_active typed he notrap nothrow selected
    obtain ⟨innerOuter, innerArgs, innerResult, innerSplit, innerHead, _⟩ :=
      hostFree_head_inv he notrap nothrow innerStep
    have both : (pre ++ innerOuter) ++ innerArgs = outer ++ args := by
      simpa [innerSplit, List.append_assoc] using split
    rcases append_eq_append_suffix both with ⟨extra, extraEq⟩ | ⟨extra, extraEq⟩
    · have lengths := congrArg List.length innerSplit
      have suffixLengths := congrArg List.length extraEq
      simp only [List.length_append] at lengths suffixLengths
      omega
    · obtain rfl := control_head_same_arity control head innerHead extraEq
      simp only [List.nil_append] at extraEq
      subst args
      have lengths := congrArg List.length innerSplit
      simp only [List.length_append] at lengths
      omega
  · exact head_typed_arity head control typed

private theorem selected_related_head_bound
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t) {f : Frame}
    {pre inner outer args : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals inner ++ e :: rest⟩)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (head : Head P s f args e next) (split : pre ++ inner = outer ++ args) :
    args.length ≤ inner.length := by
  by_cases control : famOf e = .control
  · obtain ⟨targetNext, targetHead⟩ :=
      control_head_storeRel_exists hF stores control he notrap nothrow head
    exact selected_head_bound typed he notrap nothrow targetHead split
  · exact head_typed_arity head control typed

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

/-- Original typing bounds the actual selected bare head throughout the full
recursive unwrap relation. In particular, a transformed running body cannot
borrow operands from outside its original runtime wrapper. -/
theorem KUL.typed_operand_bound
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t) :
    ∀ {x y : List Admin}, KUL R x y →
    ∀ {f : Frame} {vs inner pre outer args : List Val}
      {e : Admin} {rest : List Admin} {next : Config H},
      ContextTyped ⟨t, f, vals vs ++ x⟩ → y = vals inner ++ e :: rest →
      e.val? = none → e ≠ .trap → e ≠ .plain .throwRef →
      Head P s f args e next → pre ++ (vs ++ inner) = outer ++ args →
      args.length ≤ (vs ++ inner).length
  | _, _, .nil, _, _, _, _, _, _, _, _, _, _, shape, he, _, _, _, _ => by
    have all := congrArg (List.all · Admin.isVal) shape
    simp [Admin.isVal, he] at all
  | _, _, (@KUL.cons _ a b os ns related tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    cases inner with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      rcases related.head_operand_bound (H := H) (P := P) with rfl | bound
      · simpa only [List.append_nil] using selected_related_head_bound hF stores (inner := vs)
          typed he notrap nothrow head (by simpa using split)
      · simpa using bound head typed
    | cons v inner =>
      simp only [vals_cons', List.cons_append] at shape
      obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
      obtain rfl := KUA.eq_of_val_right related
      have typed' : ContextTyped ⟨t, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [List.append_assoc, List.singleton_append] using
        KUL.typed_operand_bound hF stores tail typed' tailShape he notrap nothrow head
          (pre := pre) (by simpa only [List.append_assoc, List.singleton_append] using split)
  | _, _, (@KUL.site _ bt os ns tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have typedBlock : ContextTyped ⟨t, f, vals vs ++ [.plain (.block bt R)]⟩ := by
        apply ContextTyped.suffix
        simpa only [List.append_assoc, List.singleton_append] using typed
      have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
      have typedTail : ContextTyped ⟨t, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using
        KUL.typed_operand_bound hF stores tail typedTail tailShape he notrap nothrow head
          (pre := pre) (by simpa only [List.append_assoc] using split)
    · obtain ⟨blockPre, blockArgs, ps, rs, stack, _, _, entry, _⟩ :=
        ContextTyped.block_entry (P := P) (rest := os) (by simpa using typed)
      have typedBody : ContextTyped ⟨t, f, vals (blockArgs ++ inner) ++ e :: insideRest⟩ := by
        have after : ContextTyped
            ⟨t, f, vals blockPre ++ [.label rs.length [] (vals blockArgs ++ expression R)] ++ os⟩ :=
          typed.step (by simpa only [List.append_assoc, List.singleton_append] using entry)
        have body : ContextTyped ⟨t, f, vals blockArgs ++ expression R⟩ :=
          ContextTyped.label after
        simpa only [bodyActive, vals_append, List.append_assoc] using body
      have bound := selected_related_head_bound hF stores typedBody he notrap nothrow head
        (pre := pre ++ blockPre) (outer := outer)
        (by simpa only [stack, List.append_assoc] using split)
      have lengths := congrArg List.length stack
      simp only [List.length_append] at bound lengths ⊢
      omega
  | _, _, (@KUL.run _ n X X' os ns body safe tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    have typedBody : ContextTyped ⟨t, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    rcases split_active shape with ⟨u, w, bodyValues, tailShape, rfl⟩ |
        ⟨insideRest, bodyActive, _⟩
    · have inside := KUL.typed_values_reverse (P := P) body (vs := []) typedBody bodyValues
      have inside' : Steps P noHost ⟨t, f, X⟩ ⟨t, f, vals u⟩ := by
        simpa only [Execution.Core.vals_nil', List.nil_append] using inside
      have complete := (Closure.steps_label inside' n []).tail Step.labelVals
      have first := Steps.append_right (Steps.vals_left complete vs) os
      have typedTail : ContextTyped ⟨t, f, vals (vs ++ u) ++ os⟩ := by
        have after := typed.steps (Closure.steps_congr first (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using after
      simpa only [List.append_assoc] using
        KUL.typed_operand_bound hF stores tail typedTail tailShape he notrap nothrow head
          (pre := pre) (by simpa only [List.append_assoc] using split)
    · have bound := KUL.typed_operand_bound hF stores body (vs := [])
        (by simpa using typedBody) bodyActive he notrap nothrow head
        (pre := pre ++ vs) (outer := outer)
        (by simpa only [List.nil_append, List.append_assoc] using split)
      simpa only [List.nil_append] using Nat.le_trans bound
        (by simp only [List.nil_append, List.length_append]; omega)
  | _, _, (@KUL.foldIf _ bt T T' E E' X os ns _ _ _ _ tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    obtain ⟨hinner, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.if_ bt T' E')) rfl he shape
    subst inner e
    simpa using head_if_bound head typed
  | _, _, (@KUL.foldBlock _ bt T T' X os ns _ _ tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    obtain ⟨hinner, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .plain (.block bt T')) rfl he shape
    subst inner e
    simpa using head_block_bound head typed
  | _, _, (@KUL.foldLabel _ n C C' Xa os ns _ _ tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    obtain ⟨hinner, hhead, _⟩ := Sim.vals_append_cons_inj
      (vs := []) (a := .label n [] C') rfl he shape
    subst inner e
    rw [head_context_args_nil (by trivial) head]
    exact Nat.zero_le _
  | _, _, (@KUL.foldExit _ n ws K J os ns kernel tail), f, vs, inner, pre, outer, args,
      e, rest, next, typed, shape, he, notrap, nothrow, head, split => by
    rcases kernel with rfl | ⟨a, rfl⟩
    · obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj
        (vs := []) (a := .trap) rfl he shape
      exact (notrap hhead.symm).elim
    · have shape' : vals [.ref (.exn a)] ++ .plain .throwRef :: ns =
          vals inner ++ e :: rest := by simpa [throwing, vals, Val.toAdmin] using shape
      obtain ⟨_, hhead, _⟩ := Sim.vals_append_cons_inj val?_throwRef he shape'
      exact (nothrow hhead.symm).elim

  | _, _, .cut discard, f, vs, inner, pre, outer, args, e, rest, next,
      _, shape, he, notrap, nothrow, _, _ => by
    obtain ⟨_, _, _, _, kernel⟩ := kernel_cut_head discard shape he
    rcases kernel with ⟨_, rfl⟩ | ⟨a, _, rfl, _⟩
    · exact (notrap rfl).elim
    · exact (nothrow rfl).elim

private theorem throwRef_head_args {s : Store H} {f : Frame} {args : List Val}
    {next : Config H} (head : Head P s f args (.plain .throwRef) next) :
    args = [.ref .null] := by
  have hc : ∀ {k : Fam}, famOf (.plain .throwRef) = k → k ≠ .control → False :=
    fun h hn => hn (h ▸ rfl)
  cases head <;> try fam_excl
  all_goals simp_all [Admin.IsCallRef]

/-- Every actual selected head respects the recursive boundary, including the
null throw_ref computation. Allocated-exception bubbling is handled as a cut. -/
theorem KUL.typed_head_operand_bound
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t)
    {x y : List Admin} (related : KUL R x y) {f : Frame}
    {vs inner pre outer args : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals vs ++ x⟩)
    (shape : y = vals inner ++ e :: rest) (he : e.val? = none)
    (head : Head P s f args e next) (split : pre ++ (vs ++ inner) = outer ++ args) :
    args.length ≤ (vs ++ inner).length := by
  by_cases nothrow : e ≠ .plain .throwRef
  · exact KUL.typed_operand_bound hF stores related typed shape he head.good.ne_trap
      nothrow head split
  · have equal : e = .plain .throwRef := Classical.not_not.mp nothrow
    subst e
    obtain rfl := throwRef_head_args head
    exact KUL.typed_throwRef_bound related typed shape

private theorem operand_suffix {pre inner outer args : List Val}
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

/-- Split the exact selected operands out of the transformed fragment.
All actual head rules are covered, with unrelated ambient values kept outside. -/
theorem KUL.selected_head_operands
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t)
    {x y : List Admin} (related : KUL R x y) {f : Frame}
    {vs inner pre outer args : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals vs ++ x⟩)
    (shape : y = vals inner ++ e :: rest) (he : e.val? = none)
    (head : Head P s f args e next) (split : pre ++ (vs ++ inner) = outer ++ args) :
    ∃ mid, vs ++ inner = mid ++ args ∧ outer = pre ++ mid :=
  operand_suffix split (KUL.typed_head_operand_bound hF stores related typed shape he head split)

/-- Cancel a selected head without excluding null throw_ref. The resulting
inner step uses that very head and retains its source store/frame update. -/
theorem KUL.cancel_head_active
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t)
    {x y : List Admin} (related : KUL R x y) {f : Frame}
    {vs inner pre outer args : List Val} {e : Admin} {tail suffix : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals vs ++ x⟩)
    (shape : y = vals inner ++ e :: tail) (he : e.val? = none)
    (head : Head P s f args e next) (split : pre ++ (vs ++ inner) = outer ++ args) :
    ∃ innerNext, Step P noHost ⟨s, f, vals (vs ++ inner) ++ e :: tail⟩ innerNext ∧
      (⟨next.store, next.frame, vals outer ++ next.code ++ (tail ++ suffix)⟩ : Config H) =
        ⟨innerNext.store, innerNext.frame, vals pre ++ innerNext.code ++ suffix⟩ := by
  obtain ⟨mid, operands, untouched⟩ :=
    KUL.selected_head_operands hF stores related typed shape he head split
  refine ⟨⟨next.store, next.frame, vals mid ++ next.code ++ tail⟩, ?_, ?_⟩
  · simpa [operands, List.append_assoc] using
      Step.append_right (Step.vals_left head.toStep mid) tail
  · simp [untouched, List.append_assoc]

/-- Cancel both untouched sequence boundaries of a computational bare step
using only its recursively related original's typing. This retains the exact
selected profile/outcome and every source store/frame update. -/
theorem KUL.cancel_instrs_active
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} (stores : StoreRel F s t)
    {x y : List Admin} (related : KUL R x y) {f : Frame} {vs inner pre : List Val}
    {e : Admin} {tail suffix : List Admin} {next : Config H}
    (typed : ContextTyped ⟨t, f, vals vs ++ x⟩)
    (shape : y = vals inner ++ e :: tail)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (step : Step P noHost
      ⟨s, f, vals (pre ++ (vs ++ inner)) ++ e :: (tail ++ suffix)⟩ next) :
    ∃ nextInner, Step P noHost ⟨s, f, vals (vs ++ inner) ++ e :: tail⟩ nextInner ∧
      next = ⟨nextInner.store, nextInner.frame, vals pre ++ nextInner.code ++ suffix⟩ := by
  obtain ⟨outer, args, c₀, split, head, result⟩ :=
    hostFree_head_inv he notrap nothrow step
  have bound := KUL.typed_operand_bound hF stores related typed shape he notrap nothrow head split
  obtain ⟨mid, hm, hp⟩ := operand_suffix split bound
  refine ⟨⟨c₀.store, c₀.frame, vals mid ++ c₀.code ++ tail⟩, ?_, ?_⟩
  · have lifted := Step.append_right (Step.vals_left head.toStep mid) tail
    simpa [hm, List.append_assoc] using lifted
  · simp [result, hp, List.append_assoc]

end Silmaril.Wasm.Binaryen.Unwrap
