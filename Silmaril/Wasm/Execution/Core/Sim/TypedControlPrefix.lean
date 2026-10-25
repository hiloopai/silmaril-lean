module

public import Silmaril.Wasm.Execution.Core.Sim.TypedPrefix
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.SingleThreaded.Agreement

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded SingleThreaded.Det

variable {H : Type}

set_option maxHeartbeats 0 in
set_option linter.unnecessarySeqFocus false in
/-- Control-head operand arity depends on the instruction and suffix operands,
not the numerical profile or the result of an inner runtime-context step. -/
theorem control_head_same_arity {P Q : Profile} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H}
    (hk : famOf e = .control)
    (h₁ : Head P s f args₁ e c₁) (h₂ : Head Q s f args₂ e c₂)
    (hp : args₁ = p ++ args₂) : p = [] := by
  have hc : ∀ {k : Fam}, famOf e = k → k ≠ .control → False :=
    fun h hk' => hk' (h ▸ hk)
  cases h₁ <;> try fam_excl
  all_goals (try (
    have lengths := congrArg List.length hp
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_nil, List.length_append] at lengths
    omega))
  all_goals (cases h₂ <;> try fam_excl)
  all_goals (try (
    have lengths := congrArg List.length hp
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_nil, List.length_cons, List.length_append] at lengths
    omega))
  all_goals (repeat' rcr_step)
  all_goals try { simp_all [Admin.IsCallRef] }
  case callRefNull.callRefFunc.inl | callRefNull.callRefFunc.inr =>
    rename_i vs a fi ps rs code hf he hn hcode ha w hcall
    rw [ha, ← List.append_assoc] at hp
    have last := congrArg List.getLast? hp
    simp at last
  case callRefFunc.callRefFunc.inl | callRefFunc.callRefFunc.inr =>
    rename_i vs₁ a₁ fi₁ ps₁ rs₁ code₁ hf₁ he₁ hn₁ hcode₁ ha₁
      vs₂ a₂ fi₂ ps₂ rs₂ code₂ hf₂ he₂ hn₂ hcode₂ ha₂ w hcall
    rw [ha₁, ha₂, ← List.append_assoc] at hp
    obtain ⟨operandsEq, last⟩ := append_singleton_inj.mp hp
    cases last
    rw [hf₁] at hf₂
    cases hf₂
    cases Expand.det he₁ he₂
    have lengths := congrArg List.length operandsEq
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at lengths
    omega
  case throw.throw =>
    rename_i ta₁ ti₁ ts₁ he₁ ht₁ hn₁ ta₂ ti₂ ts₂ he₂ hn₂ ht₂
    rw [ht₁] at ht₂
    cases ht₂
    cases Expand.det he₁ he₂
    have lengths := congrArg List.length hp
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at lengths
    omega

/-- Progress of an active typed fragment can only be a step when its first
non-value is neither an exit nor a bubbling instruction. -/
theorem ContextTyped.progress_nonexit {P : Profile} {s : Store H} {f : Frame}
    {vs : List Val} {e : Admin} {rest : List Admin}
    (typed : ContextTyped ⟨s, f, vals vs ++ e :: rest⟩)
    (he : e.val? = none) (blocked : ¬ Blocked e) (notrap : e ≠ .trap)
    (nothrow : e ≠ .plain .throwRef) :
    ∃ next, Step P divHost ⟨s, f, vals vs ++ e :: rest⟩ next := by
  obtain ⟨C, ts, xs, hs, _, hc, hcode⟩ := typed.fragment_ctx
  have progress := progress_aux (P := P) divHost_ok hs hcode f [] hc .nil
  change Out P divHost s f C.toTypeCtx C.labels C.return_
    (vals vs ++ e :: rest) ts at progress
  have active : fnv (vals vs ++ e :: rest) = (vs, e :: rest) := by
    simp [fnv_cons_of_none he]
  rcases progress with ⟨ws, shape, _⟩ | ⟨next, step⟩ | ⟨ws, tail, shape⟩ |
      ⟨ws, a, tail, shape⟩ | ⟨ws, l, tail, ts, shape, _, _⟩ |
      ⟨ws, tail, ts, shape, _, _⟩ | ⟨ws, r, c, tail, ts, shape, call, _, _⟩
  · have different := congrArg fnv shape
    rw [active] at different
    simp at different
  · exact ⟨next, step⟩
  · have different := congrArg fnv shape
    rw [active] at different
    simp at different
    exact (notrap different.2.1).elim
  · have different := congrArg fnv shape
    rw [active] at different
    simp [throwing, fnv_cons_of_none (a := .plain .throwRef) rfl] at different
    exact (nothrow different.2.1).elim
  · have different := congrArg fnv shape
    rw [active] at different
    simp [fnv_cons_of_none (a := .plain (.br l)) rfl] at different
    exact (blocked (.inl ⟨l, different.2.1⟩)).elim
  · have different := congrArg fnv shape
    rw [active] at different
    simp [fnv_cons_of_none (a := .plain .return_) rfl] at different
    exact (blocked (.inr (.inl different.2.1))).elim
  · have different := congrArg fnv shape
    rw [active] at different
    simp [fnv_cons_of_none (IsReturnCallRef.val_none call)] at different
    exact (blocked (.inr (.inr (different.2.1 ▸ call)))).elim

private theorem no_callout_without_prefix {s : Store H} {pre : List Val} {code : List Admin}
    (wide : decompose? s (vals pre ++ code) = none) : decompose? s code = none := by
  cases inner : decompose? s code with
  | none => rfl
  | some callout =>
    obtain ⟨E, a, hh, args⟩ := callout
    have lifted := decompose?_wrap pre [] inner
    simp only [List.append_nil, wide] at lifted
    cases lifted

/-- Typed cancellation includes every control and runtime-context head. The
auxiliary progress step supplies only an operand-arity bound; the conclusion
reuses the original selected head and its exact result. -/
theorem Step.cancel_values_active {P : Profile} {s : Store H} {f : Frame}
    {pre inner : List Val} {e : Admin} {rest : List Admin} {next : Config H}
    (typed : ContextTyped ⟨s, f, vals inner ++ e :: rest⟩)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (step : Step P noHost ⟨s, f, vals (pre ++ inner) ++ e :: rest⟩ next) :
    ∃ nextInner, Step P noHost ⟨s, f, vals inner ++ e :: rest⟩ nextInner ∧
      next = ⟨nextInner.store, nextInner.frame, vals pre ++ nextInner.code⟩ := by
  by_cases control : famOf e = .control
  · obtain ⟨outer, args, c₀, split, head, hn⟩ :=
      hostFree_head_inv he notrap nothrow step
    obtain ⟨progressNext, progressStep⟩ :=
      typed.progress_nonexit (P := P) he head.good.not_blocked notrap nothrow
    have wideNoCallout : decompose? s (vals pre ++ (vals inner ++ e :: rest)) = none := by
      simpa only [vals_append, Det.vals_nil, List.nil_append, List.append_nil,
        List.append_assoc] using (SingleThreaded.Step.noRedex step [] [])
    have innerNoCallout := no_callout_without_prefix wideNoCallout
    obtain innerStep | ⟨_, _, _, _, callout, _⟩ :=
      SingleThreaded.Step.split_host progressStep
    · obtain ⟨innerOuter, innerArgs, innerResult, innerSplit, innerHead, _⟩ :=
        hostFree_head_inv he notrap nothrow innerStep
      have bound : args.length ≤ inner.length := by
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
      have suffix : ∃ mid, inner = mid ++ args := by
        rcases append_eq_append_suffix split with ⟨mid, hm⟩ | ⟨extra, hx⟩
        · exact ⟨mid, hm⟩
        · have lengths := congrArg List.length hx
          have empty : extra = [] := List.eq_nil_of_length_eq_zero (by
            simp only [List.length_append] at lengths
            omega)
          subst extra
          exact ⟨[], by simpa using hx.symm⟩
      obtain ⟨mid, hm⟩ := suffix
      have hp : outer = pre ++ mid := by
        rw [hm, ← List.append_assoc] at split
        exact (List.append_cancel_right split).symm
      refine ⟨⟨c₀.store, c₀.frame, vals mid ++ c₀.code ++ rest⟩, ?_, ?_⟩
      · have lifted := Step.append_right (Step.vals_left head.toStep mid) rest
        simpa [hm, List.append_assoc] using lifted
      · simp [hn, hp, List.append_assoc]
    · rw [innerNoCallout] at callout
      cases callout
  · exact Step.cancel_values_noncontrol typed control step

/-- Both sequence-context boundaries can be cancelled while retaining the
actual selected step. Only the inner fragment needs an original typing witness;
the extra suffix may have arbitrary code. -/
theorem Step.cancel_instrs_active {P : Profile} {s : Store H} {f : Frame}
    {pre inner : List Val} {e : Admin} {tail suffix : List Admin} {next : Config H}
    (typed : ContextTyped ⟨s, f, vals inner ++ e :: tail⟩)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (step : Step P noHost ⟨s, f, vals (pre ++ inner) ++ e :: (tail ++ suffix)⟩ next) :
    ∃ nextInner, Step P noHost ⟨s, f, vals inner ++ e :: tail⟩ nextInner ∧
      next = ⟨nextInner.store, nextInner.frame, vals pre ++ nextInner.code ++ suffix⟩ := by
  obtain ⟨outer, args, c₀, split, head, hn⟩ := hostFree_head_inv he notrap nothrow step
  have projected : Step P noHost ⟨s, f, vals (pre ++ inner) ++ e :: tail⟩
      ⟨c₀.store, c₀.frame, vals outer ++ c₀.code ++ tail⟩ := by
    have lifted := Step.append_right (Step.vals_left head.toStep outer) tail
    simpa [split, List.append_assoc] using lifted
  obtain ⟨nextInner, innerStep, same⟩ :=
    Step.cancel_values_active typed he notrap nothrow projected
  refine ⟨nextInner, innerStep, ?_⟩
  have liftedEq := congrArg (fun c : Config H =>
    (⟨c.store, c.frame, c.code ++ suffix⟩ : Config H)) same
  simpa [hn, List.append_assoc] using liftedEq

end Silmaril.Wasm.Execution.Core.Sim
