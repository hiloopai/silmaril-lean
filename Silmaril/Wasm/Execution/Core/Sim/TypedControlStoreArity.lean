module

public import Silmaril.Wasm.Execution.Core.Sim.TypedControlPrefix

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded SingleThreaded.Det

variable {H : Type}

set_option maxHeartbeats 0 in
set_option linter.unnecessarySeqFocus false in
/-- Control-head operand arity depends on the instruction and suffix operands,
not the numerical profile or the result of an inner runtime-context step. -/
theorem control_head_same_arity_storeRel {P Q : Profile} {s t : Store H} {F : FuncInst H → FuncInst H → Prop} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H}
    (stores : StoreRel F s t) (hk : famOf e = .control)
    (h₁ : Head P s f args₁ e c₁) (h₂ : Head Q t f args₂ e c₂)
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
    have types := congrArg (fun fs : List DefType => fs[a₁]?) stores.types
    simp only [List.getElem?_map, hf₁, hf₂, Option.map_some, Option.some.injEq] at types
    rw [types] at he₁
    cases Expand.det he₁ he₂
    have lengths := congrArg List.length operandsEq
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at lengths
    omega
  case throw.throw =>
    rename_i ta₁ ti₁ ts₁ he₁ ht₁ hn₁ ta₂ ti₂ ts₂ he₂ hn₂ ht₂
    have tags := congrArg Store.tags stores.other
    simp only at tags
    have tagLookup : s.tag? = t.tag? := by
      funext f x
      simp only [Store.tag?, tags]
    rw [tagLookup, ht₂] at ht₁
    cases ht₁
    cases Expand.det he₁ he₂
    have lengths := congrArg List.length hp
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append] at lengths
    omega

/-- Related function implementations retain the exact selected control-head
operand list. The target head is used only for an arity bound; source outcomes
are never replaced by a new numerical choice. -/
theorem control_head_storeRel_exists {P : Profile}
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s t : Store H} {f : Frame} {args : List Val} {e : Admin} {next : Config H}
    (stores : StoreRel F s t) (control : famOf e = .control)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (head : Head P s f args e next) : ∃ next', Head P t f args e next' := by
  have respects : HostRespects F (Det.noHost (H := H)) := by
    intro _ _ _ _ _ _ impossible
    exact impossible.elim
  obtain ⟨u, code, matched, _, _⟩ := Step.match_storeRel
    (B := fun _ _ => False) hF respects head.toStep t stores
  obtain ⟨outer, consumed, targetNext, split, targetHead, _⟩ :=
    hostFree_head_inv he notrap nothrow matched
  have empty := control_head_same_arity_storeRel stores control head targetHead split
  subst outer
  simp only [List.nil_append] at split
  subst consumed
  exact ⟨targetNext, targetHead⟩

end Silmaril.Wasm.Execution.Core.Sim
