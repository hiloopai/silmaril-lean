module

public import Silmaril.Wasm.Binaryen.InlUnwrapAlignment
public import Silmaril.Wasm.Execution.Core.Sim.TypedControlPrefix

@[expose] public section

/-! # Matching a bare-body step using original block typing

Store transport happens before typed sequence cancellation. The typing witness
therefore belongs only to the original block on the target store; no typing of
the transformed source or of its callees is assumed. A selected call may enter
related function code, retained by the resulting full administrative relation.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

/-- Enter the original block and match an actual computational step of its
bare body, including calls and runtime contexts, at the same numerical profile.
The untouched prefix and both outer continuations stay explicit. -/
theorem block_active_match {F : FuncInst H → FuncInst H → Prop}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    {s s' t : Store H} {f f' : Frame} {pre args bodyValues : List Val} {bt : BlockType}
    {body : List Instr} {sourceRest targetRest after tail : List Admin}
    {ps rs : List CValType} {e : Admin}
    (hst : StoreRel F s t) (resolved : f.module.blockType? bt = some (ps, rs))
    (arity : args.length = ps.length)
    (typed : ContextTyped ⟨t, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ targetRest⟩)
    (shape : expression body = vals bodyValues ++ e :: tail)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (safe : NoEsc (vals args ++ expression body))
    (selected : Step P Det.noHost
      ⟨s, f, vals (pre ++ args) ++ expression body ++ sourceRest⟩ ⟨s', f', after⟩) :
    ∃ (t' : Store H) (innerAfter sourceCore : List Admin),
      Relation.TransGen (Step P Det.noHost)
        ⟨t, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ targetRest⟩
        ⟨t', f', vals pre ++ [.label rs.length [] innerAfter] ++ targetRest⟩ ∧
      StoreRel F s' t' ∧ NoEsc innerAfter ∧ after = sourceCore ++ sourceRest ∧
      AdminsRel BI B sourceCore (vals pre ++ innerAfter) := by
  have entry : Step P Det.noHost
      ⟨t, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ targetRest⟩
      ⟨t, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)] ++ targetRest⟩ := by
    simpa only [vals_append, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.block resolved arity) pre) targetRest
  have innerTyped : ContextTyped ⟨t, f, vals (args ++ bodyValues) ++ e :: tail⟩ := by
    have inside : ContextTyped ⟨t, f, vals args ++ expression body⟩ :=
      ContextTyped.label (typed.step entry)
    simpa only [shape, vals_append, List.append_assoc] using inside
  have respects : HostRespects F (Det.noHost (H := H)) := by
    intro _ _ _ _ _ _ impossible
    exact impossible.elim
  have selected' : Step P Det.noHost
      ⟨s, f, vals (pre ++ (args ++ bodyValues)) ++ e :: (tail ++ sourceRest)⟩
      ⟨s', f', after⟩ := by
    simpa only [shape, vals_append, List.append_assoc, List.cons_append] using selected
  obtain ⟨outer, consumed, sourceResult, split, sourceHead, sourceShape⟩ :=
    hostFree_head_inv he notrap nothrow selected'
  obtain ⟨v, g, headAfter⟩ := sourceResult
  simp only [Config.mk.injEq] at sourceShape
  obtain ⟨rfl, rfl, rfl⟩ := sourceShape
  obtain ⟨u, matchedHeadAfter, matchedHead, stores, relatedHead⟩ :=
    Step.match_storeRel (B := B) hF respects sourceHead.toStep t hst
  have matched' : Step P Det.noHost
      ⟨t, f, vals (pre ++ (args ++ bodyValues)) ++ e :: (tail ++ sourceRest)⟩
      ⟨u, f', vals outer ++ matchedHeadAfter ++ (tail ++ sourceRest)⟩ := by
    have lifted := Step.append_right (Step.vals_left matchedHead outer) (tail ++ sourceRest)
    simpa only [split, vals_append, List.append_assoc, List.singleton_append] using lifted
  obtain ⟨innerResult, innerStep, result⟩ :=
    Step.cancel_instrs_active innerTyped he notrap nothrow matched'
  obtain ⟨v, g, innerAfter⟩ := innerResult
  simp only [Config.mk.injEq] at result
  obtain ⟨rfl, rfl, codeEq⟩ := result
  have coreEq : vals outer ++ matchedHeadAfter ++ tail = vals pre ++ innerAfter :=
    List.append_cancel_right (by simpa only [List.append_assoc] using codeEq)
  have bodyStep : Step P Det.noHost
      ⟨t, f, vals args ++ expression body⟩ ⟨u, f', innerAfter⟩ := by
    simpa only [shape, vals_append, List.append_assoc] using innerStep
  refine ⟨u, innerAfter, vals outer ++ headAfter ++ tail, ?_, stores,
    NoEsc.step bodyStep safe, by simp only [List.append_assoc], ?_⟩
  · exact (Relation.TransGen.single entry).tail
      (Step.append_right (Step.vals_left (Step.ctxtLabel bodyStep) pre) targetRest)
  · rw [← coreEq]
    exact ((AdminsRel.refl _).append relatedHead).append (AdminsRel.refl _)

end Silmaril.Wasm.Binaryen.Unwrap
