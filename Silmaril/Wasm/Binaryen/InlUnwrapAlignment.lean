module

public import Silmaril.Wasm.Binaryen.InlUnwrapBlock
public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock
public import Silmaril.Wasm.Execution.Core.Sim.StepMatch

@[expose] public section

/-! # Aligning an actual block across related stores

Block entry precedes the same body step on the other store. The matched body
may enter a related callee, so its result is related by the full recursive code
closure rather than assumed identical. `ContextTyped.block_ready` supplies the
signature and operands for an active block in a well-typed ambient context.

These are alignment laws for the recursive unwrap converse, not yet that
converse or a new module-pass correctness theorem.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Match a body's actual step, including calls, after entering the corresponding
block on a related store. The outer stack prefix and continuation stay explicit. -/
theorem block_body_match {F : FuncInst H → FuncInst H → Prop}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F host)
    {s s' t : Store H} {f f' : Frame} {pre args : List Val} {bt : BlockType}
    {body : List Instr} {rest after : List Admin} {ps rs : List CValType}
    (hst : StoreRel F s t) (resolved : f.module.blockType? bt = some (ps, rs))
    (arity : args.length = ps.length)
    (bodyStep : Step P host ⟨s, f, vals args ++ expression body⟩ ⟨s', f', after⟩) :
    ∃ (t' : Store H) (after' : List Admin),
      Relation.TransGen (Step P host)
        ⟨t, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ rest⟩
        ⟨t', f', vals pre ++ [.label rs.length [] after'] ++ rest⟩ ∧
      StoreRel F s' t' ∧ AdminsRel BI B after after' := by
  obtain ⟨t', after', matched, stores, code⟩ :=
    Step.match_storeRel (B := B) hF hhost bodyStep t hst
  refine ⟨t', after', ?_, stores, code⟩
  have entry : Step P host
      ⟨t, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ rest⟩
      ⟨t, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)] ++ rest⟩ := by
    simpa only [vals_append, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.block resolved arity) pre) rest
  exact (Relation.TransGen.single entry).tail
    (Step.append_right (Step.vals_left (Step.ctxtLabel matched) pre) rest)

end Silmaril.Wasm.Binaryen.Unwrap
