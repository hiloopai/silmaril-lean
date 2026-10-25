module

public import Silmaril.Wasm.Binaryen.InlUnwrapAlignment
public import Silmaril.Wasm.Execution.Core.Sim.TypedNormalization

@[expose] public section

/-! # Typed completion of a block whose bare body is already values

This is the value phase of the block-only converse. The actual target block
supplies its signature and operand boundary through ambient typing, then
entry and label completion produce exactly the original value prefix and
bare-body values. No new eligibility test is imposed on the executable pass.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

/-- Enter and complete the real block when its bare body is already values.
The input prefix may contain both untouched values and block parameters. -/
theorem block_values_run {s : Store H} {f : Frame} {vs us : List Val}
    {bt : BlockType} {body : List Instr}
    (typed : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩)
    (bodyValues : expression body = vals us) :
    Steps P (fun _ _ _ _ => False)
      ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ ⟨s, f, vals vs ++ vals us⟩ := by
  obtain ⟨pre, args, ps, rs, hvs, _, _, entry, _⟩ :=
    ContextTyped.block_entry (P := P) (rest := []) (by simpa using typed)
  have done : Step P (fun _ _ _ _ => False)
      ⟨s, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)]⟩
      ⟨s, f, vals vs ++ vals us⟩ := by
    rw [bodyValues, hvs]
    simpa only [vals_append, List.append_assoc] using
      Step.vals_left (Step.labelVals (P := P) (host := fun _ _ _ _ => False)
        (s := s) (f := f) (vs := args ++ us) (n := rs.length) (cont := [])) pre
  have entry' : Step P (fun _ _ _ _ => False)
      ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)]⟩ := by
    simpa using entry
  exact entry'.steps.tail done

end Silmaril.Wasm.Binaryen.Unwrap
