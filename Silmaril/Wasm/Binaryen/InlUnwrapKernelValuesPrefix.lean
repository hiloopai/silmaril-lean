module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelRunning

@[expose] public section

/-! # Continue past reverse unwrap prefixes that are already values

Only the original prefix normalizes. The selected bare step and its complete
code are unchanged, including the rank used by the continuation callback.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} {m : Nat}

/-- Normalize a related original prefix whose bare prefix is values, then use
the continuation's match for the exact selected source step. The callback sees
only the normalized original typing, with the enlarged ambient value prefix. -/
theorem KUL.values_prefix_continue_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {original bare originalRest bareRest : List Admin} {ambient us : List Val}
    {sourceNext : Config H} (related : KUL R original bare)
    (typed : ContextTyped ⟨t, f, vals ambient ++ original ++ originalRest⟩)
    (values : bare = vals us)
    (selected : Step P noHost ⟨s, f, vals ambient ++ bare ++ bareRest⟩ sourceNext)
    (continuation : ContextTyped ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ →
      Step P noHost ⟨s, f, vals (ambient ++ us) ++ bareRest⟩ sourceNext →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        sourceNext ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ m) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ original ++ originalRest⟩ m := by
  have normalize : Steps P noHost
      ⟨t, f, vals ambient ++ original ++ originalRest⟩
      ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ := by
    simpa only [vals_append, List.append_assoc] using
      Steps.append_right (KUL.typed_values_reverse related typed.suffix values) originalRest
  have selected' : Step P noHost
      ⟨s, f, vals (ambient ++ us) ++ bareRest⟩ sourceNext := by
    simpa only [values, vals_append, List.append_assoc] using selected
  exact Matched.of_steps normalize (continuation (typed.steps normalize) selected')

/-- A values-only site is removed on the original side before continuing at
the same actual bare step. -/
theorem site_values_continue_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame} {bt : BlockType}
    {originalRest bareRest : List Admin} {ambient us : List Val} {sourceNext : Config H}
    (typed : ContextTyped ⟨t, f, vals ambient ++ [.plain (.block bt R)] ++ originalRest⟩)
    (values : expression R = vals us)
    (selected : Step P noHost
      ⟨s, f, vals ambient ++ expression R ++ bareRest⟩ sourceNext)
    (continuation : ContextTyped ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ →
      Step P noHost ⟨s, f, vals (ambient ++ us) ++ bareRest⟩ sourceNext →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        sourceNext ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ m) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [.plain (.block bt R)] ++ originalRest⟩ m := by
  apply KUL.values_prefix_continue_reverse (bare := expression R) ?_ typed values selected continuation
  simpa only [List.append_nil] using KUL.site (R := R) bt KUL.nil

/-- A values-only running body, including recursively inserted wrappers,
normalizes and finishes its original label before continuing. Escape freedom
is retained as the original running-phase guard. -/
theorem running_values_continue_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame} {n : Nat}
    {original bare originalRest bareRest : List Admin} {ambient us : List Val}
    {sourceNext : Config H} (body : KUL R original bare) (safe : NoEsc original)
    (typed : ContextTyped ⟨t, f, vals ambient ++ [.label n [] original] ++ originalRest⟩)
    (values : bare = vals us)
    (selected : Step P noHost ⟨s, f, vals ambient ++ bare ++ bareRest⟩ sourceNext)
    (continuation : ContextTyped ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ →
      Step P noHost ⟨s, f, vals (ambient ++ us) ++ bareRest⟩ sourceNext →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        sourceNext ⟨t, f, vals (ambient ++ us) ++ originalRest⟩ m) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [.label n [] original] ++ originalRest⟩ m := by
  apply KUL.values_prefix_continue_reverse (bare := bare) ?_ typed values selected continuation
  simpa only [List.append_nil] using KUL.run body safe KUL.nil

end Silmaril.Wasm.Binaryen.Unwrap
