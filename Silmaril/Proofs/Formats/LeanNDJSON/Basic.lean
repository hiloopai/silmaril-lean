module

public import Silmaril.Formats.LeanNDJSON.Validate.Defs

/-!
# Proofs for Lean-NDJSON validation
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.LeanNDJSON

open Silmaril.Formats.LeanNDJSON

theorem serialValid?_iff : ∀ (c : Counters) (es : List Event),
    serialValid? c es = true ↔ SerialValid c es
  | _, [] => by simp [serialValid?, SerialValid]
  | c, e :: es => by
    simp only [serialValid?, SerialValid, Bool.and_eq_true, List.all_eq_true]
    cases h : c.next e with
    | none => simp
    | some c' => simp [serialValid?_iff c' es]

theorem validate?_iff (es : List Event) : validate? es = true ↔ Valid es := by
  simp [validate?, Valid, DeclNamesNodup, serialValid?_iff]

end Silmaril.Proofs.Formats.LeanNDJSON
