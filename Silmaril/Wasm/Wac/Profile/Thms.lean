module

public import Silmaril.Wasm.Wac.Profile.Defs
public import Silmaril.Wasm.Component.Wat.Thms
public import Silmaril.Proofs.Wasm.Wac.Profile

/-!
# WAC composition profile: the round trip

The reader/printer of component WAT (`Silmaril.Wasm.Component.Wat`, `read_print`)
restricted to the composition profile:

* `profile_norm`: the profile is closed under the normal form (proof in
  `Silmaril.Proofs.Wasm.Wac.Profile`);
* `readProfile_print`: reading the printed text of a profile component gives its
  normal form, *in the profile*; `readProfile_print_of_norm`: exactly the component
  on normal forms;
* `readProfile_sound`: what `readProfile` accepts is a profile component read by
  the full reader; `readProfile_print_read`: printing what was read and reading it
  again gives its normal form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Wat

/-- **Round trip on the profile.** -/
theorem readProfile_print {c : Ast} (h : Profile c) :
    readProfile (print c) = some (norm c) := by
  have hn : isProfile (norm c) = true := profile_norm h
  simp [readProfile, read_print, hn]

/-- **Exact round trip on normal profile components.** -/
theorem readProfile_print_of_norm {c : Ast} (h : Profile c) (hn : norm c = c) :
    readProfile (print c) = some c := by
  rw [readProfile_print h, hn]

/-- The profile reader accepts only profile components read by the full reader. -/
theorem readProfile_sound {s : String} {c : Ast} (h : readProfile s = some c) :
    Profile c ∧ read s = some c := by
  unfold readProfile at h
  cases hr : read s with
  | none => simp [hr] at h
  | some d =>
    simp only [hr, Option.bind_some] at h
    by_cases hp : isProfile d = true
    · simp only [hp, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    · simp [hp] at h

/-- Printing a profile component that was read, and reading it again, gives its
normal form. -/
theorem readProfile_print_read {s : String} {c : Ast} (h : readProfile s = some c) :
    readProfile (print c) = some (norm c) :=
  readProfile_print (readProfile_sound h).1

/-- Two profile components print to the same text iff their normal forms agree. -/
theorem print_eq_iff_profile {c d : Ast} :
    print c = print d ↔ norm c = norm d :=
  print_eq_iff c d

end Silmaril.Wasm.Wac
