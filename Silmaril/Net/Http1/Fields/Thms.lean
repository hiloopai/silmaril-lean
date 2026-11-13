module

public import Silmaril.Net.Http1.Fields.Defs
import Silmaril.Proofs.Net.Http1.Fields

/-!
# Field lookup and list syntax: laws

* `listElements_token`: a token value is a one-element list (no comma or whitespace in a
  token). So a field whose values are tokens has those tokens as its elements
  (`fieldElements_tokens`).
* `fieldValues_append`, `fieldElements_append`: lookup distributes over sections.
* `fieldHasToken_iff`: the Boolean test is membership up to case.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

theorem listElements_token {l : Bytes} (h : IsToken l) : listElements l = [l] :=
  Proofs.Fields.listElements_token h

theorem fieldValues_append (fs gs : List FieldLine) (n : Bytes) :
    fieldValues (fs ++ gs) n = fieldValues fs n ++ fieldValues gs n := by
  simp [fieldValues, List.filterMap_append]

theorem fieldElements_append (fs gs : List FieldLine) (n : Bytes) :
    fieldElements (fs ++ gs) n = fieldElements fs n ++ fieldElements gs n := by
  simp [fieldElements, fieldValues_append]

theorem flatMap_listElements_tokens : ∀ {vs : List Bytes}, (∀ v ∈ vs, IsToken v) →
    vs.flatMap listElements = vs
  | [], _ => rfl
  | v :: vs, h => by
    rw [List.flatMap_cons, listElements_token (h v (by simp)),
      flatMap_listElements_tokens fun w hw => h w (by simp [hw])]
    rfl

theorem fieldElements_tokens {fs : List FieldLine} {n : Bytes}
    (h : ∀ v ∈ fieldValues fs n, IsToken v) : fieldElements fs n = fieldValues fs n :=
  flatMap_listElements_tokens h

theorem fieldHasToken_iff (fs : List FieldLine) (n tok : Bytes) :
    fieldHasToken fs n tok = true ↔ ∃ e ∈ fieldElements fs n, lower e = lower tok := by
  simp [fieldHasToken]

example : fieldHasToken [⟨ascii "Connection", ascii "keep-alive, Upgrade"⟩,
    ⟨ascii "upgrade", ascii "websocket"⟩] (ascii "connection") (ascii "upgrade") = true := by decide

end Silmaril.Net.Http1
