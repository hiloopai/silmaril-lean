module

public import Silmaril.Net.Http.Method.Defs
public import Silmaril.Net.Http.Field.Thms

@[expose] public section

/-!
# HTTP request methods: theorems

PROVED (standard axioms):

* `isIdempotent_of_isSafe`: safe methods are idempotent (§9.2.2);
* `toToken_ofToken`: the token of the method of a token is the token; `ofToken_toToken`: on
  canonical methods, `ofToken` inverts `toToken`; `canonical_ofToken`;
* `isValid_named`: the named methods are tokens.
-/

namespace Silmaril.Net.Http.Method

open Silmaril.Net.Http.Field

theorem isIdempotent_of_isSafe {m : Method} (h : m.isSafe = true) : m.isIdempotent = true := by
  cases m <;> simp_all [isSafe, isIdempotent]

theorem not_isSafe_of_not_isIdempotent {m : Method} (h : m.isIdempotent = false) :
    m.isSafe = false := by
  cases m <;> simp_all [isSafe, isIdempotent]

theorem toToken_ofToken (t : List UInt8) : (ofToken t).toToken = t := by
  unfold ofToken
  split
  · rename_i m hm
    simpa using List.find?_some hm
  · rfl

theorem ofToken_toToken {m : Method} (h : m.Canonical) : ofToken m.toToken = m := by
  cases m with
  | other t =>
    have hnone : named.find? (fun m => m.toToken == t) = none := by
      rw [List.find?_eq_none]
      intro m hm
      simpa using h m hm
    have h1 : ofToken (other t).toToken = ofToken t := rfl
    rw [h1]
    unfold ofToken
    rw [hnone]
  | _ => rfl

theorem canonical_ofToken (t : List UInt8) : (ofToken t).Canonical := by
  unfold ofToken
  split
  · rename_i m hm
    have hmem : m ∈ named := List.mem_of_find?_eq_some hm
    simp only [named, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · rename_i hnone
    intro m hm
    simpa using List.find?_eq_none.mp hnone m hm

theorem isValid_named : ∀ m ∈ named, m.isValid = true := by decide

end Silmaril.Net.Http.Method
