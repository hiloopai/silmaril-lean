module

public import Silmaril.Net.Quic.Error.Defs

@[expose] public section

/-!
# QUIC transport error codes: theorems

PROVED (standard axioms, inline):

* `TransportError.ofCode_code`: the registry lookup inverts `code`;
* `TransportError.code_ofCode`: a code that is found is the code of what is found;
* `TransportError.code_injective`: distinct errors have distinct codes;
* `TransportError.code_lt`: every code fits in two bytes (`< 0x200`), well inside the 62-bit
  variable-length integer range of §16.

CHECKED: sample lookups, including a CRYPTO_ERROR and an unregistered code.
-/

namespace Silmaril.Net.Quic.TransportError

theorem ofCode_code (e : TransportError) : ofCode e.code = some e := by
  cases e <;> try rfl
  rename_i a; simp only [code, ofCode]; split <;> simp_all <;> omega

theorem code_ofCode {n : Nat} {e : TransportError} (h : ofCode n = some e) : e.code = n := by
  unfold ofCode at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp only [code] <;> omega

theorem code_injective {e e' : TransportError} (h : e.code = e'.code) : e = e' := by
  have := ofCode_code e; rw [h, ofCode_code] at this; exact (Option.some.inj this).symm

theorem code_lt (e : TransportError) : e.code < 0x200 := by cases e <;> simp [code] <;> omega

example : ofCode 0x07 = some frameEncodingError := rfl
example : ofCode 0x0a = some protocolViolation := rfl
/-- TLS alert 120 (`no_application_protocol`) as CRYPTO_ERROR `0x0178` (RFC 9001 §8.1). -/
example : ofCode 0x0178 = some (cryptoError 120) := by decide
example : ofCode 0x11 = none := by decide
example : ofCode 0x0200 = none := by decide

end Silmaril.Net.Quic.TransportError
