module

public import Silmaril.Prelude.Bytes.Checker.Defs
public import Silmaril.Prelude.Bytes.Native.Defs
-- Native runs interpret `cstringCheck`, so its code is loaded as `meta`.
public meta import Silmaril.Prelude.Bytes.Checker.Defs
import Silmaril.Proofs.Prelude.Bytes.Checker

/-! # Format checkers: the reference instance

Proofs are in `Silmaril.Proofs.Prelude.Bytes.Checker`.
-/

@[expose] public section

namespace Silmaril.KBytes

theorem cstringCheck_sound (b : KBytes) (s : List UInt8) (h : cstringCheck b s = true) :
    CString b s :=
  Proofs.Prelude.Bytes.cstringCheck_sound b s h

/-- NUL-terminated strings as a format checker. -/
def cstring : FormatChecker (List UInt8) where
  format := "cstring"
  Parses := CString
  check := cstringCheck
  sound := cstringCheck_sound

/-- NUL-terminated strings, by one wide read. Kernel fallback: one tree descent and one literal
comparison. -/
native_decider bytes.cstring := Silmaril.KBytes.cstringCheck with_kernel_fallback
  format cstring sound Silmaril.KBytes.cstringCheck_sound

end Silmaril.KBytes
