module

public import Silmaril.Machine.Process.Lps9.Str.Defs
public import Silmaril.Proofs.Machine.Process.Lps9.Str

/-! # The LPS `Ext9` + string machine: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.Process.Lps9.Str`,
namespace `Silmaril.Proofs.Machine.Process.Lps9.Str`):

* `x86WithFlagOracle9Str_eq`: `x86WithFlagOracle9Str oracle = flagMachine oracle
  x86NativeStep9Str` (by definition).
* `decodeStr_syscall`, `str9_step_trap`: `Str9.step` is stuck at `0F 05`.
* `nativeStr_of_ne`: where `Ext8.fetch` decodes (or truncates), off `0F 05`,
  `x86NativeStep9Str` is `x86NativeStep8`.
* **`agrees_str9 : Agrees x86NativeStep9Str Str9.step`**: the LPS process machine now
  executes every `Str9` step (every `Open9` step and the three string forms, one element per
  step), so P7's bridge theorems (`psafe_of_safeNR`, `mustExit_of_must`, generic in the
  agreeing step) and Z4's `IoSpec` (`ioSafe_psafe`) apply to `Str9.step` bodies.
* Mutation probe: `stos_str9`, `stos_native9`, **`not_agrees_native9_str9`**,
  `stos_nativeStr`: on a concrete `rep stosq` state, `Str9.step` and `x86NativeStep9Str`
  step while P7's `x86NativeStep9` is `unmodeled`.

Not here: a proof that the string access spans (`strAccesses`) are complete (they matter
only under lazy reservations, which the bridge excludes), and any hardware check of the
string semantics.
-/
