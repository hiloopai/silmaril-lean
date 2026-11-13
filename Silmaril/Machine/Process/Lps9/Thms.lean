module

public import Silmaril.Machine.Process.Lps9.Defs
public import Silmaril.Proofs.Machine.Process.Lps9.Agree

/-! # The LPS `Ext9` machine: theorems (header)

PROVED (standard axioms; proofs in
`Silmaril.Proofs.Machine.Process.Lps9.Agree`, namespace `Silmaril.Proofs.Machine.Process.Lps9`):

* `x86WithFlagOracle9_eq`: `x86WithFlagOracle9 oracle = flagMachine oracle x86NativeStep9`.
* `ext9_decodeNew_syscall`, `open9_step_trap`: `Open9.step` is stuck at `0F 05`.
* `native9_of_ne_undecodable`: where `Ext8.fetch` is not `undecodable` (and off `0F 05`),
  `x86NativeStep9 = x86NativeStep8`.
* **`agrees_open9 : Agrees x86NativeStep9 Open9.step`**: the LPS process machine now executes
  every `Open9` step, so `Ext9`/jump-table bodies reach the process. This closes
  `round4/f2-safe-isa.md`'s "the process half is still Ext8-only" for `Open9`.
* `bt_open9`, `bt_native8`, `bt_native9`, **`not_agrees_native8_open9`** (mutation probe, added
  in review): on a concrete `bt eax, ecx` state, `Open9.step` and `x86NativeStep9` step while
  `x86NativeStep8` is `unmodeled`, so `Agrees x86NativeStep8 Open9.step` is false.
* `le_open9`, `safeNR_open9_of_open`, `must_open9_of_run`.
* **`psafe9_of_safeNR`**, **`mustExit9_of_must`**, `processSafe9_of_launchR`,
  `mustExit9_of_launchR`: the bridge on `x86WithFlagOracle9`, from `SafeNR A`/`Must A` for
  any `A` with `Le (ofFun Open9.step) A` (e.g. `loosen Open9.isa ⊤`).

Not here: `Str9`/`Sse9`/`SseF` forms under LPS (Z4 owns the string forms; XMM processes are an
SQLite item), and a proof that the `Ext9` access spans (`X86Accesses9.new9`) are complete;
they only matter under lazy reservations, which the bridge excludes.
-/
