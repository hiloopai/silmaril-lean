module

public import Silmaril.Machine.Process.LibMiniClient.Defs
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Insn
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Process
public import Silmaril.Proofs.Machine.Process.LibMiniClient.NonVacuity
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Cmain
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Start
public import Silmaril.Proofs.Machine.Process.LibMiniClient.StartRun
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Total

/-! # Ladder rung 12 as an LPS process: theorems (header)

PROVED (standard axioms; namespace `Silmaril.Proofs.Machine.Process.LibMiniClient`):

* `rung12_processSafe`: **conditional on `Task.startRun`**, every launch of the rung-12
  executable accepted by LPS's x86 launch (`X86Launch.ValidEntry`) is process-safe for
  `exitAllowed inp.fs` (traces are `[]` or `[exit 6]`, no error), for every flag oracle,
  refusal configuration and budget. Uses the program-independent bridge
  (`processSafe_of_launch`, `psafe_exit`).
* Instruction triples used by `_start`/`cmain` (`Insn`): `insn_triple`, `movI32_step`,
  `mov_step`, `leaRsp_step`, `xorSelf_step`, `storeI8Rsp_step`.

Non-vacuity (`NonVacuity`, namespace `Silmaril.Proofs.Machine.Process.LibMiniClient.Launch`):
* `launch_nonvacuous`: some snapshot of `image` (header and program headers read from the
  fixture bytes by silmaril's ELF reader, `hdr_ok`/`phs_ok`), entry and input pass
  `X86Launch.ValidEntry`, so the launch hypotheses of `rung12_processSafe` are satisfiable.
* `header_mutated_rejected`: a header with a wrong entry point is rejected.

**(T2): the chain is closed.** PROVED (standard axioms):

* `startRun_holds : Task.startRun` (`StartRun`). Built from:
  - `cmain_safeB` (`Cmain`): `cmain` meets `cmainSpec` (no arguments, returns `6`) under the
    **backed-stack template** `SafeB` (`Silmaril.Machine.Link.BackedSpec`), from the `Safe`
    contracts of `memset`/`memcpy` (the separation-logic layer's `fillSpec`/`copySpec`) and `len1` (R1's
    `len1Spec`) only;
  - `start_run`, `exitAt_of` (`Start`): `_start` runs to the `exit(6)` request given
    `cmain`'s contract;
  - `rung12_link` (R1's `validated_compose` on the validated link), `start_in_linked`,
    `cmain_in_linked`, `linked_in_seg1` (kernel evaluation of `Relocation.link`);
  - the launch state: `image_loaded`, `stack_zero`, `stack_rw`, `launch_split`, `stackFits`.
* **`rung12_processSafe_unconditional`**: every LPS launch of the rung-12 executable accepted
  by `X86Launch.ValidEntry` is process-safe for `exitAllowed inp.fs` (traces `[]` or
  `[exit 6]`, no error), for every flag oracle, refusal configuration and budget. No
  hypothesis beyond the launch.

**Total correctness** (`Total`, ), PROVED (standard axioms):
* `startRun_total`: from every valid launch state the open machine *reaches* `ExitAt` in
  finitely many steps. Composed with total triples along the acyclic call graph: the separation-logic layer's
  total libmini `exports_sat` (`safeT_of_sat`), `plusOne_safeT` (len1), `cmain_safeTB`,
  `start_total`. This uses the validated link's bytes but not `link_compose` (which is
  step-indexed).
* **`rung12_mustExit`**: LPS's must-exit tier `MustExitInAt … [6]` for every valid launch,
  oracle and refusal configuration (via the bridge's `mustExit_of_launch`).
* **`rung12_complete`**: `rung12_processSafe_unconditional ∧ rung12_mustExit`.

Trusted (not proved): silmaril's LPS port and its x86 launch (`X86Launch.init`,
`initialMemory`, `entryStack`), the handwritten `X86.Ext`/`Ext8` semantics behind
`Silmaril.Machine.X86.Open.step`, silmaril's ELF/linker readers that `Validated` mentions, and
the fixture bytes being the `build.sh` output.
-/
