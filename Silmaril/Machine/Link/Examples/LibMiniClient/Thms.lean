module

public import Silmaril.Machine.Link.Examples.LibMiniClient.Defs
public import Silmaril.Machine.Link.FnSpec.Thms
public import Silmaril.Proofs.Machine.Link.LibMiniClient.PlusOne
public import Silmaril.Proofs.Machine.Link.LibMiniClient.Client
public import Silmaril.Proofs.Machine.Link.LibMiniClient.Compose
public import Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity

/-! # Ladder rung 12 composed under the `FnSpec` link logic: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Machine.Link.LibMiniClient.*`, namespace
`Silmaril.Proofs.Machine.Link.LibMiniClient`):

* `plusOne_safe`: `sub $8,%rsp; call f; add $8,%rsp; add $1,%rax; ret` at `a` is
  `Safe (n + 1)` for `plusOneSpec S` whenever `f` is `Safe n` for `S` (code level, any `S`).
* `client_sat`: a unit shaped like `client.o` satisfies `TU.Sat`, relocation-parametric
  (every slot, placement and valuation; the PLT32 field is read back from the patched bytes).
* On the validated rung 12 link (`Silmaril.Machine.Link.Fixtures.LibMiniClientBfd`):
  `units_objects` (the units are the prepared inputs), `start_sat`, `main_sat`,
  `client_sat'`, `libmini_sat` (the separation-logic layer's `exports_sat`, no re-verification), `units_sat`,
  `closed`, `abi`, `exec_sections`, `len1_addr`; rejection tests `obj3_strlen_not_memcpy`
  (the code check is not vacuous) and `abi_rejects_ms64`.
* `len1_composed`: **the end-to-end theorem**: the executable parses, the linker reproduces
  the link, and `len1` at `0x401060` meets `len1Spec` (`strlen`'s `scanSpec` plus one) at every
  step index, in the linked image and on every machine state holding the loader image.
*: `len1_composedOn step` for every machine `step` with
  `[ExtendsOpen step]` (the unit contracts `*_satOn`, `closedOn` are proved once for the logic
  `logicOn step`), and **`len1_composed9`**, its instance on the open machine over `Ext9`
  (`Open9.step`, which is also `JumpTable.step`). `len1_composed` is the instance at
  `Open.step`. The non-vacuity witness below is for `Open.step`; on `Open9` the loaded-machine
  clause has the same hypotheses.
* Non-vacuity (`Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity`): `len1_nonvacuous`, a
  concrete machine state that holds the executable's loader image (installed from the parsed
  image itself) and whose non-image part splits as `len1Spec.SysVPre ⟨0x8000, "A"⟩ 0x401060
  0x7008 0x401000 ∗ F`, so the hypotheses of `len1_composed`'s loaded-machine clause are
  jointly satisfiable for the same `records` and `out`; `len1_concrete` applies
  `len1_composed` to it.

Not verified: `_start`, `cmain`, `memmove`, `memcmp` (their exports carry `unverified`, a spec
with a false precondition, so the theorem says nothing about them). Partial correctness only.
-/
