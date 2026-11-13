module

public import Silmaril.Wasi.Runtime.Launch.Defs
public import Silmaril.Proofs.Wasi.Runtime.Launch.Loop
public import Silmaril.Proofs.Wasi.Runtime.Launch.Image
public import Silmaril.Proofs.Wasi.Runtime.Launch.Valid

/-!
# `hello`'s x86 runtime at an ELF launch: theorems (header)

Part D of `docs/projects/wasm-wasi.md`. PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Runtime.Launch.*`,
namespace `Silmaril.Wasi.Runtime.Launch`).

**Any memory** (`Loop`): the proofs of `Silmaril.Wasi.Runtime` restated over every memory `M` with
`HelloMem M` (code fetchable at `codeBase`, `hi` readable at `dataBase`).
**`hello_toWrite`** starts from *any* state at `codeBase` with memory `M`, whatever its other
registers; **`helloLoopAt`** makes it a `HelloLoop Open.step segs ch e`.

**The launch** (`Image`): for a snapshot of the image `helloImage` (code `rx` at `0x401000`,
`hi` and the program header table `r` at `0x402000`) and an entry whose block does not wrap and
whose stack reservation lies above the image:
* **`launch_helloMem`**, `launch_rip`: LPS's launch state `launchState snapshot en inp` (the
  launch core with `rsp = sp`, and the initial memory with the 8 MiB stack and the entry
  block) holds the program and starts at `codeBase`. **`helloLaunch`**: it starts a `HelloLoop`.
* **`hello_processSafe`**: the launch is `ProcessSafe` (every flag oracle of the release machine
  `x86WithFlagOracle8`) for "a prefix of the OS image of `hello`'s WASI run against
  `stdoutImpl` on channel `1`, then `exit 0`". The LPS configuration is LPS's own
  `X86Launch.init`, aligned with the launch state by `initF_aligned`: the alignment hypothesis
  of `helloImg_psafe8` is discharged.

**Valid launches** (`Valid`): **`hello_processSafe_valid`**: the same from `X86Launch.ValidEntry`
alone. **`helloSnapshot_valid`**, **`hello_nonvacuous`**: the snapshot `helloSnapshot` passes
LPS's launch check on `helloEn`/`helloInp`, so the theorem is not vacuous.

**Not proved here**: `helloStart` itself is not a launch state (it has no stack and `rsp = 0`);
the launch state is a variant of it with the same code and data. `helloSnapshot` is
silmaril's parsed form of an ELF file (header, program headers, image), not file bytes, and its
program header table area holds zeros. The redirected filesystem runtime (`fsCode`) has no
launch counterpart: LPS's `initModel` binds only descriptors `0`, `1`, `2`, so descriptor `3`
is never open at a launch.
-/
