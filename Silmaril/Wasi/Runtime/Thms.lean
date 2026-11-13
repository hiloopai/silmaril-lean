module

public import Silmaril.Wasi.Runtime.Defs
public import Silmaril.Proofs.Wasi.Runtime.Loop
public import Silmaril.Proofs.Wasi.Runtime.Image

/-!
# A concrete x86 runtime of `hello`: theorems (header)

Part D of `docs/projects/wasm-wasi.md`. PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Runtime.*`,
namespace `Silmaril.Wasi.Runtime`).

**Refuted** (`Loop`): **`not_helloRt_exists`**: the frozen `Task.helloRt_exists` of
`Silmaril.Wasi.Os` is false, because `WriteStub` is empty (`writeStub_empty`): its `source` field
asks for every non-empty list as a write source, and LPS reads at most `MAX_RW_COUNT` bytes per
`write` (`writeSource_length_le`). The `WriteStub`/`HelloRt` results of `Silmaril.Wasi.Os` are
therefore vacuous; the invariant form below replaces them.

**The invariant form** (`Loop`):

* `WriteStub.toLoop`, `HelloRt.toLoop`: `WriteLoop`/`HelloLoop` generalise the exact-state
  obligations; `HelloLoop.ofRefines`: a runtime transports to every refining machine.
* **`ioSafe_writeLoop`**, **`helloLoop_ioSafe`**, **`helloLoop_psafe`**, **`helloLoop_e2e`**: a
  write loop is `IoSafeN` with `lpsEnv` (short writes included); a runtime of `hello` is
  `IoSafeN` for `helloAllowed ch fs` (a prefix of `hi`, then `exit 0`), LPS process-safe on every
  agreeing native machine, and its trace is the OS image of `helloRun`.

**The concrete program** (`Image`; `helloCode` in `Silmaril.Wasi.Runtime.Defs`), on `Open.step`:

* `movEsi_step` … `movEdi0_step`, `resume_regs`, `loop_back`, `loop_out`, `hello_toWrite`,
  `hello_toExit`: its runs between `syscall`s, one listing-law step per instruction.
* `hello_writeSource`, `hello_handles`: at the loop's `syscall`, `writeArm` handles the request
  and the source is exactly the bytes of `hi` left.
* **`helloLoopImg`**: the program is a `HelloLoop Open.step segs ch e` whenever descriptor `1` of
  `e` is the live channel `ch`. **`helloLoop_exists`**: `Task.helloLoop_exists`.
  **`initModel_stdout`**: LPS's `initModel` binds descriptor `1` to channel `1`.
* **`helloImg_psafe`**, **`helloImg_psafe8`**: the program is LPS process-safe for "a prefix of
  `hi` on `ch`, then `exit 0`", on every native machine agreeing with `Open.step`, and on the
  bridge's release machine `x86WithFlagOracle8` for every flag oracle with the trace stated as
  the OS image of `hello`'s WASI run against `stdoutImpl`.

**Not proved here**: the program is hand-written, not compiled from the component, and is not
related step by step to the host's plays (the refinement is on traces). Launch: `helloStart` is
not shown to be an `X86Launch` state of an ELF image (its memory has no stack and its own two
mappings); `helloImg_psafe8` takes an aligned configuration as a hypothesis. A launch variant with a stack,
from LPS's own `X86Launch.init` and without that hypothesis, is in `Silmaril.Wasi.Runtime.Launch`.
-/
