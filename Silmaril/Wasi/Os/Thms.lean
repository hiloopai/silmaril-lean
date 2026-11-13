module

public import Silmaril.Wasi.Os.Defs
public import Silmaril.Proofs.Wasi.Os.Write
public import Silmaril.Proofs.Wasi.Os.Trace

/-!
# WASI hosts over `IoSpec`: theorems (header)

Part D of `docs/projects/wasm-wasi.md`. PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Os.*`, namespace
`Silmaril.Wasi.Os`).

**The x86 side** (`Write`), over `lpsEnv` (the sound LPS arms of `Silmaril.Machine.Process.IoSpec`):

* **`ioSafe_writeStub`**: a stdout host stub (`WriteStub`) with bytes `bs` left is `IoSafeN` for
  every trace predicate allowing the prefixes of `bs.map (writeEv ch)`, and every continuation
  after the full write. LPS allows short writes; the stub loops (`writeStub_answer`,
  `writeStub_next`).
* **`helloRt_ioSafe`**: an x86 runtime of `hello` (`HelloRt`) is `IoSafeN` with `lpsEnv` for
  `helloAllowed ch fs`: a prefix of the write of `hi`, then `exit 0`.
* **`helloRt_psafe`**: on every native machine agreeing with `c` (`Agrees`), an aligned LPS
  configuration of the runtime is process-safe for LPS (`PSafeF`) with these traces
  (`ioSafe_psafeLps`).

**The WASI side** (`Trace`):

* **`hello_writesHi`**: for every host, every write of `hello` carries `hi` (invariant method).
* **`hello_os`**, **`hello_link_os`**: the OS image (`osTrace`) of every play of `hello`, and of
  the answers of every host linked below it, is `k` copies of `hiOut ch`.
* **`helloRun_mem`**, **`helloRun_follows`**, **`helloRun_os`**: the run `helloRun` is a play of
  `hello`, its answers follow `stdoutImpl`, and its OS image is exactly `hiOut ch`.
* **`hello_e2e`**: an x86 runtime of `hello` is `IoSafeN` with `lpsEnv` for "a prefix of the OS
  image of `helloRun`, then `exit 0`".
* The filesystem slice: **`wfRun_mem`**, **`wfRun_follows`** (the run of `writeFile` against
  `fsImpl`) and **`wfRun_fs`**: replayed on an LPS file system without `out.txt`, its answers
  leave `out.txt` containing `hi` (`lookup_set_self`).

**Assumed** (hypotheses): the code obligations of `WriteStub`/`HelloRt`. No program meets them
(`Silmaril.Wasi.Runtime.writeStub_empty`), so these results are vacuous. Their invariant form
(`Silmaril.Wasi.Runtime.HelloLoop`) is met by a concrete program (`Silmaril.Wasi.Runtime.Thms`). The filesystem slice stops at the LPS file-system state:
`lpsEnv` has no `openat`/file `write`/`close` arms, so no `IoSafeN` statement is made for it.
-/
