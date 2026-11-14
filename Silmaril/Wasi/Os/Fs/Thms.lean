module

public import Silmaril.Wasi.Os.Fs.Defs
public import Silmaril.Proofs.Wasi.Os.Fs.Arms
public import Silmaril.Proofs.Wasi.Os.Fs.Run

/-!
# The filesystem slice of WASI over `IoSpec`: theorems (header)

Part D of `docs/projects/wasm-wasi.md`. PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Os.Fs.*`,
namespace `Silmaril.Wasi.Os`).

**The arms** (`Arms`), against `spec`, LPS's native x86-64 table of the bridge:

* **`write_fileW_iff`**, **`close_iff`**: closed forms of LPS `write_spec` on a `fileW`
  descriptor (the whole readable source is written at the offset, no event, never
  `unmodeled`) and of `close_spec` on a bound descriptor.
* **`armSound_writeFile`**, **`armSound_close`**, **`sound_fsEnv`**:
  `Sound (fsEnv segs) segs refused`, for every segment list and refusal filter.
* `openat`: **`openat_create_iff`** (closed form of LPS's reference `openat_spec` on a plain
  name with `O_WRONLY|O_CREAT|O_TRUNC`), **`openCreate_spec`** and
  **`openCreate_spec_modeled`** (every outcome of `openat_spec` is an answer of `openCreateArm`, and
  `openat_spec` is never `unmodeled` there).
* **Refuted**: `openat` is not sound for the bridge's table. Number 257 is still *pending* in
  `NativeX86.table` (`openat` is not a reviewed name), so `spec` answers it `unmodeled`
  (`openat_pending`, `openCreate_unmodeled`, `not_armSound_openCreate`).

**The runtimes** (`Run`):

* `tail_write`: the tail of a runtime (`write` of `hi`, `close`, `exit 0`) is `IoSafeN` from a
  model where its descriptor is a `fileW` on an empty `out.txt`.
* **`redirectRt_ioSafe`**, **`redirectRt_psafe`**: a runtime launched with `out.txt` open
  (`RedirectRt`) is `IoSafeN` with the sound `fsEnv` for `redirAllowed`, and LPS process-safe
  (`PSafeF`) on every agreeing native machine (through `ioSafe_psafe` and `sound_fsEnv`).
* **`writeFileRt_ioSafe`**: a runtime that opens `out.txt` itself (`WriteFileRt`) is `IoSafeN`
  with `fsEnvO` for `wfAllowed` (success with `out.txt` holding `hi`, or `exit 1` after an
  injected `openat` error). **`writeFileRt_not_sound`** (refutation): on a live model such a
  runtime makes `fsEnvO` unsound for the bridge's table, so no `PSafeF` follows from it.
* The WASI side: **`fsOs_wfRun_absent`**, **`fsOs_wfRun_empty`**: the OS image `fsOs` of
  `writeFile`'s run against `fsImpl` (`wfRun`) is `wfFs` without `out.txt`, `tailFs` with an
  empty `out.txt`.
* **`redirect_e2e`**, **`writeFile_e2e`**: the exit event's file system is that OS image.

**Assumed** (hypotheses, not proved): the code obligations of `WriteTail`, `RedirectRt` and
`WriteFileRt`. A concrete x86 program meets `RedirectRt` (`Task.redirectRt_exists` is proved in
`Silmaril.Wasi.Runtime.Fs.Thms`); none is given for `WriteFileRt`.
-/
