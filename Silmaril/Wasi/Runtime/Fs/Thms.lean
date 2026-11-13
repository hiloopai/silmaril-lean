module

public import Silmaril.Wasi.Runtime.Fs.Defs
public import Silmaril.Proofs.Wasi.Runtime.Fs.Image

/-!
# A concrete x86 runtime of `writeFile`: theorems (header)

Part D of `docs/projects/wasm-wasi.md`. PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Runtime.Fs.*`,
namespace `Silmaril.Wasi.Runtime.Fs`). The program `fsCode` (`Silmaril.Wasi.Runtime.Fs.Defs`) writes
`hi` to descriptor `3`, closes it and exits `0`, on the open machine `Open.step`.

* `movRax_step` … `movRdi_step`, `fs_resume`, `fs_toWrite`, `fs_written`, `fs_closed`: its runs
  between `syscall`s, one listing-law step (`Open.step_of_listed`, `decide`d decodings, `simp` on
  `Ext.exec`) per instruction. Every state is an `fsSt`, so the trap states `fsWriteSt`,
  `fsCloseSt`, `fsExitSt` are reached exactly, for every flag choice of LPS.
* `fs_writeSource`: the readable source of the `write` is exactly `hi`.
* **`redirectImg`**: the program is a `RedirectRt Open.step segs 3` for every segment list.
  **`redirectRt_exists`**: the frozen `Task.redirectRt_exists` of `Silmaril.Wasi.Os` holds, so the
  `RedirectRt` results there are not vacuous.
* **`redirectImg_ioSafe`**, **`redirectImg_e2e`**: `IoSafeN` with the sound `fsEnv`, for
  `redirAllowed` and for "nothing, or `exit 0` with the OS image of `writeFile`'s WASI run
  against `fsImpl`", from every model whose descriptor `3` is a write-only `out.txt` at offset
  `0` with `out.txt` empty.
* **`redirectImg_psafe`**, **`redirectImg_psafe8`**: LPS process-safe on every native machine
  agreeing with `Open.step`, and on the bridge's release machine `x86WithFlagOracle8` for every
  flag oracle.

**Not proved here**: the program is hand-written, not compiled from the component; the launch
state `fsStart` is not shown to be an `X86Launch` state of an ELF image (its memory has no stack
and its own two mappings), so the process-safety theorems take an aligned configuration as a
hypothesis; and the parent's `openat` (the redirection) is outside the program.
-/
