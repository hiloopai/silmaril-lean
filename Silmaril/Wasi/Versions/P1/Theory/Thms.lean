module

public import Silmaril.Wasi.Versions.P1.Theory.Defs
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# WASI preview1: checks of the signature, and the loose host

* The tables generated from the vendored witx have the expected shape: 46 functions, 77
  `errno`s, and the core signatures of the functions most used by `wasi-libc`
  (`coreSig_fd_write`, `coreSig_path_open`, `coreSig_clock_time_get`, …).
* The named `errno` constants are the tags of their witx names (`errno_consts`).
* The adapter's `error-code → errno` table (`Gen.errnoOfCode`) has one nonzero, valid
  `errno` per `error-code` case (`errnoOfCode_ok`).
* `loose_sat`: the loose host of the preview1 theory satisfies it (from `Silmaril.Wasi.Host`).
-/

namespace Silmaril.Wasi.Versions.P1

open Silmaril.Wasi Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

/-- The witx file has 46 functions and 77 error codes. -/
theorem counts : fnNames.length = 46 ∧ Gen.errnoNames.length = 77 ∧
    Gen.errorCodeNames.length = 37 ∧ Gen.errnoOfCode.length = 37 := by decide

/-- `fd_write : (i32 fd, i32 iovs, i32 iovs_len, i32 nwritten) → i32`. -/
theorem coreSig_fd_write :
    coreParams "fd_write" = [.i32, .i32, .i32, .i32] ∧ coreResults "fd_write" = [.i32] := by
  decide

/-- `fd_read : (i32 fd, i32 iovs, i32 iovs_len, i32 nread) → i32`. -/
theorem coreSig_fd_read :
    coreParams "fd_read" = [.i32, .i32, .i32, .i32] ∧ coreResults "fd_read" = [.i32] := by
  decide

/-- `path_open : (i32 fd, i32 dirflags, i32 path, i32 path_len, i32 oflags, i64 base,
i64 inheriting, i32 fdflags, i32 opened) → i32`. -/
theorem coreSig_path_open :
    coreParams "path_open" = [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32] ∧
      coreResults "path_open" = [.i32] := by
  decide

/-- `clock_time_get : (i32 id, i64 precision, i32 time) → i32`. -/
theorem coreSig_clock_time_get :
    coreParams "clock_time_get" = [.i32, .i64, .i32] ∧ coreResults "clock_time_get" = [.i32] := by
  decide

/-- `proc_exit : (i32 rval) → ()`. -/
theorem coreSig_proc_exit : coreParams "proc_exit" = [.i32] ∧ coreResults "proc_exit" = [] := by
  decide

/-- `args_sizes_get : (i32 argc, i32 argv_buf_size) → i32`. -/
theorem coreSig_args_sizes_get :
    coreParams "args_sizes_get" = [.i32, .i32] ∧ coreResults "args_sizes_get" = [.i32] := by
  decide

/-- `poll_oneoff : (i32 in, i32 out, i32 nsubscriptions, i32 nevents) → i32`. -/
theorem coreSig_poll_oneoff :
    coreParams "poll_oneoff" = [.i32, .i32, .i32, .i32] ∧ coreResults "poll_oneoff" = [.i32] := by
  decide

/-- The named `errno` constants are the tags of their witx names. -/
theorem errno_consts : errno "badf" = eBadf ∧ errno "inval" = eInval ∧ errno "io" = eIo ∧
    errno "nomem" = eNomem ∧ errno "nosys" = eNosys ∧ errno "notdir" = eNotdir ∧
    errno "notsup" = eNotsup ∧ errno "overflow" = eOverflow ∧ errno "success" = 0 := by
  decide

/-- The clock ids. -/
theorem clock_consts : Gen.clockNames.idxOf "realtime" = clockRealtime.toNat ∧
    Gen.clockNames.idxOf "monotonic" = clockMonotonic.toNat := by
  decide

/-- The descriptor functions of the slice. -/
theorem fdFns_slice : "fd_write" ∈ fdFns ∧ "fd_read" ∈ fdFns ∧ "fd_close" ∈ fdFns ∧
    "path_open" ∈ fdFns ∧ "fd_renumber" ∈ fdFns ∧ "clock_time_get" ∉ fdFns ∧
    "random_get" ∉ fdFns ∧ "path_symlink" ∉ fdFns := by
  decide

/-- Every entry of the adapter's `error-code → errno` table is a nonzero `errno`. -/
theorem errnoOfCode_ok : ∀ e ∈ Gen.errnoOfCode, e ≠ 0 ∧ e < Gen.errnoNames.length := by
  decide

/-- **The loose preview1 host satisfies the preview1 theory.** -/
theorem loose_sat {Y : Sig.{0}} : (hostSat th.Accepts).holds (loose (Y := Y) (I := imports) th) :=
  Silmaril.Wasi.loose_sat th

end Silmaril.Wasi.Versions.P1
