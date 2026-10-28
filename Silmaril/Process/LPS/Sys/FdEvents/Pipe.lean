module

public import Silmaril.Process.LPS.Sys.FdEvents.Common

/-!
# LPS in Lean: `pipe2` (and x86-64 `pipe`)

Translation of LPS `Sys/Fs/Pipe.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/pipe.c` `do_pipe2`. The pipe *state* (`PipeBuf`, `pipe_write_room`, `pipe_append`, …) is
in `State`; the transfers on a pipe are `read`/`write` (`Sys/ReadWrite`). This module creates
the pipe:

* flags first: a bit outside `O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE` is
  `EINVAL` before the user pointer is touched; any accepted non-zero flag is `unmodeled`;
* then the two descriptors, read end first, each the lowest free number;
* then one `copy_to_user` of `int fildes[2]`: refused by `access_ok` or wholly unwritable is
  `EFAULT` with nothing installed, a writable prefix with an unwritable tail is `unmodeled`;
* `EMFILE`, `ENFILE` and `ENOMEM` are injected failures beside every answer past the flags.

## x86-64

`pipe2SpecWith` is parametric in the ABI; the only x86-64 difference in `do_pipe2` itself is
`access_ok` (`FdEventsAbi.x86`). The flag values are the same (`asm/fcntl.h` is the generic
header on x86-64). x86-64 also has the legacy `pipe` (number 22), which riscv64 lacks:
`SYSCALL_DEFINE1(pipe, int __user *, fildes)` is `do_pipe2(fildes, 0)` (`fs/pipe.c`), so
`pipeSpecX86 fildes = pipe2SpecX86 fildes 0` exactly. musl's `pipe()` issues it on x86-64.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys FdEvents

/-- LPS `Sys/Fs/Pipe.v:28` `pipe2_flags_mask`: `O_CLOEXEC | O_NONBLOCK | O_DIRECT |
O_NOTIFICATION_PIPE` (the last spelled `O_EXCL`). -/
def pipe2FlagsMask : Int := O_CLOEXEC + O_NONBLOCK + O_DIRECT + O_EXCL

/-- LPS `Sys/Fs/Pipe.v:41` `pipe2_errnos`: the injectable failures. -/
def pipe2Errnos : List Int := [EMFILE, ENFILE, ENOMEM]

/-- LPS `Sys/Fs/Pipe.v:160` `pipe2_spec`, parametric in the ABI's `access_ok`. `flags`
arrives narrowed to 32 bits (`pipeFlags32`). -/
def pipe2SpecWith (abi : FdEventsAbi) (fildes flags : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !(zldiff (uns flags) pipe2FlagsMask == 0) then errRet EINVAL
  else if !wIs0 flags then unmodeled
  else
    let id := pipeNewId m.pipes
    match pipeLookup m.pipes id with
    | some _ => unmodeled
    | none =>
      let injected : Sys SyscallEffect := do
        let e ← errnoFrom pipe2Errnos
        errRet e
      if !abi.accessOk fildes 8 then Sys.alt injected (errRet EFAULT)
      else match readBytesMap i.wmem fildes 8 with
        | some _ =>
          Sys.alt injected do
            let fdr ← lowestFd m.fds
            let fds1 := fdInsert m.fds fdr (.pipe id false)
            let fdw ← lowestFd fds1
            setFds (fdInsert fds1 fdw (.pipe id true))
            setPipes (pipeInsert m.pipes id ([], 0))
            Sys.pure (mkEffect 0 [(fildes, pipeFdBytes fdr fdw)] [])
        | none =>
          match readBytesMap i.wmem fildes 1 with
          | none => Sys.alt injected (errRet EFAULT)
          | some _ => unmodeled

/-- LPS `Sys/Fs/Pipe.v:160` `pipe2_spec` (riscv64 `access_ok`). -/
def pipe2Spec (fildes flags : Word) : Sys SyscallEffect := pipe2SpecWith .lps fildes flags

/-- x86-64 `pipe2` (number 293): LPS `pipe2_spec` with x86-64 `access_ok`. -/
def pipe2SpecX86 (fildes flags : Word) : Sys SyscallEffect := pipe2SpecWith .x86 fildes flags

/-- x86-64 `pipe` (number 22, no riscv64 counterpart): `do_pipe2(fildes, 0)`. -/
def pipeSpecX86 (fildes : Word) : Sys SyscallEffect := pipe2SpecX86 fildes 0

end Silmaril.Process.LPS
