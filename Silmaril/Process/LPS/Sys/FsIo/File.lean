module

public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess

/-!
# LPS in Lean: the descriptor table, `dup` and `dup3`

Translation of LPS `Sys/Fs/File.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/file.c`:

* `lowest_fd`: the lowest free descriptor, a singleton choice;
* `dup_modeled_entry`: duplication is modeled exactly for the kinds that carry no
  per-description state (channels, directories, `/dev/null`, `/dev/urandom`) and declines
  (`unmodeled`) for files, sockets and pipe ends, whose offset, receive script or end count a
  copied entry would split;
* `dup_spec`: `EBADF` first, then the injected `ENOMEM`/`EMFILE` beside the lowest free fd;
* `dup3_spec`: `EINVAL` for flags other than `O_CLOEXEC` and for `oldfd = newfd`, `EBADF` at
  or above `RLIMIT_NOFILE`, `EBADF` for a closed `oldfd`, then the install; a free `newfd` at
  or above `NR_OPEN_DEFAULT` is `unmodeled` (`expand_files` depends on `max_fds` and
  `sysctl_nr_open`, which the model does not carry).

## x86-64

`dup` (32) and `dup3` (292) are the same specifications. x86-64 also has the legacy `dup2`
(33), which LPS's asm-generic table lacks; `dup2Spec` is derived from `SYSCALL_DEFINE2(dup2)`
(`fs/file.c`): for `oldfd = newfd` it answers `newfd` when `oldfd` is open and `EBADF`
otherwise, and in every other case it is `ksys_dup3(oldfd, newfd, 0)`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- `Z.ldiff` (`a & ~b`) on non-negative integers. -/
def zldiff (a b : Int) : Int := ((a.toNat ^^^ (a.toNat &&& b.toNat) : Nat) : Int)

/-- LPS `Sys/Fs/File.v:29` `lowest_fd`: the lowest free descriptor. -/
def lowestFd (fds : List (Word × FdEntry)) : Sys Word :=
  Sys.choose fun fd => fdLookup fds fd = none ∧ fd = allocFd fds

/-- LPS `Sys/Fs/File.v:81` `dup_modeled_entry`: the kinds whose duplication copying the entry
models exactly. -/
def dupModeledEntry : FdEntry → Bool
  | .channel _ | .dir => true
  | .file _ _ | .fileW _ _ | .socket _ => false
  | .fileA _ _ => false
  | .fileRW _ _ => false
  | .pipe _ _ => false
  | .devNull _ _ => true
  | .urandom => true

/-- LPS `Sys/Fs/File.v:166` `dup_errnos`. -/
def dupErrnos : List Int := [ENOMEM, EMFILE]

/-- LPS `Sys/Fs/File.v:184` `dup_spec`. -/
def dupSpec (oldfd : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds oldfd with
  | none => errRet EBADF
  | some e =>
    if !dupModeledEntry e then unmodeled
    else
      Sys.alt (do let er ← errnoFrom dupErrnos; errRet er)
        (do
          let fd ← lowestFd m.fds
          modify (·.withFds (fdInsert m.fds fd e))
          retOnly fd)

/-- LPS `Sys/Fs/File.v:207` `dup3_flags_ok`: `(flags & ~O_CLOEXEC) == 0` on the `int`. -/
def dup3FlagsOk (flags : Word) : Bool := zldiff (uns (flag32 flags)) O_CLOEXEC == 0

/-- LPS `Sys/Fs/File.v:301` `dup3_newfd_under_limit`: `newfd < RLIMIT_NOFILE`. -/
def dup3NewfdUnderLimit (newfd : Word) (m : Model) : Bool := decide (uns newfd < uns m.nofile)

/-- LPS `Sys/Fs/File.v:304` `dup3_spec`. -/
def dup3Spec (oldfd newfd flags : Word) : Sys SyscallEffect := do
  let m ← getModel
  if !dup3FlagsOk flags then errRet EINVAL
  else if oldfd == newfd then errRet EINVAL
  else if !dup3NewfdUnderLimit newfd m then errRet EBADF
  else match fdLookup m.fds oldfd with
    | none => errRet EBADF
    | some e =>
      if !dupModeledEntry e then unmodeled
      else match fdLookup m.fds newfd with
        | none =>
          if uns newfd < NR_OPEN_DEFAULT then do
            modify (·.withFds (fdInsert m.fds newfd e))
            retOnly newfd
          else unmodeled
        | some _ => do
          modify (·.withFds (fdInsert m.fds newfd e))
          retOnly newfd

/-- x86-64 `dup2` (number 33; not in LPS's asm-generic table), from `SYSCALL_DEFINE2(dup2)`
(`fs/file.c`): `oldfd = newfd` answers `newfd` when it is open and `EBADF` otherwise, without
the `RLIMIT_NOFILE` test; any other pair is `ksys_dup3(oldfd, newfd, 0)`, which is LPS
`dup3_spec` with zero flags (`Sys/Fs/File.v:304`). -/
def dup2SpecX86 (oldfd newfd : Word) : Sys SyscallEffect := do
  let m ← getModel
  if oldfd == newfd then
    match fdLookup m.fds oldfd with
    | none => errRet EBADF
    | some _ => retOnly newfd
  else dup3Spec oldfd newfd 0

end Silmaril.Process.LPS
