module

public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.Sys.FsIo.Open

/-!
# LPS in Lean: `fcntl`, `flock`, `ioctl`, `fsync` and `fdatasync`

Translation of LPS (upstream commit `f1006fe8`):

* `Sys/Fs/Fcntl.v` (Linux `fs/fcntl.c`): `fcntl_spec` answers exactly three commands.
  `F_SETFD` is `0` for any argument (the close-on-exec bit it sets has no modeled reader);
  `F_SETFL` is `0` when it provably changes nothing (`setfl_noop_on`); `F_GETFL` answers
  `O_RDWR` on a socket and is `unmodeled` on every other kind (`getfl_f_flags`). Every other
  command (`F_GETFD`, `F_DUPFD`, `F_DUPFD_CLOEXEC`, the record locks, owner, lease, notify,
  pipe-size and seal commands) and every `F_SETFL` that would change something is
  `unmodeled`. A descriptor that is not open is `EBADF` before the command is examined.
* `Sys/Fs/Locks.v` (`fs/locks.c`): `flock_spec`. `LOCK_MAND` is a successful no-op decided
  before the descriptor; an unknown operation is `EINVAL`, also before the descriptor; an
  unlock is `0`; a lock is `0` on a regular file that no other descriptor names, and
  `unmodeled` otherwise.
* `Sys/Fs/Ioctl.v` (`fs/ioctl.c`): `ioctl_spec` answers the eight terminal-only requests of
  `tty_only_request` with `ENOTTY` on every open descriptor except `/dev/urandom`, and is
  `unmodeled` on every other request.
* `Sys/Fs/Sync.v` (`fs/sync.c`): `fsync_spec`, shared by `fsync` and `fdatasync`: `0` on
  files and directories, `EINVAL` on kinds without `.fsync`.

None of these specifications offers an injected failure (`errnoFrom`): LPS commits to their
answers absolutely (no LSM, no allocation failure), and so does this translation.

## x86-64

The specifications are the same on x86-64; only the syscall numbers differ (`ioctl` 16,
`fcntl` 72, `flock` 73, `fsync` 74, `fdatasync` 75, from
`arch/x86/entry/syscalls/syscall_64.tbl`). Checked against the x86-64 uapi headers
(`arch/x86/include/uapi/asm/{fcntl,ioctl,ioctls,termbits,termios}.h` are each a bare
`#include <asm-generic/…>`):

* the `F_*`, `FD_CLOEXEC`, `O_*`, `FASYNC` and `LOCK_*` values are the asm-generic ones;
* the ioctl request numbers are the asm-generic `ioctls.h` ones, and `_IOR`/`_IOW` encode
  with the asm-generic `ioctl.h` layout (`_IOC_SIZEBITS = 14`, `_IOC_DIRBITS = 2`,
  `_IOC_READ = 2`, `_IOC_WRITE = 1`), so `TIOCGPTN = 0x80045430` and `TIOCSPTLCK =
  0x40045431` as on riscv64. `struct termios` is the asm-generic layout too, but no arm here
  reads or writes it (`ENOTTY` writes nothing);
* the narrowing of the `unsigned int` arguments (`fd32`, `cmd32`): x86-64 also selects
  `ARCH_HAS_SYSCALL_WRAPPER`, and its `__SYSCALL_DEFINEx` (`arch/x86/include/asm/
  syscall_wrapper.h`) casts each register with `__SC_CAST` as riscv64 does;
* `force_o_largefile()` holds on x86-64 (no `CONFIG_ARCH_32BIT_OFF_T`), so the reasoning of
  `getfl_f_flags` about `O_LARGEFILE` carries over.

So `fsCtlX86Arms` reuses the LPS specifications under the native numbers.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! The `Sys/Fs/Open.v` flag words used by the `F_SETFL` remarks below (`wrCreateFlags`,
`isExclCreate`, `rdwrOpenWord`, `isRdwrExclCreate`, `openIgnoredFlags`, …) are those of
`Sys/FsIo/Open`. -/

/-! ## `fcntl` (LPS `Sys/Fs/Fcntl.v`) -/

/-- LPS `Sys/Fs/Fcntl.v:78` `setfl_acted_on`: the five status bits `setfl` reads
(`O_APPEND`, `O_NONBLOCK`, `FASYNC`, `O_DIRECT`, `O_NOATIME`). -/
def setflActedOn : Int := O_APPEND + O_NONBLOCK + FASYNC + O_DIRECT + O_NOATIME

/-- LPS `Sys/Fs/Fcntl.v:174` `setfl_noop_on`: an `F_SETFL` provably changes nothing. The
argument must name none of `setflActedOn`, and the descriptor must be one whose current
flags carry neither `O_APPEND` nor `FASYNC`: a file, read-write file, directory or socket the
model opened. Channels (flags chosen by the environment), append descriptors, the two
character devices and pipe ends decline. Enumerated, as in LPS. -/
def setflNoopOn (e : FdEntry) (arg : Word) : Bool :=
  match e with
  | .channel _ => false
  | .file _ _ | .fileW _ _ | .fileRW _ _ | .dir | .socket _ => zland (uns arg) setflActedOn == 0
  | .fileA _ _ => false
  | .devNull _ _ => false
  | .urandom => false
  | .pipe _ _ => false

/-- LPS `Sys/Fs/Fcntl.v:288` `modeled_open_flags_clear_of_setfl`: the residue of every
admitted open word except the append one is disjoint from `setflActedOn`. -/
theorem modeled_open_flags_clear_of_setfl (fl : Int)
    (h : fl = 0 ∨ fl = wrCreateFlags ∨ isExclCreate fl = true ∨ fl = O_DIRECTORY ∨
      rdwrOpenWord fl = true ∨ isRdwrExclCreate fl = true) :
    zland fl setflActedOn = 0 := by
  simp only [isExclCreate, rdwrOpenWord, isRdwrExclCreate, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h | (h | h) | h | (((h | h) | h) | h) | (h | h) <;> subst h <;> decide

/-- LPS `Sys/Fs/Fcntl.v:315` `open_ignored_flags_clear_of_setfl_current`. -/
theorem open_ignored_flags_clear_of_setfl_current :
    zland openIgnoredFlags (O_APPEND + FASYNC) = 0 := by decide

/-- LPS `Sys/Fs/Fcntl.v:324` `setfl_acted_on_fits_32`: masking commutes with the kernel's
`int argi = (int)arg`. -/
theorem setfl_acted_on_fits_32 : setflActedOn < 2 ^ 32 := by decide

/-- LPS `Sys/Fs/Fcntl.v:387` `socket_f_flags`: a socket's whole `f_flags` is `O_RDWR`
(`sock_alloc_file`; `SOCK_NONBLOCK` is declined by `socket` and `accept4`). -/
def socketFFlags : Int := O_RDWR

/-- LPS `Sys/Fs/Fcntl.v:417` `socket_f_flags_clear_of_setfl`. -/
theorem socket_f_flags_clear_of_setfl : zland socketFFlags setflActedOn = 0 := by decide

/-- LPS `Sys/Fs/Fcntl.v:483` `getfl_f_flags`: what `F_GETFL` answers, where the model can
derive `filp->f_flags` exactly: only on a socket. Enumerated, as in LPS. -/
def getflFFlags (e : FdEntry) : Option Word :=
  match e with
  | .socket _ => some (zw socketFFlags)
  | .channel _ | .file _ _ | .fileW _ _ | .dir => none
  | .fileRW _ _ => none
  | .fileA _ _ => none
  | .devNull _ _ => none
  | .urandom => none
  | .pipe _ _ => none

/-- LPS `Sys/Fs/Fcntl.v:750` `fcntl_spec`: `EBADF` before the command; `F_SETFD` is `0` for
any argument; a provably empty `F_SETFL` is `0`; `F_GETFL` answers where `getflFFlags`
derives the word; everything else is `unmodeled`. -/
def fcntlSpec (fd cmd arg : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some e =>
    if cmd == F_SETFD then retOnly 0
    else if cmd == F_SETFL && setflNoopOn e arg then retOnly 0
    else if cmd == F_GETFL then
      match getflFFlags e with
      | some fl => retOnly fl
      | none => unmodeled
    else unmodeled

/-! ## `flock` (LPS `Sys/Fs/Locks.v`) -/

/-- LPS `Sys/Fs/Locks.v:36` `flock_mand_b`: `cmd & LOCK_MAND`, tested first. -/
def flockMandB (cmd : Word) : Bool := zland (uns cmd) LOCK_MAND != 0

/-- LPS `Sys/Fs/Locks.v:46` `flock_base`: `cmd & ~LOCK_NB` (`Z.ldiff`). -/
def flockBase (cmd : Word) : Int := uns cmd - zland (uns cmd) LOCK_NB

/-- LPS `Sys/Fs/Locks.v:53` `flock_cmd_ok_b`: the operations `flock_translate_cmd` maps. -/
def flockCmdOkB (cmd : Word) : Bool :=
  let b := flockBase cmd
  b == LOCK_SH || b == LOCK_EX || b == LOCK_UN

/-- LPS `Sys/Fs/Locks.v:60` `flock_unlock_b`. -/
def flockUnlockB (cmd : Word) : Bool := flockBase cmd == LOCK_UN

/-- LPS `Sys/Fs/Locks.v:77` `path_openers`: how many descriptors name the path `p`.
Enumerated, as in LPS. -/
def pathOpeners : List (Word × FdEntry) → Fs.Path → Nat
  | [], _ => 0
  | (_, .file q _) :: r, p => (if Fs.pathEqb q p then 1 else 0) + pathOpeners r p
  | (_, .fileW q _) :: r, p => (if Fs.pathEqb q p then 1 else 0) + pathOpeners r p
  | (_, .fileA q _) :: r, p => (if Fs.pathEqb q p then 1 else 0) + pathOpeners r p
  | (_, .fileRW q _) :: r, p => (if Fs.pathEqb q p then 1 else 0) + pathOpeners r p
  | (_, .channel _) :: r, p => pathOpeners r p
  | (_, .dir) :: r, p => pathOpeners r p
  | (_, .socket _) :: r, p => pathOpeners r p
  | (_, .pipe _ _) :: r, p => pathOpeners r p
  | (_, .devNull _ _) :: r, p => pathOpeners r p
  | (_, .urandom) :: r, p => pathOpeners r p

/-- LPS `Sys/Fs/Locks.v:95` `flock_sole_opener`. -/
def flockSoleOpener (fds : List (Word × FdEntry)) (p : Fs.Path) : Bool :=
  pathOpeners fds p == 1

/-- The lock arms of LPS `Sys/Fs/Locks.v:275-309` (`FdFile`, `FdFileW`, `FdFileA`,
`FdFileRW`): `0` when no other descriptor names the path, `unmodeled` otherwise. -/
def flockSoleOpenerArm (fds : List (Word × FdEntry)) (p : Fs.Path) : Sys SyscallEffect :=
  if flockSoleOpener fds p then retOnly 0 else unmodeled

/-- LPS `Sys/Fs/Locks.v:260` `flock_spec`: `LOCK_MAND` is `0` and an unknown operation is
`EINVAL`, both before the descriptor; then `EBADF`; an unlock is `0`; a lock is `0` on a
regular file with no other opener and `unmodeled` otherwise. -/
def flockSpec (fd cmd : Word) : Sys SyscallEffect := do
  let m ← getModel
  if flockMandB cmd then retOnly 0
  else if !flockCmdOkB cmd then errRet EINVAL
  else match fdLookup m.fds fd with
    | none => errRet EBADF
    | some e =>
      if flockUnlockB cmd then retOnly 0
      else match e with
        | .file p _ => flockSoleOpenerArm m.fds p
        | .fileW p _ => flockSoleOpenerArm m.fds p
        | .fileA p _ => flockSoleOpenerArm m.fds p
        | .fileRW p _ => flockSoleOpenerArm m.fds p
        | .channel _ => unmodeled
        | .dir => unmodeled
        | .socket _ => unmodeled
        | .pipe _ _ => unmodeled
        | .devNull _ _ => unmodeled
        | .urandom => unmodeled

/-! ## `ioctl` (LPS `Sys/Fs/Ioctl.v`) -/

/-- LPS `Sys/Fs/Ioctl.v:127` `tty_only_request`: the eight requests only a terminal
implements. -/
def ttyOnlyRequest (req : Word) : Bool :=
  req == TCGETS || req == TCSETS || req == TIOCSCTTY ||
  req == TIOCGWINSZ || req == TIOCSWINSZ || req == TIOCNOTTY ||
  req == TIOCGPTN || req == TIOCSPTLCK

/-- LPS `Sys/Fs/Ioctl.v:187` `ioctl_spec`: `EBADF` before the request; `ENOTTY` for a
terminal-only request on every open kind except `/dev/urandom`, which declines every
request; every other request is `unmodeled`. Enumerated, as in LPS. -/
def ioctlSpec (fd req : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.channel _) | some (.file _ _) | some (.fileW _ _) | some (.fileA _ _)
  | some (.fileRW _ _) | some .dir | some (.socket _) | some (.pipe _ _)
  | some (.devNull _ _) =>
    if ttyOnlyRequest req then errRet ENOTTY else unmodeled
  | some .urandom => unmodeled

/-! ## `fsync` and `fdatasync` (LPS `Sys/Fs/Sync.v`) -/

/-- LPS `Sys/Fs/Sync.v:215` `fsync_spec`, shared by `fsync` and `fdatasync`: `EBADF`, then
`EINVAL` on kinds whose file operations have no `.fsync` (channels, sockets, pipes,
`/dev/null`, `/dev/urandom`) and `0` on files and directories. Enumerated, as in LPS. -/
def fsyncSpec (fd : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.channel _) => errRet EINVAL
  | some (.socket _) => errRet EINVAL
  | some (.pipe _ _) => errRet EINVAL
  | some (.devNull _ _) => errRet EINVAL
  | some .urandom => errRet EINVAL
  | some (.file _ _) => retOnly 0
  | some (.fileW _ _) => retOnly 0
  | some (.fileA _ _) => retOnly 0
  | some (.fileRW _ _) => retOnly 0
  | some .dir => retOnly 0

/-! ## Arms -/

/-- The arms of this family under the given numbers for `ioctl`, `fcntl`, `flock`, `fsync`
and `fdatasync`. The argument narrowings are LPS `Sys/SyscallTable.v:49-51,71-72`. -/
def fsCtlArms (ioctlNo fcntlNo flockNo fsyncNo fdatasyncNo : Nat) : List SpecArm :=
  [ arm fcntlNo "fcntl" fun i => fcntlSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1)) (i.arg 2),
    arm ioctlNo "ioctl" fun i => ioctlSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1)),
    arm flockNo "flock" fun i => flockSpec (fd32 (i.arg 0)) (cmd32 (i.arg 1)),
    arm fsyncNo "fsync" fun i => fsyncSpec (fd32 (i.arg 0)),
    arm fdatasyncNo "fdatasync" fun i => fsyncSpec (fd32 (i.arg 0)) ]

/-- The family's arms under the LPS (asm-generic) numbers: LPS `Sys/SyscallTable.v:49`
(`fcntl` 25), `:50` (`ioctl` 29), `:51` (`flock` 32), `:71` (`fsync` 82) and `:72`
(`fdatasync` 83). -/
def fsCtlLpsArms : List SpecArm := fsCtlArms 29 25 32 82 83

/-- The family's arms under the native x86-64 numbers (`syscall_64.tbl`: `ioctl` 16, `fcntl`
72, `flock` 73, `fsync` 74, `fdatasync` 75). The specifications are the LPS ones: no
structure layout or argument order differs on x86-64 (see the module docstring). -/
def fsCtlX86Arms : List SpecArm := fsCtlArms 16 72 73 74 75

end Silmaril.Process.LPS
