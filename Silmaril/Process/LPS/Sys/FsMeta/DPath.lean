module

public import Silmaril.Process.LPS.Syscall

/-!
# LPS in Lean: `getcwd` (`Sys/Fs/DPath.v`)

Translation of LPS `Sys/Fs/DPath.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/d_path.c`: `getcwd` (asm-generic 17, x86-64 79).

The model has no working directory (`Model` has no pwd field and `Fs` is a flat map with no
root and no directories), so every outcome that would carry the directory string is
`unmodeled`. What is answered is the band `size ≤ 1`, where the length `len ≥ 2` the kernel
compares against `size` exceeds it for every possible working directory: `ERANGE`, or one of
the three injectable errnos decided before the size comparison (`ENOMEM` from `__getname`,
`ENOENT` for an unlinked working directory, `ENAMETOOLONG` for a path over `PATH_MAX`). The
buffer is not an argument: the kernel neither probes nor writes it before the `ERANGE`
(`getcwd(NULL, 0)` is `-ERANGE`).

## x86-64

`SYSCALL_DEFINE2(getcwd)` and the `prepend*` helpers are generic code, so x86-64 79 is the
same specification. The one architecture-dependent step of LPS's argument is that no dentry
name reaches `2^31` bytes, which rests on `KMALLOC_MAX_SIZE = 2^(MAX_PAGE_ORDER + PAGE_SHIFT)`
being far below it. On x86-64, `MAX_PAGE_ORDER` is 10 (`include/linux/mmzone.h`, the default
when `CONFIG_ARCH_FORCE_MAX_ORDER` is unset, and x86 does not set it) and `PAGE_SHIFT` is 12,
so `KMALLOC_MAX_SIZE` is 4 MiB, as on riscv64, and the argument holds unchanged.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Fs/DPath.v:46` `getcwd_errnos`: the failures decided before the size comparison,
on state the model does not carry. `EFAULT` is absent: it can only follow the comparison. -/
def getcwdErrnos : List Int := [ENOMEM, ENOENT, ENAMETOOLONG]

/-- LPS `Sys/Fs/DPath.v:150` `getcwd_spec`: for `size > 1` the working directory would decide
the answer, so the model declines; for `size ≤ 1` the answer is `ERANGE` or an injected
failure, offered as an `alt` (exactly one applies in a run, decided by state the model does
not carry). -/
def getcwdSpec (size : Word) : Sys SyscallEffect :=
  if 1 < uns size then unmodeled
  else Sys.alt (Sys.bind (errnoFrom getcwdErrnos) errRet) (errRet ERANGE)

end Silmaril.Process.LPS
