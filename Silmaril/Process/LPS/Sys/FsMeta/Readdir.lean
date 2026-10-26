module

public import Silmaril.Process.LPS.Uaccess

/-!
# LPS in Lean: `getdents64` (`Sys/Fs/Readdir.v`)

Translation of LPS `Sys/Fs/Readdir.v` (upstream commit `f1006fe8`), the specification of
Linux `fs/readdir.c`: `getdents64` (asm-generic 61, x86-64 217).

The success arm (the listing) is `unmodeled`: `FdDir` does not say which directory it names,
`Fs` holds no `d_ino`/`d_type`/`d_off`, and the key set is not the directory. What is
modeled is the side that writes nothing, in the kernel's order: a closed descriptor is
`EBADF` (`fdget_pos`); every non-directory is `ENOTDIR` (no `.iterate_shared`, the first test
of `iterate_dir`); on a directory, a buffer too small for any entry (`ctx->count`, the low 32
bits read as a signed `int`, below 24) is `filldir64`'s `EINVAL` or the injectable `ENOENT`
of a removed directory. The buffer pointer is not an argument: no admitted arm touches it.

## x86-64

`struct linux_dirent64` (`include/linux/dirent.h`) has no architecture-dependent member, so
x86-64 217 is the same specification.

x86-64 also has the legacy `getdents` (78, `SYSCALL_DEFINE3(getdents)`), which asm-generic
does not define, so LPS has no arm for it. It fills `struct linux_dirent` (`fs/readdir.c`:
`unsigned long d_ino; unsigned long d_off; unsigned short d_reclen; char d_name[]`, with the
type byte stored after the name's NUL), whose record length is
`ALIGN(offsetof(struct linux_dirent, d_name) + namlen + 2, sizeof(long))`. With
`offsetof(…, d_name) = 18` and a name of at least one byte this is at least
`ALIGN(21, 8) = 24`, the same floor as `linux_dirent64`'s `ALIGN(19 + 1 + 1, 8) = 24`. Its
order is the same (`fdget_pos`'s `EBADF`, `iterate_dir`'s `ENOTDIR` and `ENOENT`, then
`filldir`'s `EINVAL` on `reclen > count` with a signed `int` count, before the buffer is
touched), so `getdentsSpecX86` is `getdents64Spec`; the difference in the record layout is
only visible on the success arm, which neither models. musl on x86-64 maps `SYS_getdents` to
`SYS_getdents64` (`src/internal/syscall.h`), so 78 is not what musl's `readdir` reaches.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Fs/Readdir.v:34` `getdents64_errnos`: `IS_DEADDIR`'s `ENOENT`, decided in
`iterate_dir` before `.iterate_shared` runs. -/
def getdents64Errnos : List Int := [ENOENT]

/-- LPS `Sys/Fs/Readdir.v:56` `dirent64_min_reclen`: the smallest `linux_dirent64` record,
`ALIGN(19 + 1 + 1, 8)`. -/
def dirent64MinReclen : Int := 24

/-- LPS `Sys/Fs/Readdir.v:75` `getdents64_ctx_count`: `unsigned int count` stored into the
`int ctx.count`, i.e. the low 32 bits read as two's complement. -/
def getdents64CtxCount (count : Word) : Int := sint32 count

/-- LPS `Sys/Fs/Readdir.v:79` `getdents64_no_room`: too small for the first entry, whatever
it is. -/
def getdents64NoRoom (count : Word) : Bool := decide (getdents64CtxCount count < dirent64MinReclen)

/-- LPS `Sys/Fs/Readdir.v:218` `getdents64_spec`. The match on `FdEntry` is total, as in
LPS. -/
def getdents64Spec (fd count : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.channel _) => errRet ENOTDIR
  | some (.file _ _) => errRet ENOTDIR
  | some (.fileW _ _) => errRet ENOTDIR
  | some (.fileA _ _) => errRet ENOTDIR
  | some (.fileRW _ _) => errRet ENOTDIR
  | some (.pipe _ _) => errRet ENOTDIR
  | some (.socket _) => errRet ENOTDIR
  | some (.devNull _ _) => errRet ENOTDIR
  | some .urandom => errRet ENOTDIR
  | some .dir =>
    if getdents64NoRoom count then
      Sys.alt (Sys.bind (errnoFrom getdents64Errnos) errRet) (errRet EINVAL)
    else unmodeled

/-- x86-64: offset of `d_name` in the legacy `struct linux_dirent` (`fs/readdir.c`). -/
def direntDNameOffX86 : Nat := 18

/-- x86-64: the smallest legacy `linux_dirent` record,
`ALIGN(offsetof(struct linux_dirent, d_name) + 1 + 2, sizeof(long))`. -/
def direntMinReclenX86 : Int := ((direntDNameOffX86 + 1 + 2 + 7) / 8 * 8 : Nat)

/-- The legacy floor is the `linux_dirent64` floor. -/
theorem direntMinReclenX86_eq : direntMinReclenX86 = dirent64MinReclen := by decide

/-- x86-64 `getdents` (78). Not in LPS (asm-generic has no `getdents`). Its non-success arms
are `getdents64`'s, LPS `Sys/Fs/Readdir.v:218` `getdents64_spec` (see the module docstring):
the record floor is the same 24 bytes (`direntMinReclenX86_eq`). -/
def getdentsSpecX86 (fd count : Word) : Sys SyscallEffect := getdents64Spec fd count

end Silmaril.Process.LPS
