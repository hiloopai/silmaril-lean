module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.Sys.FsIo.Namei

/-!
# LPS in Lean: the path walk and `unlinkat` (`Sys/Fs/Namei.v`)

Translation of LPS `Sys/Fs/Namei.v` (upstream commit `f1006fe8`), the specification of
Linux `fs/namei.c`: the pathname helpers the path-taking syscalls share (`..`, the separator,
trailing-separator stripping, the implied-directory test `fs_under`, the `/tmp/<name>` gate
`tmp_name`, the open-descriptor guard `fd_names_path`) and `unlinkat` (asm-generic 35,
x86-64 263).

The model's file system is a flat map from uninterpreted paths to contents. `unlinkat`
types the last component the way `link_path_walk` does (`LAST_ROOT`, `LAST_DOT`,
`LAST_DOTDOT` are answered without a file system), answers an ordinary name in the working
directory off the map (`ENOENT` when absent, the removal otherwise, with the injectable
`unlinkat_errnos`), answers `/tmp/<name>` off the run's private `/tmp`, and declines every
other spelling with a separator (the walk needs a directory tree the map does not have),
names over `NAME_MAX` (the file system's own `ENAMETOOLONG`), implied directories in the
working directory, and a path an open descriptor still names.

## x86-64

`SYSCALL_DEFINE3(unlinkat)`, `do_unlinkat` and `do_rmdir` are generic code: x86-64 263 is the
same specification as asm-generic 35. x86-64 additionally has the legacy entry points
`unlink` (87) and `rmdir` (84), which asm-generic does not define, so LPS has no arm for
them. Both are one line in `fs/namei.c`:

```
SYSCALL_DEFINE1(unlink, const char __user *, pathname)
{ return do_unlinkat(AT_FDCWD, getname(pathname)); }
SYSCALL_DEFINE1(rmdir, const char __user *, pathname)
{ return do_rmdir(AT_FDCWD, getname(pathname)); }
```

so they are `unlinkat`'s body at `AT_FDCWD` with the flag word fixed to `0` and
`AT_REMOVEDIR`, under the same pathname copy-in ledger and without the flag test (there is no
flag word). See `unlinkSpecX86` and `rmdirSpecX86`. musl on x86-64 issues `SYS_unlink` and
`SYS_rmdir` for `unlink()` and `rmdir()` (`src/unistd/unlink.c`, `src/unistd/rmdir.c`,
`#ifdef SYS_unlink`), so these are the numbers an x86-64 binary actually reaches.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys
open Fs (Path FileSystem)

/-! ## Path constants and helpers

The pathname helpers of `Sys/Fs/Namei.v:32-200` (`dotdot_path`, `slash_byte`,
`path_has_slash`, trailing-separator stripping, `dir_prefixb`, `fs_under`,
`path_strip_prefix`, `tmp_name` and their lemmas) are in `Sys/FsIo/Namei`, shared with the
file-I/O family and `Run`. -/

/-- LPS `Sys/Fs/Namei.v:223` `fd_names_path`: a file descriptor names the path `p`. The
non-file entries are enumerated (no catch-all), as in LPS, so a new `FdEntry` constructor is
a compile error here. -/
def fdNamesPath : List (Word × FdEntry) → Path → Bool
  | [], _ => false
  | (_, .file q _) :: r, p => Fs.pathEqb p q || fdNamesPath r p
  | (_, .fileW q _) :: r, p => Fs.pathEqb p q || fdNamesPath r p
  | (_, .fileA q _) :: r, p => Fs.pathEqb p q || fdNamesPath r p
  | (_, .fileRW q _) :: r, p => Fs.pathEqb p q || fdNamesPath r p
  | (_, .channel _) :: r, p => fdNamesPath r p
  | (_, .dir) :: r, p => fdNamesPath r p
  | (_, .socket _) :: r, p => fdNamesPath r p
  | (_, .pipe _ _) :: r, p => fdNamesPath r p
  | (_, .devNull _ _) :: r, p => fdNamesPath r p
  | (_, .urandom) :: r, p => fdNamesPath r p

/-! ## `unlinkat` -/

/-- LPS `Sys/Fs/Namei.v:257` `unlinkat_errnos`: the untracked environment failures of
`may_delete` / `vfs_unlink` / `mnt_want_write` (`ENOMEM`, `EACCES`, `EPERM`, `EROFS`,
`EBUSY`). `ENOENT` is not injectable: existence is tracked. -/
def unlinkatErrnos : List Int := [ENOMEM, EACCES, EPERM, EROFS, EBUSY]

/-- LPS `Sys/Fs/Namei.v:263` `modeled_unlink_flags`: `0` and `AT_REMOVEDIR`, every word the
kernel accepts (`(flag & ~AT_REMOVEDIR) != 0` is the kernel's own `EINVAL`). -/
def modeledUnlinkFlags (flags : Word) : Bool :=
  uns (flag32 flags) == 0 || uns (flag32 flags) == AT_REMOVEDIR

/-- LPS `Sys/Fs/Namei.v:268` `unlink_rmdir`: `do_rmdir` rather than `do_unlinkat`. -/
def unlinkRmdir (flags : Word) : Bool := uns (flag32 flags) == AT_REMOVEDIR

/-- LPS `Sys/Fs/Namei.v:281` `unlink_found_spec`: the removal once the key `c` is found (`p`
is the pathname as spelled). A model file is never a directory, so `rmdir` is `ENOTDIR`; a
trailing separator is `do_unlinkat`'s `slashes:` `ENOTDIR`; a path an open descriptor names
is declined; otherwise an injected failure or the removal. -/
def unlinkFoundSpec (p c : Path) (flags : Word) (m : Model) : Sys SyscallEffect :=
  if unlinkRmdir flags then errRet ENOTDIR
  else if pathTrailingSlash p then errRet ENOTDIR
  else if fdNamesPath m.fds c then unmodeled
  else Sys.alt (Sys.bind (errnoFrom unlinkatErrnos) errRet)
    (Sys.bind (modify (·.withFs (Fs.remove m.fs c))) fun _ => retOnly 0)

/-- LPS `Sys/Fs/Namei.v:397` `unlinkat_tmp_spec`: removing `/tmp/<n>` from the run's private
`/tmp`. `AT_REMOVEDIR` and over-long names are declined; an implied directory is
`may_delete`'s `EISDIR` (tested before the lookup); a name the run does not hold is
`ENOENT`. -/
def unlinkatTmpSpec (n p c : Path) (flags : Word) (m : Model) : Sys SyscallEffect :=
  if unlinkRmdir flags then unmodeled
  else if NAME_MAX < n.length then unmodeled
  else if fsUnder m.fs c then errRet EISDIR
  else match Fs.lookup m.fs c with
    | none => errRet ENOENT
    | some _ => unlinkFoundSpec p c flags m

/-- LPS `Sys/Fs/Namei.v:709` `unlinkat_body_spec`: `getname()`'s three answers, the empty
path's `ENOENT`, then the dirfd (only `AT_FDCWD` is modeled), then the type of the last
component:

| last component | `flags = 0` | `AT_REMOVEDIR` |
| --- | --- | --- |
| none (`LAST_ROOT`) | `EISDIR` | `EBUSY` |
| `.` | `EISDIR` | `EINVAL` |
| `..` | `EISDIR` | `ENOTEMPTY` |

and for an ordinary name the `/tmp` arm, the separator decline, the `NAME_MAX` and implied
directory declines, then the lookup. -/
def unlinkatBodySpec (dirfd pathp flags : Word) (i : SyscallInput) (m : Model) :
    Sys SyscallEffect :=
  match readCstr i.mem pathp with
  | .tooLong => errRet ENAMETOOLONG
  | .fault => errRet EFAULT
  | .ok p =>
    if Fs.pathEqb p [] then errRet ENOENT
    else if !(dirfd == AT_FDCWD32) then unmodeled
    else
      let c := pathStripTrailingSlashes p
      if Fs.pathEqb c [] then (if unlinkRmdir flags then errRet EBUSY else errRet EISDIR)
      else if pathHasSlash c then
        match tmpName c with
        | some n => unlinkatTmpSpec n p c flags m
        | none => unmodeled
      else if Fs.pathEqb c dotPath then
        (if unlinkRmdir flags then errRet EINVAL else errRet EISDIR)
      else if Fs.pathEqb c dotdotPath then
        (if unlinkRmdir flags then errRet ENOTEMPTY else errRet EISDIR)
      else if NAME_MAX < c.length then unmodeled
      else if fsUnder m.fs c then unmodeled
      else match Fs.lookup m.fs c with
        | none => errRet ENOENT
        | some _ => unlinkFoundSpec p c flags m

/-- LPS `Sys/Fs/Namei.v:751` `unlinkat_spec`: the flag word first (a real `EINVAL`, before
`getname()`, so no copy-in is recorded on it), then the body under the pathname copy-in
ledger. -/
def unlinkatSpec (dirfd pathp flags : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !modeledUnlinkFlags flags then errRet EINVAL
  else
    recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
      (unlinkatBodySpec dirfd pathp flags i m)

/-! ## x86-64 legacy entry points -/

/-- x86-64 `unlink` (87, `fs/namei.c` `SYSCALL_DEFINE1(unlink)`):
`do_unlinkat(AT_FDCWD, getname(pathname))`. Not in LPS (asm-generic has no `unlink`); it is
LPS `Sys/Fs/Namei.v:751` `unlinkat_spec` at `AT_FDCWD` with flag word `0`, which passes the
flag test, so the flag test is vacuous (`unlinkSpecX86_eq`). -/
def unlinkSpecX86 (pathp : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
    (unlinkatBodySpec AT_FDCWD32 pathp 0 i m)

/-- x86-64 `rmdir` (84, `fs/namei.c` `SYSCALL_DEFINE1(rmdir)`):
`do_rmdir(AT_FDCWD, getname(pathname))`. Not in LPS; it is LPS `Sys/Fs/Namei.v:751`
`unlinkat_spec` at `AT_FDCWD` with flag word `AT_REMOVEDIR` (`rmdirSpecX86_eq`). -/
def rmdirSpecX86 (pathp : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
    (unlinkatBodySpec AT_FDCWD32 pathp (zw AT_REMOVEDIR) i m)

/-- `unlink(p)` is `unlinkat(AT_FDCWD, p, 0)`. -/
theorem unlinkSpecX86_eq (pathp : Word) : unlinkSpecX86 pathp = unlinkatSpec AT_FDCWD32 pathp 0 := by
  have : modeledUnlinkFlags 0 = true := by decide
  unfold unlinkSpecX86 unlinkatSpec
  rw [this]
  rfl

/-- `rmdir(p)` is `unlinkat(AT_FDCWD, p, AT_REMOVEDIR)`. -/
theorem rmdirSpecX86_eq (pathp : Word) :
    rmdirSpecX86 pathp = unlinkatSpec AT_FDCWD32 pathp (zw AT_REMOVEDIR) := by
  have : modeledUnlinkFlags (zw AT_REMOVEDIR) = true := by decide
  unfold rmdirSpecX86 unlinkatSpec
  rw [this]
  rfl

end Silmaril.Process.LPS
