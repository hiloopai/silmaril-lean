module

public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Sys.FsMeta.DPath
public import Silmaril.Process.LPS.Sys.FsMeta.Namei
public import Silmaril.Process.LPS.Sys.FsMeta.Stat
public import Silmaril.Process.LPS.Sys.FsMeta.Readdir

/-!
# LPS in Lean: file-system metadata syscalls (paths, stat, readdir, readlink, unlink, getcwd)

The arms of LPS `Sys/Fs/DPath.v`, `Sys/Fs/Namei.v`, `Sys/Fs/Stat.v` and `Sys/Fs/Readdir.v`
(upstream commit `f1006fe8`), as rows of a syscall table. Argument narrowings follow LPS
`Sys/SyscallTable.v:42-70` (`fd32` on descriptors and dirfds, `flag32` on `newfstatat`'s
flag word).

| syscall | asm-generic (LPS) | x86-64 | x86-64 specification |
| --- | ---: | ---: | --- |
| `getcwd` | 17 | 79 | the same |
| `unlinkat` | 35 | 263 | the same |
| `getdents64` | 61 | 217 | the same |
| `readlinkat` | 78 | 267 | the same |
| `newfstatat` | 79 | 262 | the same (no arm writes the buffer) |
| `fstat` | 80 | 5 | the 144-byte x86-64 `struct stat`, x86-64 `access_ok` |
| `stat` | — | 4 | `newfstatat(AT_FDCWD, path, buf, 0)` |
| `lstat` | — | 6 | `newfstatat(AT_FDCWD, path, buf, AT_SYMLINK_NOFOLLOW)` |
| `getdents` | — | 78 | `getdents64`'s non-success arms (same 24-byte record floor) |
| `rmdir` | — | 84 | `unlinkat(AT_FDCWD, path, AT_REMOVEDIR)` |
| `unlink` | — | 87 | `unlinkat(AT_FDCWD, path, 0)` |
| `readlink` | — | 89 | `readlinkat(AT_FDCWD, …)` |

The rows marked — are x86-64 legacy entry points that asm-generic does not define; each is a
one-line wrapper in the kernel around the `*at` function the LPS arm specifies.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- The file-system metadata arms of the LPS table (LPS `Sys/SyscallTable.v:42,52,58,68-70`),
at the asm-generic numbers. -/
def fsMetaLpsArms : List SpecArm :=
  [ arm 17 "getcwd" (fun i => getcwdSpec (i.arg 1)),
    arm 35 "unlinkat" (fun i => unlinkatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 61 "getdents64" (fun i => getdents64Spec (fd32 (i.arg 0)) (i.arg 2)),
    arm 78 "readlinkat" (fun i => readlinkatSpec (fd32 (i.arg 0))),
    arm 79 "newfstatat" (fun i => newfstatatSpec (fd32 (i.arg 0)) (i.arg 1) (flag32 (i.arg 3))),
    arm 80 "fstat" (fun i => fstatSpec (fd32 (i.arg 0)) (i.arg 1)) ]

/-- The file-system metadata arms at the native x86-64 numbers
(`arch/x86/entry/syscalls/syscall_64.tbl`), with the x86-64 `struct stat` on `fstat` and the
legacy entry points `stat`, `lstat`, `getdents`, `rmdir`, `unlink` and `readlink`. -/
def fsMetaX86Arms : List SpecArm :=
  [ arm 79 "getcwd" (fun i => getcwdSpec (i.arg 1)),
    arm 263 "unlinkat" (fun i => unlinkatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 217 "getdents64" (fun i => getdents64Spec (fd32 (i.arg 0)) (i.arg 2)),
    arm 267 "readlinkat" (fun i => readlinkatSpec (fd32 (i.arg 0))),
    arm 262 "newfstatat" (fun i => newfstatatSpec (fd32 (i.arg 0)) (i.arg 1) (flag32 (i.arg 3))),
    arm 5 "fstat" (fun i => fstatSpecX86 (fd32 (i.arg 0)) (i.arg 1)),
    arm 4 "stat" (fun i => statSpecX86 (i.arg 0)),
    arm 6 "lstat" (fun i => lstatSpecX86 (i.arg 0)),
    arm 78 "getdents" (fun i => getdentsSpecX86 (fd32 (i.arg 0)) (i.arg 2)),
    arm 84 "rmdir" (fun i => rmdirSpecX86 (i.arg 0)),
    arm 87 "unlink" (fun i => unlinkSpecX86 (i.arg 0)),
    arm 89 "readlink" (fun _ => readlinkSpecX86) ]

end Silmaril.Process.LPS
