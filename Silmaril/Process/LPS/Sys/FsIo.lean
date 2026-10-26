module

public import Silmaril.Process.LPS.Sys.FsIo.ReadWrite
public import Silmaril.Process.LPS.Sys.FsIo.Open
public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Arm

/-!
# LPS in Lean: the file-I/O family's syscall arms

The arms of LPS `Sys/Fs/ReadWrite.v`, `Sys/Fs/File.v` and `Sys/Fs/Open.v` (upstream commit
`f1006fe8`), with the argument narrowings of `Sys/SyscallTable.v:47-131`:

* `fsIoLpsArms`: asm-generic (riscv64) numbers, exactly LPS's rows;
* `fsIoX86Arms`: native x86-64 numbers (`arch/x86/entry/syscalls/syscall_64.tbl`). The rows
  that read user memory through `access_ok` (`read`, `write`, `pread64`, `pwrite64`,
  `readv`, `writev`) use the x86-64 `access_ok`; the others are LPS's specifications
  unchanged. The x86-64 legacy entry points `open` (2), `access` (21), `dup2` (33) and
  `creat` (85), which the asm-generic table lacks, are fixed instances of `openat`,
  `faccessat` and `dup3` (see `Sys/FsIo/Open` and `Sys/FsIo/File`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- The file-I/O arms of LPS `Sys/SyscallTable.v:47-131`, at the asm-generic numbers. -/
def fsIoLpsArms : List SpecArm :=
  [ arm 23 "dup" (fun i => dupSpec (fd32 (i.arg 0))),
    arm 24 "dup3" (fun i => dup3Spec (fd32 (i.arg 0)) (fd32 (i.arg 1)) (i.arg 2)),
    arm 46 "ftruncate" (fun i => ftruncateSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 48 "faccessat" (fun i => faccessatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 56 "openat" (fun i => openatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 57 "close" (fun i => closeSpec (fd32 (i.arg 0))),
    arm 62 "lseek" (fun i => lseekSpec (fd32 (i.arg 0)) (i.arg 1) (whence32 (i.arg 2))),
    arm 63 "read" (fun i => readSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 64 "write" (fun i => writeSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 65 "readv" (fun i => readvSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 66 "writev" (fun i => writevSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 67 "pread64" (fun i => pread64Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 68 "pwrite64" (fun i => pwrite64Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 439 "faccessat2"
      (fun i => faccessat2Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)) ]

/-- The file-I/O arms at the native x86-64 numbers. -/
def fsIoX86Arms : List SpecArm :=
  [ arm 0 "read" (fun i => readSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 1 "write" (fun i => writeSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 2 "open" (fun i => openSpecX86 (i.arg 0) (i.arg 1)),
    arm 3 "close" (fun i => closeSpec (fd32 (i.arg 0))),
    arm 8 "lseek" (fun i => lseekSpec (fd32 (i.arg 0)) (i.arg 1) (whence32 (i.arg 2))),
    arm 17 "pread64"
      (fun i => pread64SpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 18 "pwrite64"
      (fun i => pwrite64SpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 19 "readv" (fun i => readvSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 20 "writev" (fun i => writevSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 21 "access" (fun i => accessSpecX86 (i.arg 0) (i.arg 1)),
    arm 32 "dup" (fun i => dupSpec (fd32 (i.arg 0))),
    arm 33 "dup2" (fun i => dup2SpecX86 (fd32 (i.arg 0)) (fd32 (i.arg 1))),
    arm 77 "ftruncate" (fun i => ftruncateSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 85 "creat" (fun i => creatSpecX86 (i.arg 0)),
    arm 257 "openat" (fun i => openatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 269 "faccessat" (fun i => faccessatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 292 "dup3" (fun i => dup3Spec (fd32 (i.arg 0)) (fd32 (i.arg 1)) (i.arg 2)),
    arm 439 "faccessat2"
      (fun i => faccessat2Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)) ]

theorem fsIoLpsArms_nodup : (armNumbers fsIoLpsArms).Nodup := by decide

theorem fsIoX86Arms_nodup : (armNumbers fsIoX86Arms).Nodup := by decide

end Silmaril.Process.LPS
