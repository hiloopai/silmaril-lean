module

public import Silmaril.Wasi.Os.Defs
public import Silmaril.Process.LPS.Sys.FsIo.Open
public import Silmaril.Process.LPS.Sys.Kernel

/-!
# The filesystem slice of WASI over `IoSpec`: `openat`, file `write` and `close` arms

Part D of `docs/projects/wasm-wasi.md`, the filesystem slice. `Silmaril.Machine.Process.IoSpec`'s `lpsEnv` answers
`exit`, `write` to a live channel and `read` from stdin. A WASI host serving
`wasi:filesystem` needs three more syscalls, so this module adds three LPS arms (without
changing `IoSpec`):

* **`openCreateArm segs`**: `openat(AT_FDCWD, path, O_WRONLY|O_CREAT|O_TRUNC)` (modulo
  `O_CLOEXEC|O_LARGEFILE|O_NONBLOCK`) on a plain name (non-empty, no `/`, not `.`/`..`, not a
  directory prefix of a file), with the path read as a C string. LPS (`openat_spec`,
  `create_wronly`) answers an injected `ENOMEM`/`EACCES`/`EMFILE`/`ENFILE` with the model
  unchanged, or creates the file empty (truncating it) and binds the lowest free descriptor to
  it write-only at offset `0` (`createModel`). The pathname copy-in is recorded (`openEff`).
* **`writeFileArm segs`**: `write(fd, buf, n)` on a descriptor `fileW p off` whose file exists,
  with a modelled range, a nonzero count, a non-empty readable source and a modelled gap. LPS
  (`write_file_with`) writes the *whole* readable source at `off` (`Fs.fileWrite`), advances the
  offset (`writeFileModel`) and returns its length. No event is emitted.
* **`closeArm segs`**: `close(fd)` on a bound descriptor: the entry is removed, `0` returned.

`fsArms segs = lpsArms segs ++ [writeFileArm, closeArm]` and `fsEnv segs = ofArms (fsArms segs)`;
both new arms are proved sound against LPS's native x86-64 table of the bridge (`spec`), so
`fsEnv` is `Sound` (`Silmaril.Wasi.Os.Fs.Thms`). `allArms`/`fsEnvO` add `openCreateArm`. Every
outcome of LPS's reference `openat_spec` is one of its answers, but it is **not** sound for the
bridge's table: number 257 is still pending there (`openat` is not a reviewed name of
`NativeX86.table`), so `spec` answers it `unmodeled`. The refutation is proved.

## Runtimes of `writeFile`

The code obligations of x86 runtimes of the WASI component `writeFile` (counterparts of
`HelloRt`), all hypotheses:

* `WriteTail c segs fd`: from a `write` of `hi` to `fd`, then its `close`, then `exit(0)`.
* `WriteFileRt c segs e`: from `start`, an `openat` of `out.txt` (`outPath`) for writing; on
  success the tail on the returned descriptor (the lowest free one); `exit(1)` on an injected
  error. It is `IoSafeN` with `fsEnvO`, but it reaches `PSafeF` only once `openat` is reviewed.
* `RedirectRt c segs fd`: launched with `out.txt` already open on `fd` (a shell redirection
  `fd> out.txt`, that is, the parent's `openat`), it runs to the tail. It is `IoSafeN` with the
  sound `fsEnv` and therefore LPS process-safe. Frozen target `Task.redirectRt_exists`, proved
  by a concrete program in `Silmaril.Wasi.Runtime.Fs`.

The traces allowed: `wfAllowed fs0` (nothing yet, `exit 0` with `wfFs fs0`, or `exit 1` with
`fs0`) and `redirAllowed fs0` (nothing yet, or `exit 0` with `tailFs fs0`). LPS observes the
file system only in the exit event; `wfFs`/`tailFs` are the OS image `fsOs` of `writeFile`'s
WASI run `wfRun` against `fsImpl` when `out.txt` is absent/empty.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Os

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasi.Examples (hiBytes)

/-! ## The arms -/

/-- The descriptor argument of the request at `s`. -/
abbrev reqFd (segs : List Segment) (s : X86State) : Word := fd32 ((reqOf segs s).arg 0)

/-- The pathname of the `openat` request at `s`, read as a C string. -/
abbrev reqPath (segs : List Segment) (s : X86State) : CstrResult :=
  readCstr (reqOf segs s).mem ((reqOf segs s).arg 1)

/-- The pathname copy-in that LPS records for `openat` at `s`. -/
def openCopy (segs : List Segment) (s : X86State) : List (Word × Nat) :=
  [((reqOf segs s).arg 1, cstrAccessLenAux (reqOf segs s).mem ((reqOf segs s).arg 1) pathMax)]

/-- The effect of `openat` at `s` returning `r`. -/
def openEff (segs : List Segment) (s : X86State) (r : Word) : SyscallEffect :=
  (mkEffect r [] []).withCopyins (openCopy segs s ++ [])

/-- The model after `openat` creates `p` (empty) and binds `fd` to it write-only. -/
def createModel (e : Silmaril.Process.LPS.Model) (p : Fs.Path) (fd : Word) :
    Silmaril.Process.LPS.Model :=
  (e.withFs (Fs.set e.fs p [])).withFds (fdInsert e.fds fd (.fileW p 0))

/-- **`openat(AT_FDCWD, p, O_WRONLY|O_CREAT|O_TRUNC)` on a plain name.** -/
def openCreateArm (segs : List Segment) : Arm where
  Handles s e :=
    (reqOf segs s).sysno.toNat = 257 ∧ openResidue ((reqOf segs s).arg 2) = wrCreateFlags ∧
    (reqFd segs s == AT_FDCWD32) = true ∧
    ∃ p, reqPath segs s = .ok p ∧ Fs.pathEqb p [] = false ∧ pathHasSlash p = false ∧
      pathIsDirref p = false ∧ fsUnder e.fs p = false
  out s e o :=
    ∃ p, reqPath segs s = .ok p ∧
      ((∃ err ∈ openatErrnos, o = .resume (resume s (openEff segs s (errnoRet err))) e []) ∨
       (fdLookup e.fds (allocFd e.fds) = none ∧
        o = .resume (resume s (openEff segs s (allocFd e.fds))) (createModel e p (allocFd e.fds))
          []))

/-- The effect of writing `bs` to a file at `s`. -/
def fileWEff (segs : List Segment) (s : X86State) (bs : List Byte) : SyscallEffect :=
  (mkEffect (lenWord bs) [] []).withCopyins ([((reqOf segs s).arg 1, bs.length)] ++ [])

/-- The model after writing `bs` at `off` to the file `p` (contents `data`) through `fd`. -/
def writeFileModel (e : Silmaril.Process.LPS.Model) (fd : Word) (p : Fs.Path) (off : Word)
    (data bs : List Byte) : Silmaril.Process.LPS.Model :=
  (e.withFs (Fs.set e.fs p (Fs.fileWrite data off bs))).withFds
    (fdInsert e.fds fd (.fileW p (off + lenWord bs)))

/-- The readable source of the `write` request at `s`. -/
abbrev reqSource (segs : List Segment) (s : X86State) : List Byte :=
  writeSource (reqOf segs s).mem ((reqOf segs s).arg 1) ((reqOf segs s).arg 2)

/-- **`write(fd, buf, n)` to a write-only file.** -/
def writeFileArm (segs : List Segment) : Arm where
  Handles s e :=
    (reqOf segs s).sysno.toNat = 1 ∧
    ∃ p off data, fdLookup e.fds (reqFd segs s) = some (.fileW p off) ∧
      Fs.lookup e.fs p = some data ∧
      modeledRwRangeWith accessOkb ((reqOf segs s).arg 1) ((reqOf segs s).arg 2) = true ∧
      wIs0 ((reqOf segs s).arg 2) = false ∧ reqSource segs s ≠ [] ∧
      modeledFileGap data off (reqSource segs s) = true
  out s e o :=
    ∃ p off data, fdLookup e.fds (reqFd segs s) = some (.fileW p off) ∧
      Fs.lookup e.fs p = some data ∧
      o = .resume (resume s (fileWEff segs s (reqSource segs s)))
        (writeFileModel e (reqFd segs s) p off data (reqSource segs s)) []

/-- **`close(fd)` on a bound descriptor.** -/
def closeArm (segs : List Segment) : Arm where
  Handles s e := (reqOf segs s).sysno.toNat = 3 ∧ (fdLookup e.fds (reqFd segs s)).isSome
  out s e o := o = .resume (resume s (mkEffect 0 [] [])) (e.withFds (fdRemove e.fds (reqFd segs s))) []

/-- The arms of `lpsEnv`, file `write` and `close`. -/
def fsArms (segs : List Segment) : List Arm := lpsArms segs ++ [writeFileArm segs, closeArm segs]

/-- **The LPS environment with file `write` and `close`** (sound: `sound_fsEnv`). -/
def fsEnv (segs : List Segment) : SysEnv := ofArms (fsArms segs)

/-- The arms of `fsEnv` and `openat`. -/
def allArms (segs : List Segment) : List Arm := fsArms segs ++ [openCreateArm segs]

/-- **The LPS environment with `openat`, file `write` and `close`.** It answers `openat` as
LPS's reference `openat_spec` does; it is not sound for the bridge's native table, where
`openat` is still pending (`openCreate_unmodeled`). -/
def fsEnvO (segs : List Segment) : SysEnv := ofArms (allArms segs)

/-! ## Runtimes of `writeFile` -/

/-- **The code obligations of the tail of a `writeFile` runtime**, once descriptor `fd` is open
on `out.txt`: a `write` of `hi` to `fd`, its `close`, then `exit(0)`. -/
structure WriteTail (c : MState → Option MState) (segs : List Segment) (fd : Word) where
  /-- The `write` trap. -/
  writeSt : MState
  /-- At a `syscall`. -/
  writeTrap : AtSyscall writeSt
  /-- Number `1`. -/
  writeNo : ∀ k, (reqAt segs writeSt k).sysno.toNat = 1
  /-- To the descriptor `fd`. -/
  writeFd : ∀ k, fd32 ((reqAt segs writeSt k).arg 0) = fd
  /-- A modelled range. -/
  writeRange : ∀ k,
    modeledRwRangeWith accessOkb ((reqAt segs writeSt k).arg 1) ((reqAt segs writeSt k).arg 2) = true
  /-- A nonzero count. -/
  writeCount : ∀ k, wIs0 ((reqAt segs writeSt k).arg 2) = false
  /-- The bytes are `hi`. -/
  writeBytes : ∀ k, reqSource segs (trapAt writeSt k) = hiBytes
  /-- The `close` trap. -/
  closeSt : MState
  /-- After the write it runs without syscalls to the `close`. -/
  written : ∀ k n, SafeN c (fun m => m = closeSt) n
    (resume (trapAt writeSt k) (fileWEff segs (trapAt writeSt k) hiBytes))
  /-- At a `syscall`. -/
  closeTrap : AtSyscall closeSt
  /-- Number `3`. -/
  closeNo : ∀ k, (reqAt segs closeSt k).sysno.toNat = 3
  /-- Of the descriptor `fd`. -/
  closeFd : ∀ k, fd32 ((reqAt segs closeSt k).arg 0) = fd
  /-- The `exit` trap. -/
  exitSt : MState
  /-- After the `close` it runs without syscalls to the `exit`. -/
  closed : ∀ k n, SafeN c (fun m => m = exitSt) n (resume (trapAt closeSt k) (mkEffect 0 [] []))
  /-- At a `syscall`. -/
  exitTrap : AtSyscall exitSt
  /-- Number `60`. -/
  exitNo : (exitSt.core.read .rax).toNat = 60
  /-- Status `0`. -/
  exitCode : exitSt.core.read .rdi &&& 255 = 0

/-- **An x86 runtime of `writeFile` that opens `out.txt` itself**, on the LPS model `e`:
`openat(AT_FDCWD, "out.txt", O_WRONLY|O_CREAT|O_TRUNC)`, then the tail on the returned
descriptor (the lowest free one); `exit(1)` on an injected `openat` error. -/
structure WriteFileRt (c : MState → Option MState) (segs : List Segment)
    (e : Silmaril.Process.LPS.Model) extends WriteTail c segs (allocFd e.fds) where
  /-- The launch state. -/
  start : MState
  /-- The `openat` trap. -/
  openSt : MState
  /-- It runs without syscalls to the `openat`. -/
  toOpen : ∀ n, SafeN c (fun m => m = openSt) n start
  /-- At a `syscall`. -/
  openTrap : AtSyscall openSt
  /-- Number `257`. -/
  openNo : ∀ k, (reqAt segs openSt k).sysno.toNat = 257
  /-- Relative to the working directory. -/
  openDir : ∀ k, (fd32 ((reqAt segs openSt k).arg 0) == AT_FDCWD32) = true
  /-- `O_WRONLY|O_CREAT|O_TRUNC`. -/
  openFlags : ∀ k, openResidue ((reqAt segs openSt k).arg 2) = wrCreateFlags
  /-- The path is `out.txt`. -/
  openPath : ∀ k, reqPath segs (trapAt openSt k) = .ok outPath
  /-- After a successful `openat` it runs without syscalls to the `write`. -/
  opened : ∀ k n, SafeN c (fun m => m = writeSt) n
    (resume (trapAt openSt k) (openEff segs (trapAt openSt k) (allocFd e.fds)))
  /-- The error `exit` trap. -/
  failSt : MState
  /-- After an injected `openat` error it runs without syscalls to the error `exit`. -/
  failed : ∀ k err, err ∈ openatErrnos → ∀ n, SafeN c (fun m => m = failSt) n
    (resume (trapAt openSt k) (openEff segs (trapAt openSt k) (errnoRet err)))
  /-- At a `syscall`. -/
  failTrap : AtSyscall failSt
  /-- Number `60`. -/
  failNo : (failSt.core.read .rax).toNat = 60
  /-- Status `1`. -/
  failCode : failSt.core.read .rdi &&& 255 = 1

/-- **An x86 runtime of `writeFile` launched with `out.txt` already open** on descriptor `fd`
(as by a shell redirection `fd> out.txt`, which is the `openat` above done by the parent): it
runs without syscalls to the tail. -/
structure RedirectRt (c : MState → Option MState) (segs : List Segment) (fd : Word)
    extends WriteTail c segs fd where
  /-- The launch state. -/
  start : MState
  /-- It runs without syscalls to the `write`. -/
  toWrite : ∀ n, SafeN c (fun m => m = writeSt) n start

/-- **Frozen target** (proved: `Silmaril.Wasi.Runtime.Fs.redirectRt_exists`): an x86 runtime of `writeFile` launched with
`out.txt` open exists on a machine extending the `Ext8` open machine, so that `RedirectRt` is
not vacuous. -/
def Task.redirectRt_exists : Prop :=
  ∃ (c : MState → Option MState) (segs : List Segment) (fd : Word),
    Silmaril.Machine.X86.Safe.Refines Silmaril.Machine.X86.Open.step c ∧ Nonempty (RedirectRt c segs fd)

/-- The file system after the tail on a file system where `out.txt` is empty. -/
def tailFs (fs : Fs.FileSystem) : Fs.FileSystem := Fs.set fs outPath (Fs.fileWrite [] 0 hiBytes)

/-- The file system after `writeFile`'s runtime succeeds on `fs0`: `out.txt` created empty
(truncated), then `hi` written at offset `0`. -/
def wfFs (fs0 : Fs.FileSystem) : Fs.FileSystem := tailFs (Fs.set fs0 outPath [])

/-- The traces of `writeFile`'s runtime from `fs0`: nothing yet, `exit 0` with `out.txt`
written, or `exit 1` after an `openat` error with the file system unchanged. -/
def wfAllowed (fs0 : Fs.FileSystem) (tr : List Event) : Prop :=
  tr = [] ∨ tr = [.exitEv 0 (wfFs fs0)] ∨ tr = [.exitEv 1 fs0]

/-- The traces of the redirected runtime from `fs0`: nothing yet, or `exit 0` with `hi`
written to `out.txt`. -/
def redirAllowed (fs0 : Fs.FileSystem) (tr : List Event) : Prop :=
  tr = [] ∨ tr = [.exitEv 0 (tailFs fs0)]

end Silmaril.Wasi.Os
