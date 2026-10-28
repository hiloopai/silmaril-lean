module

public import Silmaril.Process.LPS.Sys.FsIo.File
public import Silmaril.Process.LPS.Sys.FsIo.Namei
public import Silmaril.Process.LPS.Sys.ReadWrite

/-!
# LPS in Lean: `openat`, `ftruncate`, `faccessat` and `faccessat2`

Translation of LPS `Sys/Fs/Open.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/open.c`; `close_spec` is in `Silmaril.Process.LPS.Sys.Kernel` (audited against
`Open.v:1387`: it is kind-blind and removes the entry, as in LPS).

## `openat`

The full flag lattice of LPS, in its order: `build_open_flags` first (a word outside
`modeled_open_flags` is `unmodeled` before the pathname is fetched), then `getname` (the
three answers `ENAMETOOLONG`, `EFAULT`, the string; the empty string is `ENOENT`), then the
dirfd (only `AT_FDCWD` is modeled), then the path:

* a path without a separator, by flag word (modulo `O_CLOEXEC | O_LARGEFILE | O_NONBLOCK`):
  `O_RDONLY` (file, or a directory fd for `.`/`..`), `O_WRONLY|O_CREAT|O_TRUNC`, the exclusive
  `O_WRONLY|O_CREAT|O_EXCL[|O_TRUNC]`, `O_RDONLY|O_DIRECTORY`, `O_WRONLY|O_CREAT|O_APPEND`, the
  four `O_RDWR[|O_CREAT][|O_TRUNC]` words and `O_RDWR|O_CREAT|O_EXCL[|O_TRUNC]`;
* a path with a separator: `/etc/localtime` (`ENOENT` under a declared assumption),
  `/dev/null`, `/dev/urandom` and `/tmp/<name>`; every other such path is `unmodeled`.

Every arm that can succeed admits the injected `ENOMEM`/`EACCES`/`EMFILE`/`ENFILE` beside the
lowest free descriptor. Every other flag word (`O_NOCTTY`, `O_TMPFILE`, `O_PATH`, `O_NOFOLLOW`,
`O_RDWR|O_APPEND`, `O_WRONLY` without `O_CREAT`, a set high half, …) is `unmodeled`, as in LPS.

## x86-64

None of these specifications consults `access_ok` or a layout, and the `O_*` and `AT_*` values
are the asm-generic ones on x86-64 (`arch/x86/include/uapi/asm/fcntl.h` includes
`asm-generic/fcntl.h`). x86-64 keeps three legacy entry points LPS's table lacks, each a fixed
instance of a translated one (`fs/open.c`): `open(p, f, m)` is `do_sys_open(AT_FDCWD, p, f, m)`,
`creat(p, m)` is `do_sys_open(AT_FDCWD, p, O_CREAT|O_WRONLY|O_TRUNC|O_LARGEFILE, m)`, and
`access(p, m)` is `do_faccessat(AT_FDCWD, p, m, 0)`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys Fs

/-! ## `openat` -/

/-- LPS `Sys/Fs/Open.v:27` `openat_errnos`. -/
def openatErrnos : List Int := [ENOMEM, EACCES, EMFILE, ENFILE]

/-- LPS `Sys/Fs/Open.v:30` `wr_create_flags`. -/
def wrCreateFlags : Int := O_WRONLY + O_CREAT + O_TRUNC

/-- LPS `Sys/Fs/Open.v:39` `excl_create_flags`. -/
def exclCreateFlags : Int := O_WRONLY + O_CREAT + O_EXCL

/-- LPS `Sys/Fs/Open.v:41` `is_excl_create`. -/
def isExclCreate (fl : Int) : Bool := fl == exclCreateFlags || fl == exclCreateFlags + O_TRUNC

/-- LPS `Sys/Fs/Open.v:57` `append_create_flags`. -/
def appendCreateFlags : Int := O_WRONLY + O_CREAT + O_APPEND

/-- LPS `Sys/Fs/Open.v:65` `flag_set`. -/
def flagSet (fl b : Int) : Bool := zland fl b == b

/-- LPS `Sys/Fs/Open.v:87` `rdwr_open_word`. -/
def rdwrOpenWord (fl : Int) : Bool :=
  fl == O_RDWR || fl == O_RDWR + O_TRUNC || fl == O_RDWR + O_CREAT ||
    fl == O_RDWR + O_CREAT + O_TRUNC

/-- LPS `Sys/Fs/Open.v:100` `rdwr_excl_create_flags`. -/
def rdwrExclCreateFlags : Int := O_RDWR + O_CREAT + O_EXCL

/-- LPS `Sys/Fs/Open.v:102` `is_rdwr_excl_create`. -/
def isRdwrExclCreate (fl : Int) : Bool :=
  fl == rdwrExclCreateFlags || fl == rdwrExclCreateFlags + O_TRUNC

/-- LPS `Sys/Fs/Open.v:112` `open_ignored_flags`. -/
def openIgnoredFlags : Int := O_CLOEXEC + O_LARGEFILE + O_NONBLOCK

/-- The flag residue every arm reads: the unsigned word without `open_ignored_flags`
(`Z.ldiff (bv_unsigned flags) open_ignored_flags`, LPS `Sys/Fs/Open.v:203`). -/
def openResidue (flags : Word) : Int := zldiff (uns flags) openIgnoredFlags

/-- LPS `Sys/Fs/Open.v:202` `modeled_open_flags`. -/
def modeledOpenFlags (flags : Word) : Bool :=
  let fl := openResidue flags
  fl == 0 || fl == wrCreateFlags || isExclCreate fl || fl == O_DIRECTORY ||
    fl == appendCreateFlags || rdwrOpenWord fl || isRdwrExclCreate fl

/-- LPS `Sys/Fs/Open.v:268` `open_result_spec`: an injected failure, or the lowest free
descriptor and `mk`'s update. -/
def openResultSpec (m : Model) (mk : Word → Model → Model) : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom openatErrnos; errRet e)
    (do
      let fd ← lowestFd m.fds
      modify (mk fd)
      retOnly fd)

/-- LPS `Sys/Fs/Open.v:290` `create_wronly`: `p` (re)created empty, a write-only descriptor. -/
def createWronly (p : Path) (m : Model) : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom openatErrnos; errRet e)
    (do
      let fd ← lowestFd m.fds
      modify (·.withFs (Fs.set m.fs p []))
      modify (·.withFds (fdInsert m.fds fd (.fileW p 0)))
      retOnly fd)

/-- LPS `Sys/Fs/Open.v:358` `path_is_dirref`: `"."` or `".."`. -/
def pathIsDirref (p : Path) : Bool := Fs.pathEqb p dotPath || Fs.pathEqb p dotdotPath

/-- LPS `Sys/Fs/Open.v:362` `openat_read_spec`. -/
def openatReadSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p then openResultSpec m fun fd m' => m'.withFds (fdInsert m.fds fd .dir)
  else match Fs.lookup m.fs p with
    | none => errRet ENOENT
    | some _ => openResultSpec m fun fd m' => m'.withFds (fdInsert m.fds fd (.file p 0))

/-- LPS `Sys/Fs/Open.v:430` `openat_create_spec`. -/
def openatCreateSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p || fsUnder m.fs p then errRet EISDIR else createWronly p m

/-- LPS `Sys/Fs/Open.v:447` `append_open_fs`: an existing file is left alone. -/
def appendOpenFs (fs : FileSystem) (p : Path) : FileSystem :=
  match Fs.lookup fs p with
  | some _ => fs
  | none => Fs.set fs p []

/-- LPS `Sys/Fs/Open.v:473` `open_append`. -/
def openAppend (p : Path) (m : Model) : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom openatErrnos; errRet e)
    (do
      let fd ← lowestFd m.fds
      modify (·.withFs (appendOpenFs m.fs p))
      modify (·.withFds (fdInsert m.fds fd (.fileA p 0)))
      retOnly fd)

/-- LPS `Sys/Fs/Open.v:492` `openat_append_spec`. -/
def openatAppendSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p || fsUnder m.fs p then errRet EISDIR else openAppend p m

/-- LPS `Sys/Fs/Open.v:502` `openat_excl_spec`. -/
def openatExclSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p || fsUnder m.fs p then errRet EEXIST
  else match Fs.lookup m.fs p with
    | some _ => errRet EEXIST
    | none => createWronly p m

/-- LPS `Sys/Fs/Open.v:529` `open_rdwr`. -/
def openRdwr (p : Path) (fs' : FileSystem) (m : Model) : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom openatErrnos; errRet e)
    (do
      let fd ← lowestFd m.fds
      modify (·.withFs fs')
      modify (·.withFds (fdInsert m.fds fd (.fileRW p 0)))
      retOnly fd)

/-- LPS `Sys/Fs/Open.v:570` `openat_rdwr_spec`. -/
def openatRdwrSpec (creat trunc : Bool) (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p || fsUnder m.fs p then errRet EISDIR
  else match Fs.lookup m.fs p with
    | none => if creat then openRdwr p (Fs.set m.fs p []) m else errRet ENOENT
    | some _ => openRdwr p (if trunc then Fs.set m.fs p [] else m.fs) m

/-- LPS `Sys/Fs/Open.v:587` `openat_rdwr_excl_spec`. -/
def openatRdwrExclSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p || fsUnder m.fs p then errRet EEXIST
  else match Fs.lookup m.fs p with
    | some _ => errRet EEXIST
    | none => openRdwr p (Fs.set m.fs p []) m

/-- LPS `Sys/Fs/Open.v:663` `openat_dir_spec`. -/
def openatDirSpec (p : Path) (m : Model) : Sys SyscallEffect :=
  if pathIsDirref p then openResultSpec m fun fd m' => m'.withFds (fdInsert m.fds fd .dir)
  else if NAME_MAX < p.length then unmodeled
  else if fsUnder m.fs p then unmodeled
  else match Fs.lookup m.fs p with
    | none => errRet ENOENT
    | some _ => errRet ENOTDIR

/-- LPS `Sys/Fs/Open.v:755` `openat_plain_name`. -/
def openatPlainName (p : Path) : Bool := !pathIsDirref p && !pathHasSlash p

/-- LPS `Sys/Fs/Open.v:866` `localtime_path`: `"/etc/localtime"`. -/
def localtimePath : Path := [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101]

/-- LPS `Sys/Fs/Open.v:871` `openat_localtime_spec`: `ENOENT` without `O_CREAT`, under the
declared assumption that the image has no `/etc/localtime`. -/
def openatLocaltimeSpec (flags : Word) (m : Model) : Sys SyscallEffect :=
  match Fs.lookup m.fs localtimePath with
  | some _ => unmodeled
  | none =>
    if fsUnder m.fs localtimePath then unmodeled
    else if flagSet (openResidue flags) O_CREAT then unmodeled
    else errRet ENOENT

/-- LPS `Sys/Fs/Open.v:946` `open_devnull`. -/
def openDevnull (m : Model) (rd wr : Bool) : Sys SyscallEffect :=
  openResultSpec m fun fd m' => m'.withFds (fdInsert m.fds fd (.devNull rd wr))

/-- LPS `Sys/Fs/Open.v:950` `openat_devnull_spec`. -/
def openatDevnullSpec (flags : Word) (m : Model) : Sys SyscallEffect :=
  match Fs.lookup m.fs devnullPath with
  | some _ => unmodeled
  | none =>
    if fsUnder m.fs devnullPath then unmodeled
    else
      let fl := openResidue flags
      if fl == 0 then openDevnull m true false
      else if fl == wrCreateFlags then openDevnull m false true
      else if isExclCreate fl then errRet EEXIST
      else if fl == O_DIRECTORY then errRet ENOTDIR
      else if fl == appendCreateFlags then openDevnull m false true
      else if rdwrOpenWord fl then openDevnull m true true
      else if isRdwrExclCreate fl then errRet EEXIST
      else unmodeled

/-- LPS `Sys/Fs/Open.v:1028` `open_urandom`. -/
def openUrandom (m : Model) : Sys SyscallEffect :=
  openResultSpec m fun fd m' => m'.withFds (fdInsert m.fds fd .urandom)

/-- LPS `Sys/Fs/Open.v:1032` `openat_urandom_spec`: read-only; the write words are
`unmodeled`. -/
def openatUrandomSpec (flags : Word) (m : Model) : Sys SyscallEffect :=
  match Fs.lookup m.fs urandomPath with
  | some _ => unmodeled
  | none =>
    if fsUnder m.fs urandomPath then unmodeled
    else
      let fl := openResidue flags
      if fl == 0 then openUrandom m
      else if isExclCreate fl then errRet EEXIST
      else if fl == O_DIRECTORY then errRet ENOTDIR
      else if isRdwrExclCreate fl then errRet EEXIST
      else unmodeled

/-- LPS `Sys/Fs/Open.v:1149` `openat_tmp_spec`: the run's private `/tmp`. -/
def openatTmpSpec (n p : Path) (flags : Word) (m : Model) : Sys SyscallEffect :=
  if NAME_MAX < n.length then unmodeled
  else
    let fl := openResidue flags
    if fl == 0 then
      (if fsUnder m.fs p then unmodeled
       else match Fs.lookup m.fs p with
         | none => unmodeled
         | some _ => openatReadSpec p m)
    else if fl == wrCreateFlags then openatCreateSpec p m
    else unmodeled

/-- LPS `Sys/Fs/Open.v:1170` `openat_sep_spec`: the separator-bearing paths that are answered. -/
def openatSepSpec (p : Path) (flags : Word) (m : Model) : Sys SyscallEffect :=
  if Fs.pathEqb p localtimePath then openatLocaltimeSpec flags m
  else if Fs.pathEqb p devnullPath then openatDevnullSpec flags m
  else if Fs.pathEqb p urandomPath then openatUrandomSpec flags m
  else match tmpName p with
    | some n => openatTmpSpec n p flags m
    | none => unmodeled

/-- LPS `Sys/Fs/Open.v:1202` `openat_resolved_spec`: dispatch by flag word. -/
def openatResolvedSpec (p : Path) (flags : Word) (m : Model) : Sys SyscallEffect :=
  if pathHasSlash p then openatSepSpec p flags m
  else
    let fl := openResidue flags
    if fl == 0 then openatReadSpec p m
    else if fl == wrCreateFlags then openatCreateSpec p m
    else if isExclCreate fl then openatExclSpec p m
    else if fl == O_DIRECTORY then openatDirSpec p m
    else if fl == appendCreateFlags then openatAppendSpec p m
    else if rdwrOpenWord fl then openatRdwrSpec (flagSet fl O_CREAT) (flagSet fl O_TRUNC) p m
    else if isRdwrExclCreate fl then openatRdwrExclSpec p m
    else unmodeled

/-- LPS `Sys/Fs/Open.v:1339` `openat_body_spec`: `getname`, then the dirfd, then the path. -/
def openatBodySpec (i : SyscallInput) (m : Model) (dirfd pathp flags : Word) :
    Sys SyscallEffect :=
  match readCstr i.mem pathp with
  | .tooLong => errRet ENAMETOOLONG
  | .fault => errRet EFAULT
  | .ok p =>
    if Fs.pathEqb p [] then errRet ENOENT
    else if !(dirfd == AT_FDCWD32) then unmodeled
    else openatResolvedSpec p flags m

/-- LPS `Sys/Fs/Open.v:1353` `openat_core_spec`: `build_open_flags` first. -/
def openatCoreSpec (dirfd pathp flags : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !modeledOpenFlags flags then unmodeled else openatBodySpec i m dirfd pathp flags

/-- LPS `Sys/Fs/Open.v:1365` `openat_spec`: the pathname copy-in is recorded. The same
specification serves x86-64 `openat` (number 257). -/
def openatSpec (dirfd pathp flags : Word) : Sys SyscallEffect := do
  let i ← input
  recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)] (openatCoreSpec dirfd pathp flags)

/-- x86-64 `open` (number 2; not in LPS's asm-generic table): `do_sys_open(AT_FDCWD, …)`
(`fs/open.c`, `SYSCALL_DEFINE3(open)`), which is LPS `openat_spec` (`Sys/Fs/Open.v:1365`) at
`AT_FDCWD`. The `O_LARGEFILE` that `force_o_largefile()` adds is in `open_ignored_flags`. -/
def openSpecX86 (pathp flags : Word) : Sys SyscallEffect := openatSpec AT_FDCWD32 pathp flags

/-- x86-64 `creat` (number 85; not in LPS's asm-generic table):
`do_sys_open(AT_FDCWD, p, O_CREAT|O_WRONLY|O_TRUNC|O_LARGEFILE, mode)` (`fs/open.c`,
`SYSCALL_DEFINE2(creat)`), LPS `openat_spec` (`Sys/Fs/Open.v:1365`) on that word. -/
def creatSpecX86 (pathp : Word) : Sys SyscallEffect :=
  openatSpec AT_FDCWD32 pathp (zw (wrCreateFlags + O_LARGEFILE))

/-! ## `ftruncate` -/

/-- LPS `Sys/Fs/Open.v:1409` `modeled_truncate_gap`. -/
def modeledTruncateGap (data : List Byte) (len : Word) : Bool := modeledZeroFill (uns len) data

/-- LPS `Sys/Fs/Open.v:1600` `ftruncate_spec`: a negative length is `EINVAL` before the
descriptor; the offset is never touched. The same specification serves x86-64 `ftruncate`
(number 77). -/
def ftruncateSpec (fd len : Word) : Sys SyscallEffect :=
  if len.toInt < 0 then errRet EINVAL
  else do
    let m ← getModel
    match fdLookup m.fds fd with
    | none => errRet EBADF
    | some (.channel _) => errRet EINVAL
    | some (.socket _) => errRet EINVAL
    | some (.pipe _ _) => errRet EINVAL
    | some (.devNull _ _) => errRet EINVAL
    | some .urandom => errRet EINVAL
    | some (.file _ _) => errRet EINVAL
    | some .dir => errRet EINVAL
    | some (.fileA p _) | some (.fileW p _) | some (.fileRW p _) =>
      match Fs.lookup m.fs p with
      | none => unmodeled
      | some data =>
        if !modeledTruncateGap data len then unmodeled
        else do
          modify (·.withFs (Fs.set m.fs p (fileTruncate data len)))
          retOnly 0

/-! ## `faccessat` and `faccessat2` -/

/-- LPS `Sys/Fs/Open.v:1755` `faccessat_errnos`. -/
def faccessatErrnos : List Int := [ENOMEM, EACCES]

/-- LPS `Sys/Fs/Open.v:1759` `access_mode`: the `int` mode. -/
def accessMode (mode : Word) : Int := uns (int32 mode)

/-- LPS `Sys/Fs/Open.v:1766` `modeled_access_mode`: `mode & ~S_IRWXO` is zero. -/
def modeledAccessMode (mode : Word) : Bool := zldiff (accessMode mode) S_IRWXO == 0

/-- LPS `Sys/Fs/Open.v:1770` `access_mode_f_ok`: `F_OK`, the only mode modeled. -/
def accessModeFOk (mode : Word) : Bool := accessMode mode == 0

/-- LPS `Sys/Fs/Open.v:1778` `access_exists_spec`: 0, or an injected failure. -/
def accessExistsSpec : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom faccessatErrnos; errRet e) (retOnly 0)

/-- LPS `Sys/Fs/Open.v:1905` `faccessat_body_spec`. -/
def faccessatBodySpec (dirfd pathp : Word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  match readCstr i.mem pathp with
  | .tooLong => errRet ENAMETOOLONG
  | .fault => errRet EFAULT
  | .ok p =>
    if Fs.pathEqb p [] then errRet ENOENT
    else if !(dirfd == AT_FDCWD32) then unmodeled
    else if Fs.pathEqb p dotPath then accessExistsSpec
    else if Fs.pathEqb p dotdotPath then accessExistsSpec
    else if pathHasSlash p then unmodeled
    else if NAME_MAX < p.length then unmodeled
    else if fsUnder m.fs p then unmodeled
    else match Fs.lookup m.fs p with
      | none => errRet ENOENT
      | some _ => accessExistsSpec

/-- LPS `Sys/Fs/Open.v:1936` `faccessat_spec`. The same specification serves x86-64
`faccessat` (number 269). -/
def faccessatSpec (dirfd pathp mode : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !modeledAccessMode mode then errRet EINVAL
  else if !accessModeFOk mode then unmodeled
  else
    recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
      (faccessatBodySpec dirfd pathp i m)

/-- x86-64 `access` (number 21; not in LPS's asm-generic table): `do_faccessat(AT_FDCWD, p,
mode, 0)` (`fs/open.c`, `SYSCALL_DEFINE2(access)`), which is LPS `faccessat_spec`
(`Sys/Fs/Open.v:1936`) at `AT_FDCWD`. -/
def accessSpecX86 (pathp mode : Word) : Sys SyscallEffect := faccessatSpec AT_FDCWD32 pathp mode

/-- LPS `Sys/Fs/Open.v:1948` `access_flags`: the `int` flags. -/
def accessFlags (flags : Word) : Int := uns (int32 flags)

/-- LPS `Sys/Fs/Open.v:1954` `access_flags_mask`. -/
def accessFlagsMask : Int := zlor AT_EACCESS (zlor AT_SYMLINK_NOFOLLOW AT_EMPTY_PATH)

/-- LPS `Sys/Fs/Open.v:1963` `valid_access_flags`. -/
def validAccessFlags (flags : Word) : Bool := zldiff (accessFlags flags) accessFlagsMask == 0

/-- LPS `Sys/Fs/Open.v:1970` `modeled_access_flags`: `AT_EMPTY_PATH` is declined. -/
def modeledAccessFlags (flags : Word) : Bool := zland (accessFlags flags) AT_EMPTY_PATH == 0

/-- LPS `Sys/Fs/Open.v:2056` `faccessat2_spec`. The same specification serves x86-64
`faccessat2` (number 439). -/
def faccessat2Spec (dirfd pathp mode flags : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !modeledAccessMode mode then errRet EINVAL
  else if !validAccessFlags flags then errRet EINVAL
  else if !modeledAccessFlags flags then unmodeled
  else if !accessModeFOk mode then unmodeled
  else
    recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
      (faccessatBodySpec dirfd pathp i m)

end Silmaril.Process.LPS
