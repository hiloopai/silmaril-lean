module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers

/-!
# LPS in Lean: `readlinkat`, `newfstatat` and `fstat` (`Sys/Fs/Stat.v`)

Translation of LPS `Sys/Fs/Stat.v` (upstream commit `f1006fe8`), the specification of Linux
`fs/stat.c`:

* `readlinkat` (asm-generic 78, x86-64 267): the model has no symbolic links, so under
  `AT_FDCWD` the answer is `EINVAL`; any other dirfd is declined;
* `newfstatat` (asm-generic 79, x86-64 262): the failing side only. Unmodeled flag words are
  declined; then `getname()`'s three answers, the empty path's `ENOENT`, the dirfd (only
  `AT_FDCWD`), `"."` declined, an absent path `ENOENT`, a present path declined (the 128 or
  144 bytes are not a function of `Fs`). The buffer is not an argument: no admitted arm
  writes it;
* `fstat` (asm-generic 80, x86-64 5): `EBADF` for a closed descriptor; for a file the
  model holds and for `/dev/null` and `/dev/urandom`, the success arm: `access_ok` over the
  whole struct (`EFAULT`), a partially writable buffer declined, then a chosen `struct stat`
  that is well formed (a file type, zeroed padding), whose `st_size` is the file's length if
  it is a regular file (or the device's constants), and whose stable members agree with the
  first `struct stat` the run saw for that path (the pin in `Model.statpins`). Channels,
  directories, sockets and pipes are declined.

## x86-64

The x86-64 `struct stat` (`arch/x86/include/uapi/asm/stat.h`, the `__x86_64__` branch) is
144 bytes, not asm-generic's 128 (see `Uapi`, `statLayoutX86`): `st_nlink` is 8 bytes before
`st_mode`, there is a 4-byte `__pad0`, `st_blksize` is 8 bytes and the tail is `__unused[3]`.
x86's `INIT_STRUCT_STAT_PADDING` zeroes exactly `__pad0` and `__unused` (every other member
is assigned by `cp_new_stat`), so the well-formedness envelope has the same shape. The
`fstat` success arm therefore exists in two instances of one shape, `fstatSpecAt`, over a
`StatAbi`: `statAbiLps` (LPS's literal predicates and `access_okb`) and `statAbiX86` (the
x86-64 layout predicates of `Uapi` and x86-64 `access_ok` of `Uaccess`). `cp_new_stat`'s
`EOVERFLOW` tests cannot fire on x86-64 either: every destination member is at least as wide
as its `kstat` source (`st_nlink` is even wider, 64 bits) and the `MAX_NON_LFS` test is under
`BITS_PER_LONG == 32`.

`readlinkat`, `newfstatat` and `fstat`'s `EBADF` never touch the buffer, so they are the
same on x86-64. x86-64 additionally has the legacy entry points `stat` (4), `lstat` (6) and
`readlink` (89), which asm-generic does not define; `fs/stat.c` defines them as
`vfs_fstatat(AT_FDCWD, filename, &stat, 0)` (`vfs_stat`), the same with
`AT_SYMLINK_NOFOLLOW` (`vfs_lstat`), and `do_readlinkat(AT_FDCWD, …)`, so they are
`newfstatatSpec` and `readlinkatSpec` at `AT_FDCWD` with the flag fixed (`statSpecX86`,
`lstatSpecX86`, `readlinkSpecX86`). musl on x86-64 issues `SYS_stat`, `SYS_lstat` and
`SYS_fstat` (`src/stat/fstatat.c`, `fstatat_kstat`, under `#ifdef SYS_lstat`) and
`SYS_readlink` (`src/unistd/readlink.c`), so these are the numbers an x86-64 binary reaches.

The `struct stat` serializers `statBytesLps` and `statBytesX86` lay out the user-visible
members for each layout; their lengths are 128 and 144 (`statBytesLps_length`,
`statBytesX86_length`). They are not part of the specification (which chooses the bytes):
they witness that the `choose` of the success arm is satisfiable on each architecture.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys
open Fs (Path FileSystem)

/-! ## `readlinkat` -/

/-- LPS `Sys/Fs/Stat.v:51` `readlinkat_spec`: no path resolves to a symbolic link, so under
`AT_FDCWD` the answer is `EINVAL` (the path is not interpreted: a missing path or a bad
pointer is coarsened to `EINVAL` as in LPS); any other dirfd is declined. -/
def readlinkatSpec (dirfd : Word) : Sys SyscallEffect :=
  if !(dirfd == AT_FDCWD32) then unmodeled else errRet EINVAL

/-- x86-64 `readlink` (89, `fs/stat.c` `SYSCALL_DEFINE3(readlink)`):
`do_readlinkat(AT_FDCWD, path, buf, bufsiz)`. Not in LPS; it is LPS `Sys/Fs/Stat.v:51`
`readlinkat_spec` at `AT_FDCWD`. -/
def readlinkSpecX86 : Sys SyscallEffect := readlinkatSpec AT_FDCWD32

theorem readlinkSpecX86_eq : readlinkSpecX86 = errRet EINVAL := by
  simp [readlinkSpecX86, readlinkatSpec]

/-! ## `newfstatat` -/

/-- LPS `Sys/Fs/Stat.v:80` `modeled_statat_flags`: `0` (`stat`) and `AT_SYMLINK_NOFOLLOW`
(`lstat`); every other word is declined. -/
def modeledStatatFlags (flag : Word) : Bool :=
  uns flag == 0 || uns flag == AT_SYMLINK_NOFOLLOW

/-- LPS `Sys/Fs/Stat.v:258` `newfstatat_core_spec`: the failing side of `newfstatat`, in the
kernel's errno priority (flag word, pathname, dirfd, file). `".."` falls through to the
lookup and is `ENOENT`, as in LPS (a divergence LPS records). -/
def newfstatatCoreSpec (dirfd pathp flag : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !modeledStatatFlags flag then unmodeled
  else match readCstr i.mem pathp with
    | .tooLong => errRet ENAMETOOLONG
    | .fault => errRet EFAULT
    | .ok p =>
      if Fs.pathEqb p [] then errRet ENOENT
      else if !(dirfd == AT_FDCWD32) then unmodeled
      else if Fs.pathEqb p dotPath then unmodeled
      else match Fs.lookup m.fs p with
        | none => errRet ENOENT
        | some _ => unmodeled

/-- LPS `Sys/Fs/Stat.v:291` `newfstatat_spec`: the core under the pathname copy-in ledger. -/
def newfstatatSpec (dirfd pathp flag : Word) : Sys SyscallEffect := do
  let i ← input
  recordCopyins [(pathp, cstrAccessLenAux i.mem pathp pathMax)]
    (newfstatatCoreSpec dirfd pathp flag)

/-- x86-64 `stat` (4, `fs/stat.c` `SYSCALL_DEFINE2(newstat)`): `vfs_stat(filename)`, which is
`vfs_fstatat(AT_FDCWD, filename, &stat, 0)`, then `cp_new_stat`. Not in LPS; its modeled
arms are LPS `Sys/Fs/Stat.v:291` `newfstatat_spec` at `AT_FDCWD` and flag `0`. -/
def statSpecX86 (pathp : Word) : Sys SyscallEffect := newfstatatSpec AT_FDCWD32 pathp 0

/-- x86-64 `lstat` (6, `fs/stat.c` `SYSCALL_DEFINE2(newlstat)`): `vfs_lstat`, which is
`vfs_fstatat(AT_FDCWD, filename, &stat, AT_SYMLINK_NOFOLLOW)`. Not in LPS; LPS
`Sys/Fs/Stat.v:291` `newfstatat_spec` at `AT_FDCWD` and `AT_SYMLINK_NOFOLLOW`. -/
def lstatSpecX86 (pathp : Word) : Sys SyscallEffect :=
  newfstatatSpec AT_FDCWD32 pathp (zw AT_SYMLINK_NOFOLLOW)

/-! ## `fstat` -/

/-- The `struct stat` ABI of an architecture: its width, its `access_ok`, and the predicates
of LPS `Sys/Uapi.v:1149-1288` at its layout. -/
structure StatAbi where
  /-- `sizeof(struct stat)` (LPS `Sys/Uapi.v:1074` `STAT_SIZE`). -/
  size : Int
  /-- `access_ok` (LPS `State.v:1344` `access_okb`). -/
  accessOk : Word → Int → Bool
  /-- LPS `Sys/Uapi.v:1149` `stat_buf_wf`. -/
  bufWf : List Byte → Bool
  /-- LPS `Sys/Uapi.v:1183` `stat_size_ok`. -/
  sizeOk : Nat → List Byte → Bool
  /-- LPS `Sys/Uapi.v:1281` `stat_stable_eqb`. -/
  stableEqb : List Byte → List Byte → Bool
  /-- LPS `Sys/Uapi.v:1222` `stat_devnull_ok`. -/
  devnullOk : List Byte → Bool
  /-- LPS `Sys/Uapi.v:1232` `stat_urandom_ok`. -/
  urandomOk : List Byte → Bool

/-- LPS's (riscv64, asm-generic) `struct stat` ABI: exactly the predicates LPS uses. -/
def statAbiLps : StatAbi :=
  ⟨STAT_SIZE, accessOkb, statBufWf, statSizeOk, statStableEqb, statDevnullOk, statUrandomOk⟩

/-- The x86-64 `struct stat` ABI: the 144-byte layout and x86-64 `access_ok`. -/
def statAbiX86 : StatAbi :=
  ⟨STAT_SIZE_X86, accessOkbX86, statBufWfX86, statSizeOkX86, statStableEqbX86, statDevnullOkX86,
    statUrandomOkX86⟩

/-- LPS `Sys/Fs/Stat.v:487` `fstat_file_spec`, at a `struct stat` ABI: the success arm for a
descriptor on a file `Fs` holds. A path `Fs` no longer holds is declined; then `access_ok`
over the whole struct (`EFAULT`); a partially writable buffer is declined; then a chosen
well-formed `struct stat` whose `st_size` is the length if regular, held to the pin's stable
members, or pinned at the first observation. A pin that is not well formed is declined (no
branch writes one). -/
def fstatFileSpecAt (A : StatAbi) (p : Path) (statbuf : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match Fs.lookup m.fs p with
  | none => unmodeled
  | some data =>
    if !A.accessOk statbuf A.size then errRet EFAULT
    else match readBytesMap i.wmem statbuf (zw A.size) with
      | none => unmodeled
      | some _ =>
        match statpinLookup m.statpins p with
        | some b0 =>
          if !A.bufWf b0 then unmodeled
          else do
            let bs ← Sys.choose fun bs : List Byte =>
              A.bufWf bs = true ∧ A.sizeOk data.length bs = true ∧ A.stableEqb bs b0 = true
            Sys.pure (mkEffect 0 [(statbuf, bs)] [])
        | none => do
          let bs ← Sys.choose fun bs : List Byte =>
            A.bufWf bs = true ∧ A.sizeOk data.length bs = true
          modify (·.withStatpin p bs)
          Sys.pure (mkEffect 0 [(statbuf, bs)] [])

/-- LPS `Sys/Fs/Stat.v:549` `fstat_chrdev_spec`, at a `struct stat` ABI: the success arm for
a character device the model knows (`p` is its pin key, `ok` its assertions). The pin is
checked against both predicates before use. -/
def fstatChrdevSpecAt (A : StatAbi) (p : Path) (ok : List Byte → Bool) (statbuf : Word) :
    Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  if !A.accessOk statbuf A.size then errRet EFAULT
  else match readBytesMap i.wmem statbuf (zw A.size) with
    | none => unmodeled
    | some _ =>
      match statpinLookup m.statpins p with
      | some b0 =>
        if !(A.bufWf b0 && ok b0) then unmodeled
        else do
          let bs ← Sys.choose fun bs : List Byte =>
            A.bufWf bs = true ∧ ok bs = true ∧ A.stableEqb bs b0 = true
          Sys.pure (mkEffect 0 [(statbuf, bs)] [])
      | none => do
        let bs ← Sys.choose fun bs : List Byte => A.bufWf bs = true ∧ ok bs = true
        modify (·.withStatpin p bs)
        Sys.pure (mkEffect 0 [(statbuf, bs)] [])

/-- LPS `Sys/Fs/Stat.v:578` `fstat_devnull_spec`, at a `struct stat` ABI. -/
def fstatDevnullSpecAt (A : StatAbi) (statbuf : Word) : Sys SyscallEffect :=
  fstatChrdevSpecAt A devnullPath A.devnullOk statbuf

/-- LPS `Sys/Fs/Stat.v:588` `fstat_urandom_spec`, at a `struct stat` ABI. -/
def fstatUrandomSpecAt (A : StatAbi) (statbuf : Word) : Sys SyscallEffect :=
  fstatChrdevSpecAt A urandomPath A.urandomOk statbuf

/-- LPS `Sys/Fs/Stat.v:662` `fstat_spec`, at a `struct stat` ABI. Total on `FdEntry`, as in
LPS: `EBADF` (before `cp_new_stat`, so the buffer is untouched), the four file kinds share
one answer, the two devices answer, channels, directories, sockets and pipes decline. -/
def fstatSpecAt (A : StatAbi) (fd statbuf : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.channel _) => unmodeled
  | some (.file p _) => fstatFileSpecAt A p statbuf
  | some (.fileW p _) => fstatFileSpecAt A p statbuf
  | some (.fileA p _) => fstatFileSpecAt A p statbuf
  | some (.fileRW p _) => fstatFileSpecAt A p statbuf
  | some .dir => unmodeled
  | some (.socket _) => unmodeled
  | some (.pipe _ _) => unmodeled
  | some (.devNull _ _) => fstatDevnullSpecAt A statbuf
  | some .urandom => fstatUrandomSpecAt A statbuf

/-- LPS `Sys/Fs/Stat.v:487` `fstat_file_spec` (the 128-byte asm-generic `struct stat`). -/
def fstatFileSpec (p : Path) (statbuf : Word) : Sys SyscallEffect :=
  fstatFileSpecAt statAbiLps p statbuf
/-- LPS `Sys/Fs/Stat.v:549` `fstat_chrdev_spec`. -/
def fstatChrdevSpec (p : Path) (ok : List Byte → Bool) (statbuf : Word) : Sys SyscallEffect :=
  fstatChrdevSpecAt statAbiLps p ok statbuf
/-- LPS `Sys/Fs/Stat.v:578` `fstat_devnull_spec`. -/
def fstatDevnullSpec (statbuf : Word) : Sys SyscallEffect := fstatDevnullSpecAt statAbiLps statbuf
/-- LPS `Sys/Fs/Stat.v:588` `fstat_urandom_spec`. -/
def fstatUrandomSpec (statbuf : Word) : Sys SyscallEffect := fstatUrandomSpecAt statAbiLps statbuf
/-- LPS `Sys/Fs/Stat.v:662` `fstat_spec` (the 128-byte asm-generic `struct stat`). -/
def fstatSpec (fd statbuf : Word) : Sys SyscallEffect := fstatSpecAt statAbiLps fd statbuf

/-- x86-64 `fstat` (5): LPS `Sys/Fs/Stat.v:662` `fstat_spec` at the 144-byte x86-64
`struct stat` and x86-64 `access_ok`. -/
def fstatSpecX86 (fd statbuf : Word) : Sys SyscallEffect := fstatSpecAt statAbiX86 fd statbuf

/-! ## `struct stat` serializers -/

/-- The user-visible members of `struct stat`, as `cp_new_stat` assigns them. -/
structure StatFields where
  dev : Nat
  ino : Nat
  mode : Nat
  nlink : Nat
  uid : Nat
  gid : Nat
  rdev : Nat
  size : Nat
  blksize : Nat
  blocks : Nat
  atime : Nat
  atimeNsec : Nat
  mtime : Nat
  mtimeNsec : Nat
  ctime : Nat
  ctimeNsec : Nat
  deriving DecidableEq, Repr

/-- `n` little-endian bytes of `v`. -/
def leN (n : Nat) (v : Nat) : List Byte := zToLeBytes n v

theorem zToLeBytes_length (n : Nat) (z : Int) : (zToLeBytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [zToLeBytes, ih]

/-- The asm-generic `struct stat` (`include/uapi/asm-generic/stat.h`), as `cp_new_stat`
writes it after `memset`: `st_dev` 0, `st_ino` 8, `st_mode` 16 (4), `st_nlink` 20 (4),
`st_uid` 24, `st_gid` 28, `st_rdev` 32, `__pad1` 40 (8, zero), `st_size` 48, `st_blksize` 56
(4), `__pad2` 60 (4, zero), `st_blocks` 64, the timestamps 72..120, `__unused4`/`__unused5`
120 (8, zero). -/
def statBytesLps (s : StatFields) : List Byte :=
  leN 8 s.dev ++ leN 8 s.ino ++ leN 4 s.mode ++ leN 4 s.nlink ++ leN 4 s.uid ++ leN 4 s.gid ++
    leN 8 s.rdev ++ List.replicate 8 0 ++ leN 8 s.size ++ leN 4 s.blksize ++
    List.replicate 4 0 ++ leN 8 s.blocks ++ leN 8 s.atime ++ leN 8 s.atimeNsec ++
    leN 8 s.mtime ++ leN 8 s.mtimeNsec ++ leN 8 s.ctime ++ leN 8 s.ctimeNsec ++
    List.replicate 8 0

/-- The x86-64 `struct stat` (`arch/x86/include/uapi/asm/stat.h`, `__x86_64__`), as
`cp_new_stat` writes it after x86's `INIT_STRUCT_STAT_PADDING`: `st_dev` 0, `st_ino` 8,
`st_nlink` 16 (8), `st_mode` 24 (4), `st_uid` 28, `st_gid` 32, `__pad0` 36 (4, zero),
`st_rdev` 40, `st_size` 48, `st_blksize` 56 (8), `st_blocks` 64, the timestamps 72..120,
`__unused[3]` 120 (24, zero). -/
def statBytesX86 (s : StatFields) : List Byte :=
  leN 8 s.dev ++ leN 8 s.ino ++ leN 8 s.nlink ++ leN 4 s.mode ++ leN 4 s.uid ++ leN 4 s.gid ++
    List.replicate 4 0 ++ leN 8 s.rdev ++ leN 8 s.size ++ leN 8 s.blksize ++ leN 8 s.blocks ++
    leN 8 s.atime ++ leN 8 s.atimeNsec ++ leN 8 s.mtime ++ leN 8 s.mtimeNsec ++
    leN 8 s.ctime ++ leN 8 s.ctimeNsec ++ List.replicate 24 0

/-- The asm-generic serialization is `STAT_SIZE = 128` bytes. -/
theorem statBytesLps_length (s : StatFields) : ((statBytesLps s).length : Int) = STAT_SIZE := by
  simp [statBytesLps, leN, zToLeBytes_length, STAT_SIZE]

/-- The x86-64 serialization is `STAT_SIZE_X86 = 144` bytes. -/
theorem statBytesX86_length (s : StatFields) :
    ((statBytesX86 s).length : Int) = STAT_SIZE_X86 := by
  simp [statBytesX86, leN, zToLeBytes_length, STAT_SIZE_X86]

/-- The two layouts have different widths, so no buffer is well formed for both. -/
theorem statBytes_length_ne (s t : StatFields) : (statBytesLps s).length ≠ (statBytesX86 t).length := by
  simp [statBytesLps, statBytesX86, leN, zToLeBytes_length]

end Silmaril.Process.LPS
