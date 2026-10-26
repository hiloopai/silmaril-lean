module

public import Silmaril.Process.LPS.Sys.ReadWrite
public import Silmaril.Process.LPS.Uapi

/-!
# LPS in Lean: `pread64`, `pwrite64`, `writev`, `readv` and `lseek`

Translation of the rest of LPS `Sys/Fs/ReadWrite.v` (upstream commit `f1006fe8`), the
specification of Linux `fs/read_write.c`; `read_spec` and `write_spec` are in
`Silmaril.Process.LPS.Sys.ReadWrite`.

* `pread64`/`pwrite64` (`ReadWrite.v:1262-1634`): `pos < 0` is `EINVAL` before the
  descriptor; channels, pipes and sockets are `ESPIPE` (no `FMODE_PREAD`/`FMODE_PWRITE`);
  then `vfs_read`/`vfs_write` at `pos`, leaving the descriptor's offset where it was. A
  `pwrite64` on an append descriptor is `unmodeled`, as in LPS.
* `writev` (`ReadWrite.v:1650-1929`): the `iovec` import, the zero aggregate, the position
  test, then a channel's nonempty prefix of the gathered bytes or a file's whole gathered
  prefix; vectored writes to pipes and sockets are `unmodeled`.
* `readv` (`ReadWrite.v:1996-2421`): `FMODE_READ` before the import, the heap-backed count
  band `9..IOV_MAX` declined (`-ENOMEM` of the temporary array), then the canonical scatter;
  vectored reads of pipes and of `/dev/urandom` are `unmodeled`, as in LPS.
* `lseek` (`ReadWrite.v:2433-2628`): `EBADF`, then `whence > SEEK_MAX` is `EINVAL`, then the
  kind: streams are `ESPIPE`, the devices pin the offset at 0, a directory is `unmodeled`,
  `SEEK_DATA`/`SEEK_HOLE` on a file are `unmodeled`.

## x86-64

The only architecture-dependent test in these specifications is `access_ok`, reached through
`pread64`/`pwrite64` directly and through `__import_iovec` in `readv`/`writev`. Each spec that
consults it is written over the predicate `ok`; the LPS specification is the instance at
`accessOkb` and the x86-64 one (`…X86`) the instance at `accessOkbX86`. `lseek` consults no
user memory and is the same specification on both. `struct iovec` (16 bytes, base then
length) and every argument order are the same on x86-64.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys Fs

/-! ## `pread64` and `pwrite64` -/

/-- LPS `Sys/Fs/ReadWrite.v:1326` `ppos_einvalb`: `pos < 0` as an `loff_t`. -/
def pposEinvalb (pos : Word) : Bool := decide (pos.toInt < 0)

/-- LPS `Sys/Fs/ReadWrite.v:1369` `pread64_spec`, over the `access_ok` predicate `ok`. -/
def pread64SpecWith (ok : Word → Int → Bool) (fd buf count pos : Word) : Sys SyscallEffect :=
  if pposEinvalb pos then errRet EINVAL
  else do
    let i ← input
    let m ← getModel
    match fdLookup m.fds fd with
    | none => errRet EBADF
    | some (.channel _) => errRet ESPIPE
    | some (.pipe _ _) => errRet ESPIPE
    | some (.socket _) => errRet ESPIPE
    | some (.fileW _ _) => errRet EBADF
    | some (.fileA _ _) => errRet EBADF
    | some (.devNull rd _) =>
      if !rd then errRet EBADF
      else if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else retOnly 0
    | some .urandom =>
      if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else readUrandom buf count i m
    | some .dir =>
      if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else errRet EISDIR
    | some (.file p _) | some (.fileRW p _) =>
      if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else match Fs.lookup m.fs p with
        | none => unmodeled
        | some data =>
          let bs := fileRead data pos (zw (rwCountClamp count))
          match readBytesMap i.wmem buf (lenWord bs) with
          | none =>
            match readBytesMap i.wmem buf 1 with
            | none => errRet EFAULT
            | some _ => unmodeled
          | some _ => Sys.pure (mkEffect (lenWord bs) (deliveredWrites buf bs) [])

/-- LPS `Sys/Fs/ReadWrite.v:1369` `pread64_spec` (riscv64 `access_ok`). -/
def pread64Spec (fd buf count pos : Word) : Sys SyscallEffect :=
  pread64SpecWith accessOkb fd buf count pos

/-- x86-64 `pread64` (number 17): LPS `pread64_spec` with x86-64 `access_ok`. -/
def pread64SpecX86 (fd buf count pos : Word) : Sys SyscallEffect :=
  pread64SpecWith accessOkbX86 fd buf count pos

/-- LPS `Sys/Fs/ReadWrite.v:1518` `pwrite64_spec`, over the `access_ok` predicate `ok`. -/
def pwrite64SpecWith (ok : Word → Int → Bool) (fd buf count pos : Word) : Sys SyscallEffect :=
  if pposEinvalb pos then errRet EINVAL
  else do
    let i ← input
    let m ← getModel
    match fdLookup m.fds fd with
    | none => errRet EBADF
    | some (.channel _) => errRet ESPIPE
    | some (.pipe _ _) => errRet ESPIPE
    | some (.socket _) => errRet ESPIPE
    | some (.file _ _) => errRet EBADF
    | some .urandom => errRet EBADF
    | some (.devNull _ wr) =>
      if !wr then errRet EBADF
      else if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else retOnly (zw (rwCountClamp count))
    | some .dir => errRet EBADF
    | some (.fileA _ _) => unmodeled
    | some (.fileW p _) | some (.fileRW p _) =>
      if !ok buf (uns count) then errRet EFAULT
      else if rwPosEinvalb pos (uns count) then errRet EINVAL
      else
        let bs := writeSource i.mem buf count
        if !wIs0 count && bs.length == 0 then errRet EFAULT
        else match Fs.lookup m.fs p with
          | none => unmodeled
          | some data =>
            if !modeledFileGap data pos bs then unmodeled
            else do
              modify (·.withFs (Fs.set m.fs p (fileWrite data pos bs)))
              if wIs0 count then retOnly (lenWord bs)
              else recordCopyins [(buf, bs.length)] (retOnly (lenWord bs))

/-- LPS `Sys/Fs/ReadWrite.v:1518` `pwrite64_spec` (riscv64 `access_ok`). -/
def pwrite64Spec (fd buf count pos : Word) : Sys SyscallEffect :=
  pwrite64SpecWith accessOkb fd buf count pos

/-- x86-64 `pwrite64` (number 18): LPS `pwrite64_spec` with x86-64 `access_ok`. -/
def pwrite64SpecX86 (fd buf count pos : Word) : Sys SyscallEffect :=
  pwrite64SpecWith accessOkbX86 fd buf count pos

/-! ## `writev` -/

/-- LPS `Sys/Fs/ReadWrite.v:1650` `iovcnt32`: only the low 32 bits of the count are used. -/
def iovcnt32 (iovcnt : Word) : Word := abiLow32 iovcnt

/-- LPS `Sys/Fs/ReadWrite.v:1656` `writev_buf_gap`: a `writev` the model declines. -/
def writevBufGap : Sys SyscallEffect := unmodeled

/-- LPS `Sys/Fs/ReadWrite.v:1738` `writev_ledger`. -/
def writevLedger (iovs : List (Word × Word)) (bs : List Byte) : Sys SyscallEffect :=
  recordCopyins (iovPrefixAccesses (capIovecs iovs) bs.length) (retOnly (lenWord bs))

/-- LPS `Sys/Fs/ReadWrite.v:1760` `writev_file_arm`, over the `access_ok` predicate `ok`. -/
def writevFileArmWith (ok : Word → Int → Bool) (mp : Word → Option Byte) (iov iovcnt off : Word)
    (place : List Byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  recordCopyins (importIovecsAccessesWith ok mp iov (iovcnt32 iovcnt))
    (match importIovecsWith ok mp iov (iovcnt32 iovcnt) with
     | .fault => errRet EFAULT
     | .inval => errRet EINVAL
     | .ok iovs0 =>
       let total := iovsTotal (capIovecs iovs0)
       let bs := writevGathered mp iovs0
       if total == 0 then retOnly 0
       else if rwPosEinvalb off total then errRet EINVAL
       else if bs.length == 0 then errRet EFAULT
       else match place bs with
         | none => writevBufGap
         | some upd =>
           if addrIsError (lenWord bs) then writevBufGap else upd (writevLedger iovs0 bs))

/-- LPS `Sys/Fs/ReadWrite.v:1783` `writev_spec`, over the `access_ok` predicate `ok`. -/
def writevSpecWith (ok : Word → Int → Bool) (fd iov iovcnt : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.file _ _) => errRet EBADF
  | some .dir => errRet EBADF
  | some (.socket _) => writevBufGap
  | some (.channel ch) =>
    if wIs0 ch then errRet EBADF
    else
      recordCopyins (importIovecsAccessesWith ok i.mem iov (iovcnt32 iovcnt))
        (match importIovecsWith ok i.mem iov (iovcnt32 iovcnt) with
         | .fault => errRet EFAULT
         | .inval => errRet EINVAL
         | .ok iovs0 =>
           let total := iovsTotal (capIovecs iovs0)
           let bs := writevGathered i.mem iovs0
           if total == 0 then retOnly 0
           else if bs.length == 0 then errRet EFAULT
           else if addrIsError (lenWord bs) then writevBufGap
           else do
             let ds ← Sys.choose fun ds : List Byte =>
               1 ≤ ds.length ∧ (ds.length : Int) < twoPow64 ∧
                 addrIsError (lenWord ds) = false ∧ ds = bs.take ds.length
             emit (ds.map (.writeEv ch))
             recordCopyins (iovPrefixAccesses (capIovecs iovs0) ds.length)
               (retOnly (lenWord ds)))
  | some (.fileW p off) =>
    writevFileArmWith ok i.mem iov iovcnt off fun bs =>
      match Fs.lookup m.fs p with
      | none => none
      | some data =>
        if !modeledFileGap data off bs then none
        else some fun k => do
          modify (·.withFs (Fs.set m.fs p (fileWrite data off bs)))
          modify (·.withFds (fdInsert m.fds fd (.fileW p (off + lenWord bs))))
          k
  | some (.fileRW p off) =>
    writevFileArmWith ok i.mem iov iovcnt off fun bs =>
      match Fs.lookup m.fs p with
      | none => none
      | some data =>
        if !modeledFileGap data off bs then none
        else some fun k => do
          modify (·.withFs (Fs.set m.fs p (fileWrite data off bs)))
          modify (·.withFds (fdInsert m.fds fd (.fileRW p (off + lenWord bs))))
          k
  | some (.fileA p off) =>
    writevFileArmWith ok i.mem iov iovcnt off fun bs =>
      match Fs.lookup m.fs p with
      | none => none
      | some data => some fun k => do
        modify (·.withFs (Fs.set m.fs p (fileWrite data (lenWord data) bs)))
        modify (·.withFds (fdInsert m.fds fd (.fileA p (appendNewPos data bs off))))
        k
  | some .urandom => errRet EBADF
  | some (.devNull _ wr) =>
    if !wr then errRet EBADF
    else
      recordCopyins (importIovecsAccessesWith ok i.mem iov (iovcnt32 iovcnt))
        (match importIovecsWith ok i.mem iov (iovcnt32 iovcnt) with
         | .fault => errRet EFAULT
         | .inval => errRet EINVAL
         | .ok iovs0 => retOnly (zw (iovsTotal (capIovecs iovs0))))
  | some (.pipe _ w) =>
    if !w then errRet EBADF
    else
      recordCopyins (importIovecsAccessesWith ok i.mem iov (iovcnt32 iovcnt))
        (match importIovecsWith ok i.mem iov (iovcnt32 iovcnt) with
         | .fault => errRet EFAULT
         | .inval => errRet EINVAL
         | .ok iovs0 =>
           if iovsTotal (capIovecs iovs0) == 0 then retOnly 0 else writevBufGap)

/-- LPS `Sys/Fs/ReadWrite.v:1783` `writev_spec` (riscv64 `access_ok`). -/
def writevSpec (fd iov iovcnt : Word) : Sys SyscallEffect := writevSpecWith accessOkb fd iov iovcnt

/-- x86-64 `writev` (number 20): LPS `writev_spec` with x86-64 `access_ok`. -/
def writevSpecX86 (fd iov iovcnt : Word) : Sys SyscallEffect :=
  writevSpecWith accessOkbX86 fd iov iovcnt

/-! ## `readv` -/

/-- LPS `Sys/Fs/ReadWrite.v:1996` `ReadableFd`: the kinds a `readv` reaches once the
`FMODE_READ` gate has passed. -/
inductive ReadableFd where
  | channel (chan : Word)
  | file (p : Path) (offset : Word)
  | fileRW (p : Path) (offset : Word)
  | dir
  | socket (sk : SockState)
  | pipe (id : Word)
  | devNull
  | urandom

/-- LPS `Sys/Fs/ReadWrite.v:2044` `readable_fd`: `FMODE_READ`. -/
def readableFd : FdEntry → Option ReadableFd
  | .channel ch => if wIs0 ch then some (.channel ch) else none
  | .file p off => some (.file p off)
  | .fileRW p off => some (.fileRW p off)
  | .dir => some .dir
  | .socket sk => some (.socket sk)
  | .fileW _ _ => none
  | .fileA _ _ => none
  | .pipe id w => if w then none else some (.pipe id)
  | .devNull rd _ => if rd then some .devNull else none
  | .urandom => some .urandom

/-- LPS `Sys/Fs/ReadWrite.v:2080` `UIO_FASTIOV`. -/
def UIO_FASTIOV : Int := 8

/-- LPS `Sys/Fs/ReadWrite.v:2082` `readv_heap_iovecb`: counts `9..IOV_MAX` allocate. -/
def readvHeapIovecb (iovcnt : Word) : Bool :=
  let n := uns (iovcnt32 iovcnt)
  decide (UIO_FASTIOV < n) && decide (n ≤ IOV_MAX)

/-- LPS `Sys/Fs/ReadWrite.v:2090` `readv_buf_gap`: a `readv` the model declines. -/
def readvBufGap : Sys SyscallEffect := unmodeled

/-- LPS `Sys/Fs/ReadWrite.v:2098` `readv_heap_gap`. -/
def readvHeapGap : Sys SyscallEffect := readvBufGap

/-- Reading a file into the imported vector (LPS `Sys/Fs/ReadWrite.v:2299-2357`, shared by
`RdFile` and `RdFileRW`). -/
def readvFile (fd : Word) (iovs : List (Word × Word)) (total : Int) (i : SyscallInput)
    (m : Model) (p : Path) (off : Word) (reentry : Path → Word → FdEntry) : Sys SyscallEffect :=
  match Fs.lookup m.fs p with
  | none => readvBufGap
  | some data =>
    if rwPosEinvalb off total then errRet EINVAL
    else
      let bs := fileRead data off (zw total)
      match scatterIovecs i.wmem iovs bs with
      | some writes =>
        if addrIsError (lenWord bs) then readvBufGap
        else do
          modify (·.withFds (fdInsert m.fds fd (reentry p (off + lenWord bs))))
          Sys.pure (mkEffect (lenWord bs) writes [])
      | none =>
        match scatterIovecs i.wmem iovs [0] with
        | none => errRet EFAULT
        | some _ => readvBufGap

/-- LPS `Sys/Fs/ReadWrite.v:2168` `readv_imported`: execute a `readv` once the vector is
imported. -/
def readvImported (fd : Word) (r : ReadableFd) (iovs0 : List (Word × Word)) (i : SyscallInput)
    (m : Model) : Sys SyscallEffect :=
  let iovs := capIovecs iovs0
  let total := iovsTotal iovs
  if total == 0 then retOnly 0
  else match r with
    | .channel ch =>
      if m.stdin.atEof then retOnly 0
      else match scatterIovecs i.wmem iovs [0] with
        | none => errRet EFAULT
        | some _ =>
          match scatterIovecs i.wmem iovs (m.stdin.takeZ total).1 with
          | none => readvBufGap
          | some _ => do
            let bs ← Sys.choose fun bs : List Byte =>
              1 ≤ bs.length ∧ (bs.length : Int) ≤ total ∧ (m.stdin.take bs.length).1 = bs ∧
                (scatterIovecs i.wmem iovs bs).isSome
            match scatterIovecs i.wmem iovs bs with
            | some writes => do
              modify (·.withStdin (m.stdin.take bs.length).2)
              emit (bs.map (.readEv ch))
              Sys.pure (mkEffect (lenWord bs) writes [])
            | none => Sys.choose fun _ : SyscallEffect => False
    | .socket sk =>
      match sk with
      | .connected peer ch rx =>
        match rx.item 0 with
        | .inr .fin => retOnly 0
        | .inr .rst => do
          modify (·.withFds (fdInsert m.fds fd (.socket (.reset peer ch))))
          errRet ECONNRESET
        | .inr .timedOut => do
          modify (·.withFds (fdInsert m.fds fd (.socket (.reset peer ch))))
          errRet ETIMEDOUT
        | .inl _ =>
          match scatterIovecs i.wmem iovs [0] with
          | none => errRet EFAULT
          | some _ =>
            match scatterIovecs i.wmem iovs (rx.takeZ total).1 with
            | none => readvBufGap
            | some _ => do
              let bs ← Sys.choose fun bs : List Byte =>
                1 ≤ bs.length ∧ (bs.length : Int) ≤ total ∧ (rx.take bs.length).1 = bs ∧
                  (scatterIovecs i.wmem iovs bs).isSome
              match scatterIovecs i.wmem iovs bs with
              | some writes => do
                modify (·.withFds
                  (fdInsert m.fds fd (.socket (.connected peer ch (rx.take bs.length).2))))
                emit (bs.map (.readEv ch))
                Sys.pure (mkEffect (lenWord bs) writes [])
              | none => Sys.choose fun _ : SyscallEffect => False
      | .reset _ _ => retOnly 0
      | _ => errRet ENOTCONN
    | .pipe _ => readvBufGap
    | .devNull => retOnly 0
    | .urandom => readvBufGap
    | .dir => errRet EISDIR
    | .file p off => readvFile fd iovs total i m p off .file
    | .fileRW p off => readvFile fd iovs total i m p off .fileRW

/-- LPS `Sys/Fs/ReadWrite.v:2396` `readv_spec`, over the `access_ok` predicate `ok`. -/
def readvSpecWith (ok : Word → Int → Bool) (fd iov iovcnt : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some e =>
    match readableFd e with
    | none => errRet EBADF
    | some r =>
      if readvHeapIovecb iovcnt then readvHeapGap
      else
        recordCopyins (importIovecsAccessesWith ok i.mem iov (iovcnt32 iovcnt))
          (match importIovecsWith ok i.mem iov (iovcnt32 iovcnt) with
           | .fault => errRet EFAULT
           | .inval => errRet EINVAL
           | .ok iovs0 => readvImported fd r iovs0 i m)

/-- LPS `Sys/Fs/ReadWrite.v:2396` `readv_spec` (riscv64 `access_ok`). -/
def readvSpec (fd iov iovcnt : Word) : Sys SyscallEffect := readvSpecWith accessOkb fd iov iovcnt

/-- x86-64 `readv` (number 19): LPS `readv_spec` with x86-64 `access_ok`. -/
def readvSpecX86 (fd iov iovcnt : Word) : Sys SyscallEffect :=
  readvSpecWith accessOkbX86 fd iov iovcnt

/-! ## `lseek` -/

/-- LPS `Sys/Fs/ReadWrite.v:2433` `lseek_base`: the origin `SEEK_SET`/`SEEK_CUR`/`SEEK_END`
selects; `none` for `SEEK_DATA`/`SEEK_HOLE`. -/
def lseekBase (whence cur len : Word) : Option Word :=
  if uns whence == SEEK_SET then some 0
  else if uns whence == SEEK_CUR then some cur
  else if uns whence == SEEK_END then some len
  else none

/-- LPS `Sys/Fs/ReadWrite.v:2445` `lseek_dest`: `base` plus the signed displacement, `none`
when negative or past `LLONG_MAX`. -/
def lseekDest (base off : Word) : Option Word :=
  let d := uns base + off.toInt
  if decide (0 ≤ d) && decide (d < 2 ^ 63) then some (zw d) else none

/-- Repositioning a regular file (LPS `Sys/Fs/ReadWrite.v:2544-2626`, shared by the four file
kinds, which `generic_file_llseek` does not tell apart). -/
def lseekFile (fd off whence : Word) (m : Model) (p : Path) (cur : Word)
    (reentry : Path → Word → FdEntry) : Sys SyscallEffect :=
  match Fs.lookup m.fs p with
  | none => unmodeled
  | some data =>
    match lseekBase whence cur (lenWord data) with
    | none => unmodeled
    | some base =>
      match lseekDest base off with
      | none => errRet EINVAL
      | some r => do
        modify (·.withFds (fdInsert m.fds fd (reentry p r)))
        retOnly r

/-- LPS `Sys/Fs/ReadWrite.v:2476` `lseek_spec`. The same specification serves x86-64
`lseek` (number 8). -/
def lseekSpec (fd off whence : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some e =>
    if SEEK_MAX < uns whence then errRet EINVAL
    else match e with
      | .channel _ => errRet ESPIPE
      | .socket _ => errRet ESPIPE
      | .pipe _ _ => errRet ESPIPE
      | .devNull _ _ => retOnly 0
      | .urandom => retOnly 0
      | .dir => unmodeled
      | .file p cur => lseekFile fd off whence m p cur .file
      | .fileRW p cur => lseekFile fd off whence m p cur .fileRW
      | .fileW p cur => lseekFile fd off whence m p cur .fileW
      | .fileA p cur => lseekFile fd off whence m p cur .fileA

end Silmaril.Process.LPS
