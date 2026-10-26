module

public import Silmaril.Process.LPS.Uaccess

/-!
# LPS in Lean: `read` and `write`

Translation of `read_spec` and `write_spec` from LPS `Sys/Fs/ReadWrite.v` (upstream commit
`f1006fe8`), the specification of Linux `fs/read_write.c`, with their helpers.

* A `read` of stdin (channel 0) delivers **any non-empty prefix** of the remaining stream,
  up to the clamped count, and emits one `readEv` per byte: short reads are behaviours.
* A `write` to channel 1 or 2 accepts any non-empty prefix of the readable source bytes and
  emits one `writeEv` per byte. Channels other than 0 are write-only by assumption (piped
  stdio).
* An output buffer that is not fully writable is `unmodeled`, except where Linux answers
  `-EFAULT` deterministically (the first byte is unmapped).
* Writes to sockets are `unmodeled` in LPS too.

## x86-64

Every helper that consults `access_ok` takes the predicate as its first argument (`…With ok`):
LPS's own definitions are the instances at `accessOkb` (riscv64 Sv48, `State.v:1344`), and
`readSpecX86`/`writeSpecX86` are the instances at `accessOkbX86`
(`arch/x86/include/asm/uaccess_64.h`, see `Silmaril.Process.LPS.Uaccess`). Nothing else in
`read`/`write` differs on x86-64: `MAX_RW_COUNT` is `INT_MAX & PAGE_MASK` on both, and the
descriptor kinds and their tests are architecture-independent.

## Audit (lane fs-io)

Every arm of `read_spec` and `write_spec` was compared with LPS `Sys/Fs/ReadWrite.v:345-725`
and `:909-1260`, mode by mode: regular files at an offset (read-only, write-only, append,
read-write), stdin/stdout/stderr channels (short transfers, EOF, the zero count), pipes (both
ends, empty with and without a writer, room, `SIGPIPE` decline), sockets (connected, reset,
FIN/RST/timeout, never connected), `/dev/null`, `/dev/urandom`, directories, `EFAULT` on the
first byte, `EBADF`, the `MAX_RW_COUNT` clamp and the `rw_bytes_max` gate. LPS's `FdEntry`
has no eventfd or timerfd kind at this commit (`State.v:2611`), so neither has an arm. No
divergence was found; the change is the `access_ok` parametrisation above.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys Fs

/-- LPS `Sys/Uaccess.v:442` `access_ok_zero`, over the `access_ok` predicate `ok`. -/
def accessOkZeroWith (ok : Word → Int → Bool) (buf count : Word) (k : Sys SyscallEffect) :
    Sys SyscallEffect :=
  if ok buf (uns count) then k else errRet EFAULT

theorem accessOkZeroWith_accessOkb : accessOkZeroWith accessOkb = accessOkZero := rfl

/-- LPS `Sys/Uaccess.v:397` `modeled_rw_range`, over the `access_ok` predicate `ok`. -/
def modeledRwRangeWith (ok : Word → Int → Bool) (buf count : Word) : Bool :=
  modeledRwCount count || ok buf (uns count)

theorem modeledRwRangeWith_accessOkb : modeledRwRangeWith accessOkb = modeledRwRange := rfl

/-- LPS `Sys/Fs/ReadWrite.v:34` `modeled_zero_fill`. -/
def modeledZeroFill (endpoint : Int) (data : List Byte) : Bool :=
  decide (endpoint - data.length ≤ rwBytesMax)

/-- LPS `Sys/Fs/ReadWrite.v:44` `modeled_file_gap`. -/
def modeledFileGap (data : List Byte) (off : Word) (bs : List Byte) : Bool :=
  match bs with
  | [] => true
  | _ :: _ => modeledZeroFill (uns off) data

/-- LPS `Sys/Fs/ReadWrite.v:90` `append_new_pos`. -/
def appendNewPos (data bs : List Byte) (off : Word) : Word :=
  match bs with
  | [] => off
  | _ :: _ => lenWord data + lenWord bs

/-- LPS `Sys/Fs/ReadWrite.v:233` `rw_pos_einvalb`. -/
def rwPosEinvalb (off : Word) (count : Int) : Bool := decide (2 ^ 63 - 1 < uns off + count)

/-- LPS `Sys/Fs/ReadWrite.v:257` `socket_pending_error`: report a pending error once and
leave the socket reset. -/
def socketPendingErrorWith (ok : Word → Int → Bool) (e : Int) (fd : Word) (peer : PeerAddr)
    (ch buf count : Word) (m : Model) : Sys SyscallEffect :=
  accessOkZeroWith ok buf count do
    modify (·.withFds (fdInsert m.fds fd (.socket (.reset peer ch))))
    errRet e

/-- LPS `Sys/Fs/ReadWrite.v:321` `read_urandom`: `/dev/urandom` delivers the full request
from the input stream `in_urandom`. -/
def readUrandom (buf count : Word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  if wIs0 count then retOnly 0
  else match readBytesMap i.wmem buf 1 with
    | none => errRet EFAULT
    | some _ =>
      let r := m.urandom.takeZ (rwCountClamp count)
      if (r.1.length : Int) ≠ rwCountClamp count then unmodeled
      else match readBytesMap i.wmem buf (lenWord r.1) with
        | none => unmodeled
        | some _ => do
          modify (·.withUrandom r.2)
          Sys.pure (mkEffect (lenWord r.1) [(buf, r.1)] [])

/-- Reading a regular file (LPS `Sys/Fs/ReadWrite.v:543-635`, shared by `FdFile` and
`FdFileRW`): deliver the bytes from the offset, advancing it. -/
def readFileWith (ok : Word → Int → Bool) (fd buf count : Word) (i : SyscallInput) (m : Model)
    (p : Path) (off : Word) (reentry : Path → Word → FdEntry) : Sys SyscallEffect :=
  if !ok buf (uns count) then errRet EFAULT
  else match Fs.lookup m.fs p with
    | none => unmodeled
    | some data =>
      let bs := fileRead data off (zw (rwCountClamp count))
      match readBytesMap i.wmem buf (lenWord bs) with
      | none =>
        match readBytesMap i.wmem buf 1 with
        | none => errRet EFAULT
        | some _ => unmodeled
      | some _ => do
        modify (·.withFds (fdInsert m.fds fd (reentry p (off + lenWord bs))))
        Sys.pure (mkEffect (lenWord bs) (deliveredWrites buf bs) [])

/-- LPS `Sys/Fs/ReadWrite.v:345` `read_spec`, over the `access_ok` predicate `ok`. -/
def readSpecWith (ok : Word → Int → Bool) (fd buf count : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.fileW _ _) => errRet EBADF
  | some (.fileA _ _) => errRet EBADF
  | some (.channel ch) =>
    if !wIs0 ch then errRet EBADF
    else if !ok buf (uns count) then errRet EFAULT
    else if wIs0 count then retOnly 0
    else if m.stdin.atEof then retOnly 0
    else match readBytesMap i.wmem buf 1 with
      | none => errRet EFAULT
      | some _ =>
        match readBytesMap i.wmem buf (lenWord (m.stdin.takeZ (rwCountClamp count)).1) with
        | none => unmodeled
        | some _ => do
          let bs ← Sys.choose fun bs : List Byte =>
            1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp count ∧
              (m.stdin.take bs.length).1 = bs ∧ (readBytesMap i.wmem buf (lenWord bs)).isSome
          modify (·.withStdin (m.stdin.take bs.length).2)
          emit (bs.map (.readEv ch))
          Sys.pure (mkEffect (lenWord bs) [(buf, bs)] [])
  | some (.devNull rd _) =>
    if !rd then errRet EBADF
    else if !ok buf (uns count) then errRet EFAULT
    else retOnly 0
  | some .urandom =>
    if !ok buf (uns count) then errRet EFAULT else readUrandom buf count i m
  | some .dir =>
    if !ok buf (uns count) then errRet EFAULT else errRet EISDIR
  | some (.socket sk) =>
    if !modeledRwRangeWith ok buf count then unmodeled
    else if wIs0 count then accessOkZeroWith ok buf count (retOnly 0)
    else match sk with
      | .connected peer ch rx =>
        match rx.item 0 with
        | .inr .fin => accessOkZeroWith ok buf count (retOnly 0)
        | .inr .rst => socketPendingErrorWith ok ECONNRESET fd peer ch buf count m
        | .inr .timedOut => socketPendingErrorWith ok ETIMEDOUT fd peer ch buf count m
        | .inl _ =>
          match readBytesMap i.wmem buf 1 with
          | none => errRet EFAULT
          | some _ =>
            match readBytesMap i.wmem buf (lenWord (rx.takeZ (rwCountClamp count)).1) with
            | none => unmodeled
            | some _ => do
              let bs ← Sys.choose fun bs : List Byte =>
                1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp count ∧
                  (rx.take bs.length).1 = bs ∧ (readBytesMap i.wmem buf (lenWord bs)).isSome
              modify (·.withFds
                (fdInsert m.fds fd (.socket (.connected peer ch (rx.take bs.length).2))))
              emit (bs.map (.readEv ch))
              Sys.pure (mkEffect (lenWord bs) [(buf, bs)] [])
      | .reset _ _ => accessOkZeroWith ok buf count (retOnly 0)
      | _ => accessOkZeroWith ok buf count (errRet ENOTCONN)
  | some (.file p off) => readFileWith ok fd buf count i m p off .file
  | some (.fileRW p off) => readFileWith ok fd buf count i m p off .fileRW
  | some (.pipe id w) =>
    if w then errRet EBADF
    else if !modeledRwRangeWith ok buf count then unmodeled
    else if wIs0 count then accessOkZeroWith ok buf count (retOnly 0)
    else match pipeLookup m.pipes id with
      | none => unmodeled
      | some ([], _) =>
        if pipeEndLive m.fds id true then unmodeled
        else accessOkZeroWith ok buf count (retOnly 0)
      | some (q@(_ :: _), used) =>
        let del := pipeTake q (rwCountClamp count)
        match readBytesMap i.wmem buf (lenWord del) with
        | none =>
          match readBytesMap i.wmem buf 1 with
          | none => errRet EFAULT
          | some _ => unmodeled
        | some _ => do
          modify (·.withPipes (pipeInsert m.pipes id (pipeConsume (q, used) del.length)))
          Sys.pure (mkEffect (lenWord del) (deliveredWrites buf del) [])

/-- LPS `Sys/Fs/ReadWrite.v:345` `read_spec` (riscv64 `access_ok`). -/
def readSpec (fd buf count : Word) : Sys SyscallEffect := readSpecWith accessOkb fd buf count

/-- x86-64 `read` (number 0): LPS `read_spec` with x86-64 `access_ok`. -/
def readSpecX86 (fd buf count : Word) : Sys SyscallEffect :=
  readSpecWith accessOkbX86 fd buf count

/-- LPS `Sys/Fs/ReadWrite.v:859` `write_range_gate`. -/
def writeRangeGateWith (ok : Word → Int → Bool) (buf count : Word) (k : Sys SyscallEffect) :
    Sys SyscallEffect :=
  if !modeledRwRangeWith ok buf count then unmodeled else k

/-- LPS `Sys/Fs/ReadWrite.v:859` `write_range_gate` (riscv64 `access_ok`). -/
def writeRangeGate (buf count : Word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  writeRangeGateWith accessOkb buf count k

/-- LPS `Sys/Fs/ReadWrite.v:869` `write_ledger`. -/
def writeLedger (buf count : Word) (bs : List Byte) : Sys SyscallEffect :=
  if wIs0 count then retOnly (lenWord bs)
  else recordCopyins [(buf, bs.length)] (retOnly (lenWord bs))

/-- LPS `Sys/Fs/ReadWrite.v:895` `write_file_tail`. -/
def writeFileTailWith (ok : Word → Int → Bool) (mp : Word → Option Byte) (buf count : Word)
    (place : List Byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  let bs := writeSource mp buf count
  if !wIs0 count && bs.length == 0 then errRet EFAULT
  else
    let deliver :=
      match place bs with
      | none => unmodeled
      | some upd => upd (writeLedger buf count bs)
    if wIs0 count then accessOkZeroWith ok buf count deliver else deliver

/-- LPS `Sys/Fs/ReadWrite.v:895` `write_file_tail` (riscv64 `access_ok`). -/
def writeFileTail (mp : Word → Option Byte) (buf count : Word)
    (place : List Byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  writeFileTailWith accessOkb mp buf count place

/-- Writing a regular file at its offset (LPS `Sys/Fs/ReadWrite.v:1017-1072`, shared by
`FdFileW` and `FdFileRW`). -/
def writeFileWith (ok : Word → Int → Bool) (fd buf count : Word) (i : SyscallInput) (m : Model)
    (p : Path) (off : Word) (reentry : Path → Word → FdEntry) : Sys SyscallEffect :=
  writeRangeGateWith ok buf count
    (writeFileTailWith ok i.mem buf count fun bs =>
      match Fs.lookup m.fs p with
      | none => none
      | some data =>
        if !modeledFileGap data off bs then none
        else some fun k => do
          modify (·.withFs (Fs.set m.fs p (fileWrite data off bs)))
          modify (·.withFds (fdInsert m.fds fd (reentry p (off + lenWord bs))))
          k)

/-- LPS `Sys/Fs/ReadWrite.v:909` `write_spec`, over the `access_ok` predicate `ok`. -/
def writeSpecWith (ok : Word → Int → Bool) (fd buf count : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.file _ _) => errRet EBADF
  | some .urandom => errRet EBADF
  | some (.devNull _ wr) =>
    if !wr then errRet EBADF
    else writeRangeGateWith ok buf count (accessOkZeroWith ok buf count (retOnly (zw (rwCountClamp count))))
  | some (.channel ch) =>
    if wIs0 ch then errRet EBADF
    else if !modeledRwRangeWith ok buf count then unmodeled
    else if wIs0 count then accessOkZeroWith ok buf count (retOnly 0)
    else
      let bs := writeSource i.mem buf count
      if bs.length == 0 then errRet EFAULT
      else do
        let ds ← Sys.choose fun ds : List Byte =>
          1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp count ∧ ds = bs.take ds.length
        emit (ds.map (.writeEv ch))
        recordCopyins [(buf, ds.length)] (retOnly (lenWord ds))
  | some .dir => errRet EBADF
  | some (.socket _) => unmodeled
  | some (.fileW p off) => writeFileWith ok fd buf count i m p off .fileW
  | some (.fileRW p off) => writeFileWith ok fd buf count i m p off .fileRW
  | some (.fileA p off) =>
    writeRangeGateWith ok buf count
      (if !ok buf (uns count) then errRet EFAULT
       else if rwPosEinvalb off (uns count) then errRet EINVAL
       else writeFileTailWith ok i.mem buf count fun bs =>
         match Fs.lookup m.fs p with
         | none => none
         | some data => some fun k => do
           modify (·.withFs (Fs.set m.fs p (fileWrite data (lenWord data) bs)))
           modify (·.withFds (fdInsert m.fds fd (.fileA p (appendNewPos data bs off))))
           k)
  | some (.pipe id w) =>
    if !w then errRet EBADF
    else if !modeledRwRangeWith ok buf count then unmodeled
    else if wIs0 count then accessOkZeroWith ok buf count (retOnly 0)
    else if !pipeEndLive m.fds id false then unmodeled
    else match pipeLookup m.pipes id with
      | none => unmodeled
      | some st =>
        if !pipeWriteRoom st (uns count) then unmodeled
        else
          let bs := writeSource i.mem buf count
          if bs.length != wordToNat count then unmodeled
          else do
            modify (·.withPipes (pipeInsert m.pipes id (pipeAppend st bs)))
            recordCopyins [(buf, bs.length)] (retOnly count)

/-- LPS `Sys/Fs/ReadWrite.v:909` `write_spec` (riscv64 `access_ok`). -/
def writeSpec (fd buf count : Word) : Sys SyscallEffect := writeSpecWith accessOkb fd buf count

/-- x86-64 `write` (number 1): LPS `write_spec` with x86-64 `access_ok`. -/
def writeSpecX86 (fd buf count : Word) : Sys SyscallEffect :=
  writeSpecWith accessOkbX86 fd buf count

end Silmaril.Process.LPS
