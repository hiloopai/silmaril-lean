module

public import Silmaril.Process.LPS.Sys.SocketCore
public import Silmaril.Process.LPS.Arm
public import Silmaril.Process.LPS.Sys.FsIo.ReadWrite

/-!
# LPS in Lean: the socket family

Translation of the second half of LPS `Sys/Net/Socket.v` (upstream commit `f1006fe8`) and
the socket rows of `Sys/SyscallTable.v`; the first half is
`Silmaril.Process.LPS.Sys.SocketCore`.

* `sendto` and `sendmsg` (`sendto_spec`, `sendmsg_spec`): modelled only with the flag word
  exactly `MSG_NOSIGNAL` (so no `SIGPIPE` can be raised) and no destination address. A send
  on a connection delivers any non-empty prefix (short sends), emitting one `writeEv` per
  byte on the connection's channel; a pending reset or timeout is reported once; every
  no-connection state is `EPIPE`. `sendto` judges its buffer before its descriptor,
  `sendmsg` its descriptor before its header;
* `socketpair` (`socketpair_spec`): AF_INET always fails with `EOPNOTSUPP` after writing
  the two reserved descriptor numbers;
* `recvfrom` and `recvmsg` (`recvfrom_spec`, `recvmsg_spec`): the descriptor answers
  (`EBADF`, `ENOTSOCK`) in their two different orders; on a socket both are `unmodeled`, as
  in LPS (reading a socket is modelled through `read`).

## The tables

`socketLpsArms` are the sixteen LPS arms with their asm-generic numbers and the argument
narrowings of `Sys/SyscallTable.v:104-126`. `socketX86Arms` are the same arms with the
x86-64 numbers of `arch/x86/entry/syscalls/syscall_64.tbl` (`socket` 41, `connect` 42,
`accept` 43, `sendto` 44, `recvfrom` 45, `sendmsg` 46, `recvmsg` 47, `shutdown` 48, `bind`
49, `listen` 50, `getsockname` 51, `getpeername` 52, `socketpair` 53, `setsockopt` 54,
`getsockopt` 55, `accept4` 288). The argument order of every one of these calls is the
same on x86-64.

## x86-64 differences

The structures these calls read or write have the generic LP64 layout on x86-64 too:
`struct user_msghdr` is 56 bytes (`msg_name` 0, `msg_namelen` 8, `msg_iov` 16,
`msg_iovlen` 24, `msg_control` 32, `msg_controllen` 40, `msg_flags` 48), `struct iovec` 16
bytes, `struct sockaddr_in` 16 bytes, the `socketpair` vector two little-endian `int`s.
`struct cmsghdr` (16 bytes on LP64) is never parsed: a non-zero `msg_controllen` is
`unmodeled` on both. `MSG_NOSIGNAL` (`0x4000`) is from `include/linux/socket.h` on both;
`MSG_CMSG_COMPAT` depends on `CONFIG_COMPAT` (`IA32_EMULATION` on x86-64) exactly as on
riscv64, so the decline stays.

What differs is `access_ok` (see `Uaccess`): x86-64 refuses ranges reaching past
`TASK_SIZE_MAX = 2^47 - 4096`, LPS's riscv64 form accepts up to `2^47`. Four arms consult it,
and their x86-64 forms use `accessOkbX86`:

* `sendmsg` (`sendmsgSpecX86`): `__import_iovec`'s `access_ok` on the descriptor array and on
  every segment. LPS's `sendmsg_spec` omits this check on riscv64 too (it reads the
  descriptors with `copy_iovecs_aux`), so a segment base Linux refuses with `-EFAULT` is
  accepted there and the readable prefix sent. The riscv64 table keeps LPS's arm for literal
  agreement; `sendmsgSpecLinux` is the riscv64 arm with Linux's import, and
  `SoundReference.soundSyscallSpec` the sound reference table that statements should use.

* `sendto` (`sendtoSpecX86`) and `recvfrom` (`recvfromSpecX86`): `import_ubuf`'s
  `access_ok`, decided before the descriptor;
* `socketpair` (`socketpairSpecX86`): the two `put_user` stores. On x86-64 `put_user` checks
  the pointer against `USER_PTR_MAX` (`check_range` in `arch/x86/lib/putuser.S`) and the
  store itself faults in the never-mapped guard page at `TASK_SIZE_MAX`; a 4-byte store
  faults as a whole. So "the first store is refused" is `!accessOkbX86 sv 4` and "both
  stores land" is `accessOkbX86 sv 8` with the 8 bytes writable, as LPS has it for riscv64
  (`accessOkbX86_both_stores` in the checks is LPS's `access_okb_both_stores` for x86-64).

**Open x86-64 gap: the `access_ok` verdict depends on the kernel version.** `accessOkbX86` is
the v6.13+ form (`USER_PTR_MAX = TASK_SIZE_MAX`, `arch/x86/kernel/cpu/common.c`). LPS's
window is v6.10-v6.15, and in it x86-64's `valid_user_address` changed twice: v6.10 and v6.11
accept any non-wrapping range whose end is below `2^63` (`(long)(x) >= 0`), v6.12 has
`USER_PTR_MAX = TASK_SIZE_MAX - 1`, and LA57 machines have `TASK_SIZE_MAX = 2^56 - 4096`.
(Checked against the upstream tags: `arch/x86/include/asm/uaccess_64.h` at v6.10 and v6.11
defines `valid_user_address(x)` as `((__force long)(x) >= 0)`, at v6.12 and v6.13 as
`<= runtime_const_ptr(USER_PTR_MAX)`; `arch/x86/kernel/cpu/common.c` sets `USER_PTR_MAX` to
`TASK_SIZE_MAX-1` at v6.12 and v6.12.1 and to `TASK_SIZE_MAX` at v6.13. `__access_ok` with a
non-constant size checks `valid_user_address(ptr + size)` and no wraparound on every one.) So
for a `sendto`/`recvfrom` buffer whose end lies in `[TASK_SIZE_MAX, 2^63)` the deterministic
`EFAULT` of `sendtoSpecX86`/`recvfromSpecX86` is not what a v6.10/v6.11 kernel answers
(`recvfrom(-1, 2^47 - 16, 16)` is `EBADF` there), and at an end of exactly `TASK_SIZE_MAX` a
v6.12 kernel refuses what `accessOkbX86` accepts. The sound repair is a three-valued verdict
in the shared `Uaccess` layer (accept where every version and paging mode accepts, refuse
where every one refuses, `unmodeled` in between); it is recorded for the x86 lane, which
owns `accessOkZeroX86`, rather than patched here for one family. `put_user` (`socketpair`)
is not affected: its store faults on every version once it leaves the mapped user range.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! ## The send path -/

/-- LPS `Sys/Net/Socket.v:1541` `MSG_NOSIGNAL` (`include/linux/socket.h`; the same on
x86-64). -/
def MSG_NOSIGNAL : Int := 0x4000

/-- LPS `Sys/Net/Socket.v:1547` `sendflags32`: `flags` is an `unsigned int`. -/
def sendflags32 (fl : Word) : Word := abiLow32 fl

/-- LPS `Sys/Net/Socket.v:1561` `send_flags_modeled`: the flag word is exactly
`MSG_NOSIGNAL`. -/
def sendFlagsModeled (fl : Word) : Bool := uns (sendflags32 fl) == MSG_NOSIGNAL

/-- LPS `Sys/Net/Socket.v:1567` `SendState`. -/
inductive SendState where
  /-- `ESTABLISHED` or `CLOSE_WAIT`: the send goes out. -/
  | goes (chan : Word)
  /-- One pending peer error. -/
  | err (e : Int) (peer : PeerAddr) (chan : Word)
  /-- No connection: `EPIPE`. -/
  | dead

/-- LPS `Sys/Net/Socket.v:1614` `send_state`. A consumed FIN (`CLOSE_WAIT`) still sends; a
fresh socket is `EPIPE` (TCP does not autobind on send). -/
def sendState : SockState → SendState
  | .connected peer ch rx =>
    match rx.item 0 with
    | .inr .rst => .err ECONNRESET peer ch
    | .inr .timedOut => .err ETIMEDOUT peer ch
    | .inr .fin => .goes ch
    | .inl _ => .goes ch
  | .reset _ _ => .dead
  | .bound => .dead
  | .listening => .dead
  | .fresh => .dead

/-- LPS `Sys/Net/Socket.v:1665` `send_bytes`: a zero-length request is 0, an unreadable
source `EFAULT`, otherwise any non-empty prefix of the source is sent. `pre` is what the call
has already copied in, `acc` the ranges of a delivered prefix. -/
def sendBytes (pre : List (Word × Nat)) (acc : Nat → List (Word × Nat)) (total : Word)
    (bs : List Byte) (ch : Word) : Sys SyscallEffect :=
  if wIs0 total then recordCopyins pre (retOnly 0)
  else if bs.length == 0 then recordCopyins pre (errRet EFAULT)
  else do
    let ds ← Sys.choose fun ds : List Byte =>
      1 ≤ (ds.length : Int) ∧ (ds.length : Int) ≤ uns total ∧ ds = bs.take ds.length
    emit (ds.map (.writeEv ch))
    recordCopyins (pre ++ acc ds.length) (retOnly (lenWord ds))

/-- LPS `Sys/Net/Socket.v:1682` `send_on_socket`: a pending error is consumed as a read
would consume it (`socket_pending_error`), leaving the socket reset. -/
def sendOnSocket (pre : List (Word × Nat)) (acc : Nat → List (Word × Nat)) (fd : Word)
    (sk : SockState) (total : Word) (bs : List Byte) (m : Model) : Sys SyscallEffect :=
  match sendState sk with
  | .dead => recordCopyins pre (errRet EPIPE)
  | .err e peer ch =>
    recordCopyins pre (do
      setFds (fdInsert m.fds fd (.socket (.reset peer ch)))
      errRet e)
  | .goes ch => sendBytes pre acc total bs ch

/-- LPS `Sys/Net/Socket.v:1750` `sendto_spec`, over the `access_ok_zero` gate of
`import_ubuf`: the model gates (flags, destination address, transfer size) first, then the
buffer range, then the descriptor. -/
def sendtoSpecWith (aok : Word → Word → Sys SyscallEffect → Sys SyscallEffect)
    (fd buf count flags addrp _addrlen : Word) : Sys SyscallEffect :=
  if !sendFlagsModeled flags then unmodeled
  else if !wIs0 addrp then unmodeled
  else if !modeledRwCount count then unmodeled
  else do
    let i ← input
    let m ← getModel
    aok buf count
      (match fdLookup m.fds fd with
       | none => errRet EBADF
       | some (.socket sk) =>
         sendOnSocket [] (fun n => [(buf, n)]) fd sk count (readableBytes i.mem buf count) m
       | some _ => errRet ENOTSOCK)

/-- LPS `Sys/Net/Socket.v:1750` `sendto_spec`. -/
def sendtoSpec (fd buf count flags addrp addrlen : Word) : Sys SyscallEffect :=
  sendtoSpecWith accessOkZero fd buf count flags addrp addrlen

/-- x86-64 form of `sendto_spec`: `import_ubuf`'s `access_ok` is x86-64's. -/
def sendtoSpecX86 (fd buf count flags addrp addrlen : Word) : Sys SyscallEffect :=
  sendtoSpecWith accessOkZeroX86 fd buf count flags addrp addrlen

/-- LPS `Sys/Net/Socket.v:1789` `MSGHDR_SIZE`: `struct user_msghdr` on LP64 (x86-64
included). -/
def MSGHDR_SIZE : Int := 56

/-- LPS `Sys/Net/Socket.v:1855` `sendmsg_spec`. The flag word is the syscall argument, never
`msg_flags`. The descriptor is resolved before the 56-byte header is copied; a non-NULL
`msg_name`, an `msg_iovlen` in the heap-backed range (over `UIO_FASTIOV`) and a non-zero
`msg_controllen` are `unmodeled`; `msg_iovlen` over `UIO_MAXIOV` is `EMSGSIZE`. The ledger
is the header, then the descriptors walked, then the payload prefix sent.

`sendmsgSpecWith` is parametrised by the iovec import `imp` and the descriptor ranges it
reads `acc`. LPS's `sendmsg_spec` (`sendmsgSpec`) uses `copy_iovecs_aux`, which reads the
descriptors without `access_ok` on the array or on any segment base. Linux's
`copy_msghdr_from_user` goes through `import_iovec`/`__import_iovec`, which does both (and
answers `-EFAULT` before sending anything); `sendmsgSpecX86` uses that import
(`importIovecsX86`). -/
def sendmsgSpecWith (imp : (Word → Option Byte) → Word → Word → IovImport)
    (acc : (Word → Option Byte) → Word → Word → List (Word × Nat))
    (fd msgp flags : Word) : Sys SyscallEffect :=
  if !sendFlagsModeled flags then unmodeled
  else do
    let i ← input
    let m ← getModel
    match fdLookup m.fds fd with
    | none => errRet EBADF
    | some (.channel _) | some (.file _ _) | some (.fileW _ _) | some (.fileA _ _)
    | some (.fileRW _ _) | some .dir | some (.pipe _ _) | some (.devNull _ _)
    | some .urandom => errRet ENOTSOCK
    | some (.socket sk) =>
      match readBytesMap i.mem msgp (zw MSGHDR_SIZE) with
      | none => errRet EFAULT
      | some _ =>
        let hdr : List (Word × Nat) := [(msgp, MSGHDR_SIZE.toNat)]
        match readU64 i.mem msgp, readU64 i.mem (msgp + 8), readU64 i.mem (msgp + 16),
            readU64 i.mem (msgp + 24), readU64 i.mem (msgp + 32),
            readU64 i.mem (msgp + 40) with
        | some name, some _namelen, some iov, some iovlen, some _ctl, some ctllen =>
          let walked := acc i.mem iov iovlen
          if !wIs0 name then unmodeled
          else if IOV_MAX < uns iovlen then recordCopyins hdr (errRet EMSGSIZE)
          else if UIO_FASTIOV < uns iovlen then unmodeled
          else
            match imp i.mem iov iovlen with
            | .fault => recordCopyins (hdr ++ walked) (errRet EFAULT)
            | .inval => recordCopyins (hdr ++ walked) (errRet EINVAL)
            | .ok iovs0 =>
              if !wIs0 ctllen then unmodeled
              else if ¬(iovsTotal (capIovecs iovs0) ≤ rwBytesMax) then unmodeled
              else
                sendOnSocket (hdr ++ walked) (fun n => iovPrefixAccesses (capIovecs iovs0) n)
                  fd sk (zw (iovsTotal (capIovecs iovs0))) (writevGathered i.mem iovs0) m
        | _, _, _, _, _, _ => recordCopyins hdr (errRet EFAULT)

/-- LPS `Sys/Net/Socket.v:1855` `sendmsg_spec`: `copy_iovecs_aux`, no `access_ok` on the
descriptor array or the segment bases. This is a gap against Linux's `__import_iovec` on
riscv64 too; it is kept here for literal agreement with LPS. The riscv64 variants that close
it are `sendmsgSpecLinux` (exact) and `SoundReference.sendmsgSpecSound` (LPS's arm, `unmodeled`
wherever the two imports differ), related to this one in `Silmaril.Process.LPS.SoundReference`. -/
def sendmsgSpec (fd msgp flags : Word) : Sys SyscallEffect :=
  sendmsgSpecWith (fun mp a n => copyIovecsAux mp a (wordToNat n))
    (fun mp a n => copyIovecsAccesses mp a (wordToNat n)) fd msgp flags

/-- x86-64 `sendmsg` (number 46): the iovecs are imported as Linux's `__import_iovec` does,
with x86-64 `access_ok` on the descriptor array and on every segment (capped for a single
segment, uncapped otherwise), so a segment base past `TASK_SIZE_MAX` is `-EFAULT` with nothing
sent. -/
def sendmsgSpecX86 (fd msgp flags : Word) : Sys SyscallEffect :=
  sendmsgSpecWith importIovecsX86 importIovecsAccessesX86 fd msgp flags

/-- riscv64 `sendmsg` as Linux runs it: the iovecs are imported through `__import_iovec` with
the Sv48 `access_ok` (LPS's own `import_iovecs`, the import its `readv`/`writev` use), so a
segment base Linux refuses is `-EFAULT` with nothing sent. -/
def sendmsgSpecLinux (fd msgp flags : Word) : Sys SyscallEffect :=
  sendmsgSpecWith importIovecs importIovecsAccesses fd msgp flags

/-! ## `recvfrom` (207) and `recvmsg` (212) -/

/-- LPS `Sys/Net/Socket.v:2002` `sockfd_lookup_errno`: `EBADF`, `ENOTSOCK`, or `none` for a
socket. -/
def sockfdLookupErrno (fds : List (Word × FdEntry)) (fd : Word) : Option Int :=
  match fdLookup fds fd with
  | none => some EBADF
  | some (.channel _) => some ENOTSOCK
  | some (.file _ _) => some ENOTSOCK
  | some (.fileW _ _) => some ENOTSOCK
  | some (.fileA _ _) => some ENOTSOCK
  | some (.fileRW _ _) => some ENOTSOCK
  | some .dir => some ENOTSOCK
  | some (.pipe _ _) => some ENOTSOCK
  | some (.devNull _ _) => some ENOTSOCK
  | some .urandom => some ENOTSOCK
  | some (.socket _) => none

/-- LPS `Sys/Net/Socket.v:2032` `recv_fd_answer`: the errno, or the decline a socket
takes. -/
def recvFdAnswer (fds : List (Word × FdEntry)) (fd : Word) : Sys SyscallEffect :=
  match sockfdLookupErrno fds fd with
  | some e => errRet e
  | none => unmodeled

/-- LPS `Sys/Net/Socket.v:2392` `recvfrom_spec`, over `import_ubuf`'s `access_ok` gate: the
buffer is validated before the descriptor. (LPS also binds the input, which it does not
use.) -/
def recvfromSpecWith (aok : Word → Word → Sys SyscallEffect → Sys SyscallEffect)
    (fd buf size : Word) : Sys SyscallEffect :=
  if !modeledRwCount size then unmodeled
  else do
    let m ← getModel
    aok buf size (recvFdAnswer m.fds fd)

/-- LPS `Sys/Net/Socket.v:2392` `recvfrom_spec`. -/
def recvfromSpec (fd buf size : Word) : Sys SyscallEffect := recvfromSpecWith accessOkZero fd buf size

/-- x86-64 form of `recvfrom_spec`. -/
def recvfromSpecX86 (fd buf size : Word) : Sys SyscallEffect :=
  recvfromSpecWith accessOkZeroX86 fd buf size

/-- LPS `Sys/Net/Socket.v:2443` `recvmsg_spec`: `MSG_CMSG_COMPAT` depends on the kernel
build and is `unmodeled`; the descriptor is resolved before the header is read. -/
def recvmsgSpec (fd flags : Word) : Sys SyscallEffect :=
  if zland (uns (abiLow32 flags)) MSG_CMSG_COMPAT ≠ 0 then unmodeled
  else do
    let m ← getModel
    recvFdAnswer m.fds fd

/-! ## `socketpair` (199) -/

/-- LPS `Sys/Net/Socket.v:2047` `socketpair_flags_ok`. -/
def socketpairFlagsOk (type : Word) : Bool :=
  zldiff (zldiff (uns (abiLow32 type)) SOCK_TYPE_MASK) (zlor SOCK_CLOEXEC SOCK_NONBLOCK) == 0

/-- LPS `Sys/Net/Socket.v:2053` `socketpair_base_type`. -/
def socketpairBaseType (type : Word) : Int := zland (uns (abiLow32 type)) SOCK_TYPE_MASK

/-- LPS `Sys/Net/Socket.v:2075` `socketpair_modeled_b`: AF_INET, `SOCK_STREAM` or
`SOCK_DGRAM`, protocol 0. -/
def socketpairModeledB (family type protocol : Word) : Bool :=
  uns (abiLow32 family) == AF_INET &&
    (socketpairBaseType type == SOCK_STREAM || socketpairBaseType type == SOCK_DGRAM) &&
    uns (abiLow32 protocol) == 0

/-- LPS `Sys/Net/Socket.v:2087` `socketpair_fds`: the two reserved descriptors. -/
def socketpairFds (fds : List (Word × FdEntry)) : Option (Word × Word) :=
  match fdLookup fds (allocFd fds), fdLookup fds (allocFd2 fds) with
  | none, none => some (allocFd fds, allocFd2 fds)
  | _, _ => none

/-- LPS `Sys/Net/Socket.v:2098` `socketpair_writes`: two 4-byte `put_user` stores. -/
def socketpairWrites (sv fd1 fd2 : Word) : List (Word × List Byte) :=
  [(sv, wordLe4 fd1), (sv + 4, wordLe4 fd2)]

/-- LPS `Sys/Net/Socket.v:2108` `socketpair_reserve_errnos`. -/
def socketpairReserveErrnos : List Int := [EMFILE, ENOMEM]

/-- LPS `Sys/Net/Socket.v:2135` `socketpair_create_errnos`: after both writes. -/
def socketpairCreateErrnos : List Int := [ENFILE, ENOMEM]

/-- LPS `Sys/Net/Socket.v:2140` `socketpair_written`. -/
def socketpairWritten (sv fd1 fd2 : Word) : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom socketpairReserveErrnos; errRet e)
    (Sys.alt
      (do
        let e ← errnoFrom socketpairCreateErrnos
        Sys.pure (mkEffect (errnoRet e) (socketpairWrites sv fd1 fd2) []))
      (Sys.pure (mkEffect (errnoRet EOPNOTSUPP) (socketpairWrites sv fd1 fd2) [])))

/-- LPS `Sys/Net/Socket.v:2151` `socketpair_faulted`. -/
def socketpairFaulted : Sys SyscallEffect :=
  Sys.alt (do let e ← errnoFrom socketpairReserveErrnos; errRet e) (errRet EFAULT)

/-- LPS `Sys/Net/Socket.v:2242` `socketpair_dest_writable`, over the `access_ok`
predicate. -/
def socketpairDestWritableWith (ok : Word → Int → Bool) (mp : Word → Option Byte) (sv : Word) :
    Bool :=
  ok sv 8 && (readBytesMap mp sv 8).isSome

/-- LPS `Sys/Net/Socket.v:2287` `socketpair_spec`, over the `access_ok` predicate of the two
`put_user` stores. -/
def socketpairSpecWith (ok : Word → Int → Bool) (family type protocol sv : Word) :
    Sys SyscallEffect :=
  if !socketpairFlagsOk type then errRet EINVAL
  else if !socketpairModeledB family type protocol then unmodeled
  else do
    let i ← input
    let m ← getModel
    match socketpairFds m.fds with
    | none => unmodeled
    | some (fd1, fd2) =>
      if socketpairDestWritableWith ok i.wmem sv then socketpairWritten sv fd1 fd2
      else if !ok sv 4 then socketpairFaulted
      else unmodeled

/-- LPS `Sys/Net/Socket.v:2287` `socketpair_spec`. -/
def socketpairSpec (family type protocol sv : Word) : Sys SyscallEffect :=
  socketpairSpecWith accessOkb family type protocol sv

/-- x86-64 form of `socketpair_spec`. -/
def socketpairSpecX86 (family type protocol sv : Word) : Sys SyscallEffect :=
  socketpairSpecWith accessOkbX86 family type protocol sv

/-! ## The arms -/

/-- The socket arms of LPS `Sys/SyscallTable.v:104-126`, with the asm-generic numbers. -/
def socketLpsArms : List SpecArm :=
  [ arm 198 "socket" (fun i => socketSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 199 "socketpair" (fun i => socketpairSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 200 "bind" (fun i => bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 201 "listen" (fun i => listenSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 202 "accept" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0),
    arm 203 "connect" (fun i => connectSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 204 "getsockname" (fun i => getsocknameSpec (fd32 (i.arg 0))),
    arm 205 "getpeername" (fun i => getpeernameSpec (fd32 (i.arg 0))),
    arm 206 "sendto" (fun i =>
      sendtoSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 207 "recvfrom" (fun i => recvfromSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 208 "setsockopt" (fun i =>
      setsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (int32 (i.arg 4))),
    arm 209 "getsockopt" (fun i =>
      getsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (i.arg 4)),
    arm 210 "shutdown" (fun i => shutdownSpec (fd32 (i.arg 0)) (int32 (i.arg 1))),
    arm 211 "sendmsg" (fun i => sendmsgSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 212 "recvmsg" (fun i => recvmsgSpec (fd32 (i.arg 0)) (i.arg 2)),
    arm 242 "accept4" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)) ]

/-- The socket arms with the native x86-64 numbers (`syscall_64.tbl`). The arguments are
those of the LPS arms; `sendto`, `recvfrom` and `socketpair` take their x86-64 `access_ok`
forms. -/
def socketX86Arms : List SpecArm :=
  [ arm 41 "socket" (fun i => socketSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 53 "socketpair" (fun i => socketpairSpecX86 (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 49 "bind" (fun i => bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 50 "listen" (fun i => listenSpec (fd32 (i.arg 0)) (i.arg 1)),
    arm 43 "accept" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0),
    arm 42 "connect" (fun i => connectSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 51 "getsockname" (fun i => getsocknameSpec (fd32 (i.arg 0))),
    arm 52 "getpeername" (fun i => getpeernameSpec (fd32 (i.arg 0))),
    arm 44 "sendto" (fun i =>
      sendtoSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 45 "recvfrom" (fun i => recvfromSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 54 "setsockopt" (fun i =>
      setsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (int32 (i.arg 4))),
    arm 55 "getsockopt" (fun i =>
      getsockoptSpec (fd32 (i.arg 0)) (int32 (i.arg 1)) (i.arg 4)),
    arm 48 "shutdown" (fun i => shutdownSpec (fd32 (i.arg 0)) (int32 (i.arg 1))),
    arm 46 "sendmsg" (fun i => sendmsgSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
    arm 47 "recvmsg" (fun i => recvmsgSpec (fd32 (i.arg 0)) (i.arg 2)),
    arm 288 "accept4" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3)) ]

end Silmaril.Process.LPS
