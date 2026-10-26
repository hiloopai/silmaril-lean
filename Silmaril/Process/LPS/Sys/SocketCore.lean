module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.MonadExt
public import Silmaril.Process.LPS.Sys.FsIo.File

/-!
# LPS in Lean: sockets, connection set-up, options and addresses

Translation of the first half of LPS `Sys/Net/Socket.v` (upstream commit `f1006fe8`), the
specification of Linux `net/socket.c` for AF_INET stream sockets:

* `socket` (`socket_spec`): only `AF_INET`/`SOCK_STREAM` with protocol 0 or `IPPROTO_TCP`
  succeeds; the validation order of `__sys_socket_create`, `__sock_create` and
  `inet_create` is kept; `SOCK_NONBLOCK`, other families and other AF_INET types are
  `unmodeled`; the success path keeps the injected `ENOMEM`/`EMFILE`/`ENFILE` live;
* `bind` (`bind_spec`): only `INADDR_ANY` on port 0; the injected `EADDRINUSE` stays live;
* `listen` (`listen_spec`): listen without bind autobinds (injected `EADDRINUSE`);
* `accept`/`accept4` (`accept4_spec`): a listening socket takes the next connection of the
  environment's queue `IoState.net`, reported on trace channel `3 + connIx`; a non-NULL
  address argument and `SOCK_NONBLOCK` are `unmodeled`;
* `connect` (`connect_spec`): the address checks are answered, the connection attempt itself
  is `unmodeled` (the environment decides it);
* `getsockname`, `getpeername`, `setsockopt`, `getsockopt`, `shutdown`: the descriptor
  verdict (`sock_fd`) and the few answers that need no option table and no address export.

The send and receive paths, `socketpair` and the syscall-table arms are in
`Silmaril.Process.LPS.Sys.Socket`.

## x86-64

Nothing in this module depends on the architecture. The structures read here (`struct
sockaddr_in`, 16 bytes: `sin_family` host order at 0, `sin_port` big-endian at 2,
`sin_addr` big-endian at 4; `sockaddr_storage`, 128 bytes; the `int` at `optlen`) have the
same layout on x86-64, which is also little-endian; the `SOCK_*`, `AF_*`, `IPPROTO_*`,
`SOL_SOCKET` and `SHUT_*` constants are the generic ones on both (see `Uapi`). The user
copies (`move_addr_to_kernel`, the `optlen` read) are `read_bytes_map` as in LPS, which is
exact on both architectures as long as nothing at or above the user-space limit is mapped
(on x86-64 the guard page below `2^47`; see `Machines/X86.lean`).

The helpers of other LPS files it needs are the shared ones: `set_fds` (`Monad.v`) is
`Sys.setFds` of `MonadExt`, `lowest_fd` (`Sys/Fs/File.v`) and `Z.ldiff` are `lowestFd` and
`zldiff` of `Sys/FsIo/File`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys


/-! ## Injected failures and connection channels -/

/-- LPS `Sys/Net/Socket.v:35` `socket_errnos`: descriptor-table, file-table and allocation
failures the model does not decide. -/
def socketErrnos : List Int := [ENOMEM, EMFILE, ENFILE]
/-- LPS `Sys/Net/Socket.v:36` `accept_errnos`. -/
def acceptErrnos : List Int := [ENOMEM, EMFILE, ENFILE]
/-- LPS `Sys/Net/Socket.v:44` `bind_errnos`: every failure of `inet_csk_get_port`. -/
def bindErrnos : List Int := [EADDRINUSE]
/-- LPS `Sys/Net/Socket.v:45` `listen_errnos`. -/
def listenErrnos : List Int := [EADDRINUSE]

/-- LPS `Sys/Net/Socket.v:62` `conn_channel`: the trace channel of the `ix`-th connection
handed over, past stdin, stdout and stderr (not the descriptor, which `close` can reissue). -/
def connChannel (ix : Word) : Word := ix + 3

/-- LPS `Sys/Net/Socket.v:82` `conn_ix_exhausted`: three values before the counter wraps
onto the standard channels, `accept` stops handing connections over. -/
def connIxExhausted (ix : Word) : Bool := decide (twoPow64 - 3 ≤ uns ix)

/-! ## `struct sockaddr_in` -/

/-- LPS `Sys/Net/Socket.v:91` `sa_family_of`: `sin_family`, host (little-endian) order. -/
def saFamilyOf : List Byte → Int
  | b0 :: b1 :: _ => uns b0 + 256 * uns b1
  | _ => -1

/-- LPS `Sys/Net/Socket.v:99` `sin_port_of`: `sin_port`, network order. -/
def sinPortOf : List Byte → Int
  | _ :: _ :: b2 :: b3 :: _ => 256 * uns b2 + uns b3
  | _ => -1

/-- LPS `Sys/Net/Socket.v:106` `sin_addr_of`: `sin_addr.s_addr`, network order. -/
def sinAddrOf : List Byte → Int
  | _ :: _ :: _ :: _ :: b4 :: b5 :: b6 :: b7 :: _ =>
    16777216 * uns b4 + 65536 * uns b5 + 256 * uns b6 + uns b7
  | _ => -1

/-- LPS `Sys/Net/Socket.v:115` `INADDR_ANY`, the only bind address the model accepts. -/
def INADDR_ANY : Int := 0

/-! ## `socket` (198) -/

/-- LPS `Sys/Net/Socket.v:168` `socket_spec`. The order is `__sys_socket_create` (unknown
flag bit), `__sock_create` (family range, type range), `inet_create` (protocol range, then
the `inetsw` walk); the descriptor is allocated last, so the injected failures attach to the
success path only. -/
def socketSpec (domain type protocol : Word) : Sys SyscallEffect := do
  let m ← getModel
  let tu := uns (abiLow32 type)
  let flagbits := zldiff tu SOCK_TYPE_MASK
  if zldiff flagbits (zlor SOCK_CLOEXEC SOCK_NONBLOCK) ≠ 0 then errRet EINVAL
  else if zland flagbits SOCK_NONBLOCK ≠ 0 then unmodeled
  else
    let ty := zland tu SOCK_TYPE_MASK
    let fam := sint32 domain
    let pro := sint32 protocol
    if fam < 0 ∨ NPROTO ≤ fam then errRet EAFNOSUPPORT
    else if SOCK_MAX ≤ ty then errRet EINVAL
    else if fam ≠ AF_INET then unmodeled
    else if ty = SOCK_PACKET then unmodeled
    else if pro < 0 ∨ IPPROTO_MAX ≤ pro then errRet EINVAL
    else if ty = SOCK_STREAM then
      if pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP then unmodeled
      else if ¬(pro = IPPROTO_IP ∨ pro = IPPROTO_TCP) then errRet EPROTONOSUPPORT
      else
        Sys.alt (do let e ← errnoFrom socketErrnos; errRet e)
          (do
            let fd ← lowestFd m.fds
            setFds (fdInsert m.fds fd (.socket .fresh))
            retOnly fd)
    else if ty = SOCK_DGRAM ∨ ty = SOCK_RAW then unmodeled
    else if ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP then unmodeled
    else errRet ESOCKTNOSUPPORT

/-! ## `bind` (200) -/

/-- LPS `Sys/Net/Socket.v:304` `bind_spec`. The descriptor is resolved first (`EBADF`,
`ENOTSOCK`), then `move_addr_to_kernel` (`EINVAL` outside `[0, 128]`, `EFAULT` on a failed
copy, recorded in the ledger from the copy on), then `inet_bind_sk`/`__inet_bind`. -/
def bindSpec (fd addrp addrlen : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.socket sk) =>
    let al := sint32 addrlen
    if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then errRet EINVAL
    else if al = 0 then errRet EINVAL
    else
      match readBytesMap i.mem addrp (zw al) with
      | none => errRet EFAULT
      | some bs =>
        recordCopyins [(addrp, al.toNat)]
          (if al < SOCKADDR_IN_SIZE then errRet EINVAL
           else
             let fam := saFamilyOf bs
             let port := sinPortOf bs
             let a := sinAddrOf bs
             if ¬(fam = AF_INET ∨ (fam = AF_UNSPEC ∧ a = INADDR_ANY)) then errRet EAFNOSUPPORT
             else if a ≠ INADDR_ANY then unmodeled
             else if port ≠ 0 then unmodeled
             else
               match sk with
               | .fresh =>
                 Sys.alt (do let e ← errnoFrom bindErrnos; errRet e)
                   (do
                     setFds (fdInsert m.fds fd (.socket .bound))
                     retOnly 0)
               | .bound | .listening => errRet EINVAL
               | .connected _ _ rx =>
                 match rx.item 0 with
                 | .inl _ | .inr .fin => errRet EINVAL
                 | .inr .rst | .inr .timedOut => unmodeled
               | .reset _ _ => unmodeled)
  | some _ => errRet ENOTSOCK

/-! ## `listen` (201) -/

/-- LPS `Sys/Net/Socket.v:464` `listen_spec`. The backlog is clamped and observed by nothing.
Re-listening succeeds; only the autobind of an unbound socket can fail (`EADDRINUSE`). -/
def listenSpec (fd _backlog : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some (.socket sk) =>
    match sk with
    | .connected _ _ _ => errRet EINVAL
    | .reset _ _ => errRet EINVAL
    | .listening => retOnly 0
    | .bound => do
      setFds (fdInsert m.fds fd (.socket .listening))
      retOnly 0
    | .fresh =>
      Sys.alt (do let e ← errnoFrom listenErrnos; errRet e)
        (do
          setFds (fdInsert m.fds fd (.socket .listening))
          retOnly 0)
  | some _ => errRet ENOTSOCK

/-! ## `accept` (202) and `accept4` (242) -/

/-- LPS `Sys/Net/Socket.v:568` `accept4_spec`, which `accept` reaches with `flags = 0`.
`EBADF` comes before the flags; a failing accept leaves the queue untouched; a success takes
the head of `IoState.net` and advances `connIx`. Once the channel counter is exhausted the
success branch is empty (a `choose` with no witness, as in LPS) while the injected errnos
stay live. -/
def accept4Spec (fd addrp _addrlenp flags : Word) : Sys SyscallEffect := do
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some e =>
    let fl := uns (abiLow32 flags)
    if zldiff fl (zlor SOCK_CLOEXEC SOCK_NONBLOCK) ≠ 0 then errRet EINVAL
    else if zland fl SOCK_NONBLOCK ≠ 0 then unmodeled
    else
      match e with
      | .socket sk =>
        if !wIs0 addrp then unmodeled
        else
          match sk with
          | .listening =>
            Sys.alt (do let er ← errnoFrom acceptErrnos; errRet er)
              (if connIxExhausted m.connIx then Sys.choose fun (_ : SyscallEffect) => False
               else do
                 let nfd ← lowestFd m.fds
                 modify (·.withAccepted (fdInsert m.fds nfd
                   (.socket (.connected (nqPeer m.net) (connChannel m.connIx)
                     (nqScript m.net)))))
                 retOnly nfd)
          | _ => errRet EINVAL
      | _ => errRet ENOTSOCK

/-! ## `connect` (203) -/

/-- LPS `Sys/Net/Socket.v:839` `connect_spec`. Unlike `bind`, only `EBADF` precedes the
address copy; `ENOTSOCK` comes after it. A listening, accepted or reset socket is
`EISCONN`; `AF_UNSPEC` on a fresh socket is a disconnect that returns 0; the connection
attempt itself is `unmodeled`. -/
def connectSpec (fd addrp addrlen : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match fdLookup m.fds fd with
  | none => errRet EBADF
  | some e =>
    let al := sint32 addrlen
    if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then errRet EINVAL
    else
      match readBytesMap i.mem addrp (zw al) with
      | none => errRet EFAULT
      | some bs =>
        recordCopyins (if al = 0 then [] else [(addrp, bs.length)])
          (match e with
           | .socket sk =>
             if al < SA_FAMILY_SIZE then errRet EINVAL
             else if saFamilyOf bs = AF_UNSPEC then
               match sk with
               | .fresh => retOnly 0
               | .bound | .listening | .connected _ _ _ | .reset _ _ => unmodeled
             else
               match sk with
               | .listening | .connected _ _ _ | .reset _ _ => errRet EISCONN
               | .fresh | .bound =>
                 if al < SOCKADDR_IN_SIZE then errRet EINVAL
                 else if saFamilyOf bs ≠ AF_INET then errRet EAFNOSUPPORT
                 else unmodeled
           | _ => errRet ENOTSOCK)

/-! ## Options and addresses: `getsockname` (204), `getpeername` (205), `setsockopt` (208),
`getsockopt` (209), `shutdown` (210) -/

/-- LPS `Sys/Net/Socket.v:936` `sock_fd`: the descriptor verdict the five calls share,
`EBADF`, `ENOTSOCK` or the socket. The arms are spelled out, as in LPS, so that a new
`FdEntry` constructor must be answered here. -/
def sockFd (m : Model) (fd : Word) : SockState ⊕ Int :=
  match fdLookup m.fds fd with
  | none => .inr EBADF
  | some (.channel _) => .inr ENOTSOCK
  | some (.file _ _) => .inr ENOTSOCK
  | some (.fileW _ _) => .inr ENOTSOCK
  | some (.fileA _ _) => .inr ENOTSOCK
  | some (.fileRW _ _) => .inr ENOTSOCK
  | some .dir => .inr ENOTSOCK
  | some (.pipe _ _) => .inr ENOTSOCK
  | some (.devNull _ _) => .inr ENOTSOCK
  | some .urandom => .inr ENOTSOCK
  | some (.socket sk) => .inl sk

/-- LPS `Sys/Net/Socket.v:959` `sock_level_known`: a level with a handler on an
AF_INET/SOCK_STREAM socket. -/
def sockLevelKnown (level : Word) : Bool :=
  let l := uns level
  l == SOL_SOCKET || l == IPPROTO_IP || l == IPPROTO_TCP

/-- LPS `Sys/Net/Socket.v:964` `shut_how_ok`. -/
def shutHowOk (how : Word) : Bool :=
  let h := uns how
  h == SHUT_RD || h == SHUT_WR || h == SHUT_RDWR

/-- LPS `Sys/Net/Socket.v:972` `int32_neg`: negative as the `int` in the low 32 bits. -/
def int32Neg (w : Word) : Bool := decide (sint32 w < 0)

/-- LPS `Sys/Net/Socket.v:1011` `getsockname_spec`: on a socket the only answer is a success
writing an address (no export in `SyscallEffect`, and an ephemeral port the model does not
carry), so it is `unmodeled`. -/
def getsocknameSpec (fd : Word) : Sys SyscallEffect := do
  let m ← getModel
  match sockFd m fd with
  | .inr e => errRet e
  | .inl _ => unmodeled

/-- LPS `Sys/Net/Socket.v:1064` `getpeername_spec`: `ENOTCONN` for a socket never connected
(`inet_dport == 0`) and for a reset one (`TCP_CLOSE`); a connected socket would succeed by
writing the peer address, which is `unmodeled`. -/
def getpeernameSpec (fd : Word) : Sys SyscallEffect := do
  let m ← getModel
  match sockFd m fd with
  | .inr e => errRet e
  | .inl sk =>
    match sk with
    | .fresh => errRet ENOTCONN
    | .bound => errRet ENOTCONN
    | .listening => errRet ENOTCONN
    | .reset _ _ => errRet ENOTCONN
    | .connected _ _ _ => unmodeled

/-- LPS `Sys/Net/Socket.v:1116` `setsockopt_spec`: a negative `optlen` is `EINVAL` (the
v6.7+ order, after the descriptor), an unknown level is `ENOPROTOOPT` (`ip_setsockopt`);
the option table is `unmodeled`. -/
def setsockoptSpec (fd level optlen : Word) : Sys SyscallEffect := do
  let m ← getModel
  match sockFd m fd with
  | .inr e => errRet e
  | .inl _ =>
    if int32Neg optlen then errRet EINVAL
    else if !sockLevelKnown level then errRet ENOPROTOOPT
    else unmodeled

/-- LPS `Sys/Net/Socket.v:1231` `getsockopt_optlen_read`: the four bytes
`do_sock_getsockopt` reads at `optlen` before it dispatches, recorded only when wholly
readable. -/
def getsockoptOptlenRead (i : SyscallInput) (optlenp : Word) : List (Word × Nat) :=
  match readBytesMap i.mem optlenp 4 with
  | some _ => [(optlenp, 4)]
  | none => []

/-- LPS `Sys/Net/Socket.v:1238` `getsockopt_spec`: an unknown level is `EOPNOTSUPP`
(`do_ip_getsockopt`, not `setsockopt`'s `ENOPROTOOPT`), after the `optlen` read; the option
table is `unmodeled`. -/
def getsockoptSpec (fd level optlenp : Word) : Sys SyscallEffect := do
  let i ← input
  let m ← getModel
  match sockFd m fd with
  | .inr e => errRet e
  | .inl _ =>
    recordCopyins (getsockoptOptlenRead i optlenp)
      (if !sockLevelKnown level then errRet EOPNOTSUPP else unmodeled)

/-- LPS `Sys/Net/Socket.v:1325` `shutdown_spec`: `how` outside `{0, 1, 2}` is `EINVAL` on
every socket; `SHUT_WR` on a listener is 0 with no state change; every other case sets
shutdown bits `SockState` does not carry, and is `unmodeled`. -/
def shutdownSpec (fd how : Word) : Sys SyscallEffect := do
  let m ← getModel
  match sockFd m fd with
  | .inr e => errRet e
  | .inl sk =>
    if !shutHowOk how then errRet EINVAL
    else
      match sk with
      | .fresh => unmodeled
      | .bound => unmodeled
      | .listening => if uns how = SHUT_WR then retOnly 0 else unmodeled
      | .connected _ _ _ => unmodeled
      | .reset _ _ => unmodeled

end Silmaril.Process.LPS
