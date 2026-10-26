module

public import Silmaril.Process.LPS.Syscall

/-!
# LPS in Lean: the user ABI constants (`Sys/Uapi.v`) and their x86-64 variants

Translation of LPS `Sys/Uapi.v` (upstream commit `f1006fe8`): the open, socket, seek, mremap,
madvise, ioctl, fcntl, flock, clock, timerfd, eventfd, signal, scheduling, futex, utsname
and `struct stat` constants that the syscall specifications share, with the `struct stat`
decoders and predicates.

Constants already translated elsewhere are not repeated here: `PROT_*`, `MAP_*`,
`MAP_NORESERVE` and `GRND_*` are in `Basic`, `WNOHANG` is in `Sys/Kernel` and
`sig_kernel_only_mask` is `Run.sigKernelOnlyMask`.

## x86-64 differences

LPS fixes the riscv64 ABI, which takes every uapi header from `asm-generic`. On x86-64 the
following headers are `#include <asm-generic/…>` and nothing else, so every constant above
that comes from them has the same value on x86-64: `asm/fcntl.h`, `asm/ioctls.h`,
`asm/socket.h`, `asm/resource.h`, `asm/errno.h`, `asm/poll.h`, `asm/termbits.h`,
`asm/termios.h`. `asm/mman.h` adds two flags and includes the generic header. The
differences are the following; each has an `…X86` definition below:

* `struct stat` (`arch/x86/include/uapi/asm/stat.h`, the `__x86_64__` branch) is 144 bytes,
  not 128: `st_nlink` is 8 bytes and moves before `st_mode`, `st_mode` is at 24, there is a
  4-byte `__pad0` at 36, `st_rdev` is at 40, `st_blksize` is 8 bytes (no `__pad2`) and the
  tail is `__unused[3]`, 24 bytes at 120. `INIT_STRUCT_STAT_PADDING` zeroes `__pad0` and
  `__unused`. See `statLayoutX86`;
* `struct epoll_event` is `__attribute__((packed))` under `__x86_64__`
  (`include/uapi/linux/eventpoll.h`, `EPOLL_PACKED`): 12 bytes with `data` at offset 4,
  against LPS's 16 with `data` at 8 (`Sys/Fs/EventPoll.v:203`). So `EP_MAX_EVENTS` is
  `INT_MAX / 12 = 178956970`. See `epollEventBytesX86`;
* `struct sigaction` (the kernel's, `arch/x86/include/uapi/asm/signal.h:90`): x86-64 defines
  `SA_RESTORER = 0x04000000`, so the struct has an `sa_restorer` member: handler at 0, flags
  at 8, restorer at 16, mask at 24, 32 bytes, against LPS's 24 bytes without a restorer
  (`Sys/Kernel/Signal.v:290`). `SA_RESTORER` is then in `UAPI_SA_FLAGS`
  (`include/linux/signal_types.h`, `__ARCH_UAPI_SA_FLAGS`), so `do_sigaction` keeps it.
  See `kernelSigactionBytesX86`;
* `UTS_MACHINE` is `"x86_64"` (`arch/x86/Makefile`), not `"riscv64"`
  (`Sys/Kernel/Sys.v:926`). See `utsMachineCharsX86`;
* `mmap` has two x86-only flags, `MAP_32BIT = 0x40` and `MAP_ABOVE4G = 0x80`
  (`arch/x86/include/uapi/asm/mman.h`). On riscv64 those bits name nothing and are ignored;
  on x86-64 `MAP_32BIT` changes placement. See `MAP_32BIT_X86`;
* `arch_prctl` (x86-only, `arch/x86/include/uapi/asm/prctl.h`) sets the `fs`/`gs` bases that
  riscv64 sets through `tp`. See `ARCH_SET_FS_X86`.

The legacy `clone` register order also differs, and is decoded in `Sys/Fork`
(`cloneRegsX86`): riscv64 selects `CONFIG_CLONE_BACKWARDS` and reads
`flags, newsp, parent_tid, tls, child_tid` (LPS `Sys/Kernel/Fork.v:376-379`), while x86-64
selects none of `CLONE_BACKWARDS*` (only `X86_32` selects `CLONE_BACKWARDS`) and reads
`flags, newsp, parent_tid, child_tid, tls`.

Checked and found the same on x86-64: `stack_t` (24 bytes);
`sigset_t` (8 bytes, `_NSIG = 64`); `MINSIGSTKSZ = 2048` (x86-64 additionally checks the
alternate stack against the runtime signal-frame size under `CONFIG_DYNAMIC_SIGFRAME`, which
is what LPS's `sigaltstack_size_valid` premise covers); `SIGKILL`, `SIGSTOP`, `SIGABRT`;
`struct new_utsname`; `struct iovec`; `struct timespec`; `struct sockaddr_in`; `struct
rlimit64`; the `int` pipe descriptors.

The user address-space bound is not a uapi constant; its x86-64 form is in `Uaccess`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Fs (Path)

/-! ## Open and `*at` flags -/

/-- LPS `Sys/Uapi.v:20` `O_WRONLY`. -/
def O_WRONLY : Int := 1
/-- LPS `Sys/Uapi.v:33` `O_RDWR`. -/
def O_RDWR : Int := 2
/-- LPS `Sys/Uapi.v:34` `O_CREAT`. -/
def O_CREAT : Int := 64
/-- LPS `Sys/Uapi.v:35` `O_EXCL`. -/
def O_EXCL : Int := 128
/-- LPS `Sys/Uapi.v:36` `O_TRUNC`. -/
def O_TRUNC : Int := 512
/-- LPS `Sys/Uapi.v:37` `O_CLOEXEC`. -/
def O_CLOEXEC : Int := 524288
/-- LPS `Sys/Uapi.v:41` `O_LARGEFILE`: musl ORs it into every open; meaningless on 64-bit. -/
def O_LARGEFILE : Int := 32768
/-- LPS `Sys/Uapi.v:138` `O_NONBLOCK` (asm-generic; the same on x86-64). -/
def O_NONBLOCK : Int := 2048
/-- LPS `Sys/Uapi.v:159` `O_DIRECTORY`. -/
def O_DIRECTORY : Int := 65536
/-- LPS `Sys/Uapi.v:161` `AT_FDCWD`: `-100` in two's complement. -/
def AT_FDCWD : Word := zw (-100)
/-- LPS `Sys/Uapi.v:168` `AT_FDCWD32`: `AT_FDCWD` after the `int dfd` narrowing. -/
def AT_FDCWD32 : Word := fd32 AT_FDCWD
/-- LPS `Sys/Uapi.v:175` `ID_MINUS_ONE`: `(uid_t)-1` after the 32-bit narrowing. -/
def ID_MINUS_ONE : Word := zw 4294967295
/-- LPS `Sys/Uapi.v:179` `AT_SYMLINK_NOFOLLOW`. -/
def AT_SYMLINK_NOFOLLOW : Int := 256
/-- LPS `Sys/Uapi.v:189` `AT_EACCESS`. -/
def AT_EACCESS : Int := 512
/-- LPS `Sys/Uapi.v:197` `AT_EMPTY_PATH`. -/
def AT_EMPTY_PATH : Int := 4096
/-- LPS `Sys/Uapi.v:210` `S_IRWXO`: the mask `faccessat`'s `mode` is validated against. -/
def S_IRWXO : Int := 7

/-- LPS `Sys/Uapi.v:222` `dot_path`: `"."`. -/
def dotPath : Path := [46]
/-- LPS `Sys/Uapi.v:231` `devnull_path`: `"/dev/null"`. -/
def devnullPath : Path := [47, 100, 101, 118, 47, 110, 117, 108, 108]
/-- LPS `Sys/Uapi.v:241` `urandom_path`: `"/dev/urandom"`. -/
def urandomPath : Path := [47, 100, 101, 118, 47, 117, 114, 97, 110, 100, 111, 109]

/-! ## Sockets -/

/-- LPS `Sys/Uapi.v:254` `AF_UNSPEC`. -/
def AF_UNSPEC : Int := 0
/-- LPS `Sys/Uapi.v:255` `AF_INET`. -/
def AF_INET : Int := 2
/-- LPS `Sys/Uapi.v:256` `NPROTO` (`AF_MAX`). -/
def NPROTO : Int := 46
/-- LPS `Sys/Uapi.v:258` `SOCK_STREAM`. -/
def SOCK_STREAM : Int := 1
/-- LPS `Sys/Uapi.v:259` `SOCK_DGRAM`. -/
def SOCK_DGRAM : Int := 2
/-- LPS `Sys/Uapi.v:260` `SOCK_RAW`. -/
def SOCK_RAW : Int := 3
/-- LPS `Sys/Uapi.v:261` `SOCK_SEQPACKET`. -/
def SOCK_SEQPACKET : Int := 5
/-- LPS `Sys/Uapi.v:262` `SOCK_DCCP`. -/
def SOCK_DCCP : Int := 6
/-- LPS `Sys/Uapi.v:263` `SOCK_PACKET`. -/
def SOCK_PACKET : Int := 10
/-- LPS `Sys/Uapi.v:264` `SOCK_MAX`. -/
def SOCK_MAX : Int := 11
/-- LPS `Sys/Uapi.v:268` `SOCK_TYPE_MASK`. -/
def SOCK_TYPE_MASK : Int := 15
/-- LPS `Sys/Uapi.v:276` `SOCK_CLOEXEC` (`O_CLOEXEC`; the same on x86-64, which does not
define `ARCH_HAS_SOCKET_TYPES`). -/
def SOCK_CLOEXEC : Int := 524288
/-- LPS `Sys/Uapi.v:277` `SOCK_NONBLOCK` (`O_NONBLOCK`). -/
def SOCK_NONBLOCK : Int := 2048
/-- LPS `Sys/Uapi.v:285` `IPPROTO_IP`. -/
def IPPROTO_IP : Int := 0
/-- LPS `Sys/Uapi.v:286` `IPPROTO_TCP`. -/
def IPPROTO_TCP : Int := 6
/-- LPS `Sys/Uapi.v:287` `IPPROTO_SCTP`. -/
def IPPROTO_SCTP : Int := 132
/-- LPS `Sys/Uapi.v:288` `IPPROTO_MPTCP`. -/
def IPPROTO_MPTCP : Int := 262
/-- LPS `Sys/Uapi.v:289` `IPPROTO_MAX`. -/
def IPPROTO_MAX : Int := 263
/-- LPS `Sys/Uapi.v:307` `SOCKADDR_STORAGE_SIZE`. -/
def SOCKADDR_STORAGE_SIZE : Int := 128
/-- LPS `Sys/Uapi.v:308` `SA_FAMILY_SIZE`. -/
def SA_FAMILY_SIZE : Int := 2
/-- LPS `Sys/Uapi.v:309` `SOCKADDR_IN_SIZE`. -/
def SOCKADDR_IN_SIZE : Int := 16
/-- LPS `Sys/Uapi.v:330` `SOL_SOCKET`. -/
def SOL_SOCKET : Int := 1
/-- LPS `Sys/Uapi.v:331` `SHUT_RD`. -/
def SHUT_RD : Int := 0
/-- LPS `Sys/Uapi.v:332` `SHUT_WR`. -/
def SHUT_WR : Int := 1
/-- LPS `Sys/Uapi.v:333` `SHUT_RDWR`. -/
def SHUT_RDWR : Int := 2

/-! ## Seek, mprotect, mremap, madvise -/

/-- LPS `Sys/Uapi.v:335` `SEEK_SET`. -/
def SEEK_SET : Int := 0
/-- LPS `Sys/Uapi.v:336` `SEEK_CUR`. -/
def SEEK_CUR : Int := 1
/-- LPS `Sys/Uapi.v:337` `SEEK_END`. -/
def SEEK_END : Int := 2
/-- LPS `Sys/Uapi.v:343` `SEEK_MAX` (`SEEK_HOLE`). -/
def SEEK_MAX : Int := 4
/-- LPS `Sys/Uapi.v:354` `PROT_GROWSDOWN`. -/
def PROT_GROWSDOWN : Int := 0x01000000
/-- LPS `Sys/Uapi.v:355` `PROT_GROWSUP`. -/
def PROT_GROWSUP : Int := 0x02000000
/-- LPS `Sys/Uapi.v:377` `MREMAP_MAYMOVE`. -/
def MREMAP_MAYMOVE : Int := 1
/-- LPS `Sys/Uapi.v:385` `MADV_DONTNEED`. -/
def MADV_DONTNEED : Int := 4

/-- x86-64 only: `MAP_32BIT` (`arch/x86/include/uapi/asm/mman.h`), place the mapping in the
low 2 GiB. On riscv64 (LPS) the bit names no flag and `do_mmap` ignores it. -/
def MAP_32BIT_X86 : Int := 0x40
/-- x86-64 only: `MAP_ABOVE4G` (`arch/x86/include/uapi/asm/mman.h`). -/
def MAP_ABOVE4G_X86 : Int := 0x80

/-! ## ioctl, fcntl, flock -/

/-- LPS `Sys/Uapi.v:409` `TCGETS` (asm-generic `ioctls.h`; the same on x86-64). -/
def TCGETS : Word := 21505
/-- LPS `Sys/Uapi.v:410` `TCSETS`. -/
def TCSETS : Word := 21506
/-- LPS `Sys/Uapi.v:411` `TIOCSCTTY`. -/
def TIOCSCTTY : Word := 21518
/-- LPS `Sys/Uapi.v:412` `TIOCGWINSZ`. -/
def TIOCGWINSZ : Word := 21523
/-- LPS `Sys/Uapi.v:413` `TIOCSWINSZ`. -/
def TIOCSWINSZ : Word := 21524
/-- LPS `Sys/Uapi.v:414` `TIOCNOTTY`. -/
def TIOCNOTTY : Word := 21538
/-- LPS `Sys/Uapi.v:415` `TIOCGPTN`. -/
def TIOCGPTN : Word := 2147767344
/-- LPS `Sys/Uapi.v:416` `TIOCSPTLCK`. -/
def TIOCSPTLCK : Word := 1074025521
/-- LPS `Sys/Uapi.v:426` `F_GETFD`. -/
def F_GETFD : Word := 1
/-- LPS `Sys/Uapi.v:427` `F_SETFD`. -/
def F_SETFD : Word := 2
/-- LPS `Sys/Uapi.v:428` `F_GETFL`. -/
def F_GETFL : Word := 3
/-- LPS `Sys/Uapi.v:429` `F_SETFL`. -/
def F_SETFL : Word := 4
/-- LPS `Sys/Uapi.v:451` `LOCK_SH`. -/
def LOCK_SH : Int := 1
/-- LPS `Sys/Uapi.v:452` `LOCK_EX`. -/
def LOCK_EX : Int := 2
/-- LPS `Sys/Uapi.v:453` `LOCK_NB`. -/
def LOCK_NB : Int := 4
/-- LPS `Sys/Uapi.v:454` `LOCK_UN`. -/
def LOCK_UN : Int := 8
/-- LPS `Sys/Uapi.v:455` `LOCK_MAND`: still read by `flock`, which then succeeds as a no-op. -/
def LOCK_MAND : Int := 32
/-- LPS `Sys/Uapi.v:470` `O_APPEND`. -/
def O_APPEND : Int := 1024
/-- LPS `Sys/Uapi.v:471` `FASYNC`. -/
def FASYNC : Int := 8192
/-- LPS `Sys/Uapi.v:476` `O_DIRECT`. -/
def O_DIRECT : Int := 16384
/-- LPS `Sys/Uapi.v:477` `O_NOATIME`. -/
def O_NOATIME : Int := 262144
/-- LPS `Sys/Uapi.v:481` `RLIMIT_CORE`. -/
def RLIMIT_CORE : Int := 4

/-! ## Clocks, timers and event counters -/

/-- LPS `Sys/Uapi.v:501` `CLOCK_REALTIME`. -/
def CLOCK_REALTIME : Int := 0
/-- LPS `Sys/Uapi.v:502` `CLOCK_MONOTONIC`. -/
def CLOCK_MONOTONIC : Int := 1
/-- LPS `Sys/Uapi.v:503` `CLOCK_PROCESS_CPUTIME_ID`. -/
def CLOCK_PROCESS_CPUTIME_ID : Int := 2
/-- LPS `Sys/Uapi.v:504` `CLOCK_MONOTONIC_RAW`. -/
def CLOCK_MONOTONIC_RAW : Int := 4
/-- LPS `Sys/Uapi.v:505` `CLOCK_REALTIME_COARSE`. -/
def CLOCK_REALTIME_COARSE : Int := 5
/-- LPS `Sys/Uapi.v:506` `CLOCK_MONOTONIC_COARSE`. -/
def CLOCK_MONOTONIC_COARSE : Int := 6
/-- LPS `Sys/Uapi.v:507` `CLOCK_BOOTTIME`. -/
def CLOCK_BOOTTIME : Int := 7
/-- LPS `Sys/Uapi.v:508` `CLOCK_REALTIME_ALARM`. -/
def CLOCK_REALTIME_ALARM : Int := 8
/-- LPS `Sys/Uapi.v:509` `CLOCK_BOOTTIME_ALARM`. -/
def CLOCK_BOOTTIME_ALARM : Int := 9

/-- `Z.lor` on non-negative integers. -/
def zlor (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)
/-- `Z.land` on non-negative integers. -/
def zland (a b : Int) : Int := ((a.toNat &&& b.toNat : Nat) : Int)

/-- LPS `Sys/Uapi.v:529` `TFD_CREATE_FLAGS`: `O_CLOEXEC | O_NONBLOCK`. -/
def TFD_CREATE_FLAGS : Int := zlor O_CLOEXEC O_NONBLOCK
/-- LPS `Sys/Uapi.v:548` `EFD_SEMAPHORE`. -/
def EFD_SEMAPHORE : Int := 1
/-- LPS `Sys/Uapi.v:567` `EFD_FLAGS_SET`: `O_CLOEXEC | O_NONBLOCK | EFD_SEMAPHORE`. -/
def EFD_FLAGS_SET : Int := zlor (zlor O_CLOEXEC O_NONBLOCK) EFD_SEMAPHORE
/-- LPS `Sys/Uapi.v:584` `CLOCK_NS_ENVELOPE`: `2^63` ns, the first value `ktime_t` cannot
hold. -/
def CLOCK_NS_ENVELOPE : Int := 2 ^ 63
/-- LPS `Sys/Uapi.v:605` `KTIME_MAX`. -/
def KTIME_MAX : Int := 2 ^ 63 - 1
/-- LPS `Sys/Uapi.v:617` `KTIME_SEC_MAX`. -/
def KTIME_SEC_MAX : Int := 9223372036

/-- LPS `Sys/Uapi.v:641` `tv_sec_of`: the first 8-byte little-endian field. -/
def tvSecOf (bs : List Byte) : Int := bytesLeToZ (bs.take 8)
/-- LPS `Sys/Uapi.v:643` `tv_frac_of`: the rest, as the second field. -/
def tvFracOf (bs : List Byte) : Int := bytesLeToZ (bs.drop 8)
/-- LPS `Sys/Uapi.v:650` `timespec_ns`, computed in `Int` (no wrapping). -/
def timespecNs (bs : List Byte) : Int := tvSecOf bs * 1000000000 + tvFracOf bs
/-- LPS `Sys/Uapi.v:674` `timespec_ktime`: `ktime_set` saturates at `KTIME_SEC_MAX`. -/
def timespecKtime (bs : List Byte) : Int :=
  if tvSecOf bs < KTIME_SEC_MAX then timespecNs bs else KTIME_MAX
/-- LPS `Sys/Uapi.v:687` `timespec_ns_signed`: `tv_sec` read as a signed 64-bit field. -/
def timespecNsSigned (bs : List Byte) : Int :=
  (if tvSecOf bs < 2 ^ 63 then tvSecOf bs else tvSecOf bs - 2 ^ 64) * 1000000000 + tvFracOf bs

/-- LPS `Sys/Uapi.v:696` `AT_REMOVEDIR`. -/
def AT_REMOVEDIR : Int := 512
/-- LPS `Sys/Uapi.v:709` `NAME_MAX`. -/
def NAME_MAX : Nat := 255
/-- LPS `Sys/Uapi.v:713` `NSEC_PER_SEC`. -/
def NSEC_PER_SEC : Int := 1000000000

/-! ## Signals -/

/-- LPS `Sys/Uapi.v:719` `kernel_sigset_bytes` (the same 8 bytes on x86-64). -/
def kernelSigsetBytes : Int := 8
/-- LPS `Sys/Uapi.v:725` `SIG_BLOCK`. -/
def SIG_BLOCK : Int := 0
/-- LPS `Sys/Uapi.v:726` `SIG_UNBLOCK`. -/
def SIG_UNBLOCK : Int := 1
/-- LPS `Sys/Uapi.v:727` `SIG_SETMASK`. -/
def SIG_SETMASK : Int := 2
/-- LPS `Sys/Uapi.v:746` `NSIG_BYTES`. -/
def NSIG_BYTES : Int := 8
/-- LPS `Sys/Uapi.v:760` `SS_ONSTACK`. -/
def SS_ONSTACK : Int := 1
/-- LPS `Sys/Uapi.v:761` `SS_DISABLE`. -/
def SS_DISABLE : Int := 2
/-- LPS `Sys/Uapi.v:762` `SS_AUTODISARM` (`SS_FLAG_BITS`). -/
def SS_AUTODISARM : Int := 0x80000000
/-- LPS `Sys/Uapi.v:773` `SIGALTSTACK_BYTES`: `sizeof(stack_t)`, 24 (the same on x86-64). -/
def SIGALTSTACK_BYTES : Int := 24
/-- LPS `Sys/Uapi.v:774` `SS_SP_OFF`. -/
def SS_SP_OFF : Int := 0
/-- LPS `Sys/Uapi.v:775` `SS_FLAGS_OFF`. -/
def SS_FLAGS_OFF : Int := 8
/-- LPS `Sys/Uapi.v:776` `SS_SIZE_OFF`. -/
def SS_SIZE_OFF : Int := 16
/-- LPS `Sys/Uapi.v:787` `MINSIGSTKSZ` (2048 on x86-64 too,
`arch/x86/include/uapi/asm/signal.h:64`). -/
def MINSIGSTKSZ : Int := 2048
/-- LPS `Sys/Uapi.v:822` `SIGABRT`. -/
def SIGABRT : Int := 6
/-- LPS `Sys/Uapi.v:823` `sigabrt_mask`: `1 << (SIGABRT - 1)`. -/
def sigabrtMask : Int := 32

/-- x86-64 only: `SA_RESTORER` (`arch/x86/include/uapi/asm/signal.h:62`). riscv64 (LPS)
defines none (`Sys/Kernel/Signal.v:231`). On x86-64 it is `__ARCH_UAPI_SA_FLAGS`, so it
survives `do_sigaction`'s `sa_flags &= UAPI_SA_FLAGS`. -/
def SA_RESTORER_X86 : Int := 0x04000000

/-- LPS `Sys/Kernel/Signal.v:290`: the kernel's `struct sigaction` on riscv64 is
`sa_handler` (0), `sa_flags` (8), `sa_mask` (16): 24 bytes, no `sa_restorer`. -/
def kernelSigactionBytes : Int := 24
/-- The kernel's `struct sigaction` on x86-64 (`arch/x86/include/uapi/asm/signal.h:90`):
`sa_handler` (0), `sa_flags` (8), `sa_restorer` (16), `sa_mask` (24): 32 bytes. -/
def kernelSigactionBytesX86 : Int := 32
/-- `sa_flags` offset, riscv64 and x86-64. -/
def SA_FLAGS_OFF : Int := 8
/-- `sa_mask` offset on riscv64 (LPS). -/
def SA_MASK_OFF : Int := 16
/-- `sa_restorer` offset on x86-64. -/
def SA_RESTORER_OFF_X86 : Int := 16
/-- `sa_mask` offset on x86-64. -/
def SA_MASK_OFF_X86 : Int := 24

/-! ## Messages, descriptors, groups, scheduling, futexes -/

/-- LPS `Sys/Uapi.v:842` `MSG_CMSG_COMPAT` (under `CONFIG_COMPAT`). -/
def MSG_CMSG_COMPAT : Int := 2147483648
/-- LPS `Sys/Uapi.v:880` `NR_OPEN_DEFAULT` (`BITS_PER_LONG`, 64 on both LP64 targets). -/
def NR_OPEN_DEFAULT : Int := 64
/-- LPS `Sys/Uapi.v:890` `NGROUPS_MAX`. -/
def NGROUPS_MAX : Int := 65536
/-- LPS `Sys/Uapi.v:905` `SCHED_NORMAL`. -/
def SCHED_NORMAL : Int := 0
/-- LPS `Sys/Uapi.v:906` `SCHED_FIFO`. -/
def SCHED_FIFO : Int := 1
/-- LPS `Sys/Uapi.v:907` `SCHED_RR`. -/
def SCHED_RR : Int := 2
/-- LPS `Sys/Uapi.v:908` `SCHED_BATCH`. -/
def SCHED_BATCH : Int := 3
/-- LPS `Sys/Uapi.v:909` `SCHED_IDLE`. -/
def SCHED_IDLE : Int := 5
/-- LPS `Sys/Uapi.v:910` `SCHED_DEADLINE`. -/
def SCHED_DEADLINE : Int := 6
/-- LPS `Sys/Uapi.v:911` `SCHED_EXT`. -/
def SCHED_EXT : Int := 7
/-- LPS `Sys/Uapi.v:921` `SCHED_RESET_ON_FORK`. -/
def SCHED_RESET_ON_FORK : Int := 0x40000000
/-- LPS `Sys/Uapi.v:932` `MAX_RT_PRIO`. -/
def MAX_RT_PRIO : Int := 100
/-- LPS `Sys/Uapi.v:945` `CLONE_VM`. -/
def CLONE_VM : Int := 256
/-- LPS `Sys/Uapi.v:968` `FUTEX_WAIT`. -/
def FUTEX_WAIT : Int := 0
/-- LPS `Sys/Uapi.v:969` `FUTEX_WAKE`. -/
def FUTEX_WAKE : Int := 1
/-- LPS `Sys/Uapi.v:970` `FUTEX_PRIVATE_FLAG`. -/
def FUTEX_PRIVATE_FLAG : Int := 128
/-- LPS `Sys/Uapi.v:971` `FUTEX_WAIT_PRIVATE`. -/
def FUTEX_WAIT_PRIVATE : Int := zlor FUTEX_WAIT FUTEX_PRIVATE_FLAG
/-- LPS `Sys/Uapi.v:972` `FUTEX_WAKE_PRIVATE`. -/
def FUTEX_WAKE_PRIVATE : Int := zlor FUTEX_WAKE FUTEX_PRIVATE_FLAG
/-- LPS `Sys/Uapi.v:987` `FUTEX_WORD_SIZE`. -/
def FUTEX_WORD_SIZE : Int := 4

/-! ## `uname` and `prctl` -/

/-- LPS `Sys/Uapi.v:998` `NEW_UTS_LEN`. -/
def NEW_UTS_LEN : Int := 64
/-- LPS `Sys/Uapi.v:1012` `NEW_UTSNAME_SIZE`: six 65-byte fields (the same on x86-64). -/
def NEW_UTSNAME_SIZE : Int := 390
/-- LPS `Sys/Kernel/Sys.v:926` `uts_machine_chars`: `"riscv64"`. -/
def utsMachineChars : List Int := [114, 105, 115, 99, 118, 54, 52]
/-- x86-64: `UTS_MACHINE` is `"x86_64"` (`arch/x86/Makefile`, `UTS_MACHINE := x86_64` for
`CONFIG_X86_64`). -/
def utsMachineCharsX86 : List Int := [120, 56, 54, 95, 54, 52]
/-- LPS `Sys/Uapi.v:1021` `PR_CAPBSET_READ`. -/
def PR_CAPBSET_READ : Int := 23
/-- LPS `Sys/Uapi.v:1037` `CAP_LAST_CAP`. -/
def CAP_LAST_CAP : Int := 40

/-! ## `arch_prctl` (x86-64 only) -/

/-- x86-64 only: `ARCH_SET_GS` (`arch/x86/include/uapi/asm/prctl.h`). -/
def ARCH_SET_GS_X86 : Int := 0x1001
/-- x86-64 only: `ARCH_SET_FS`. -/
def ARCH_SET_FS_X86 : Int := 0x1002
/-- x86-64 only: `ARCH_GET_FS`. -/
def ARCH_GET_FS_X86 : Int := 0x1003
/-- x86-64 only: `ARCH_GET_GS`. -/
def ARCH_GET_GS_X86 : Int := 0x1004

/-! ## `struct epoll_event` -/

/-- LPS `Sys/Fs/EventPoll.v:203` `epoll_event_bytes`: 16 on riscv64 (`data` 8-aligned). -/
def epollEventBytes : Int := 16
/-- LPS `Sys/Fs/EventPoll.v:208` `EP_MAX_EVENTS`: `INT_MAX / 16`. -/
def EP_MAX_EVENTS : Int := 134217727
/-- Offset of `data` in `struct epoll_event` on riscv64. -/
def epollEventDataOff : Int := 8
/-- x86-64: `struct epoll_event` is packed (`EPOLL_PACKED` under `__x86_64__`,
`include/uapi/linux/eventpoll.h`): 12 bytes. -/
def epollEventBytesX86 : Int := 12
/-- x86-64: `EP_MAX_EVENTS = INT_MAX / sizeof(struct epoll_event) = INT_MAX / 12`. -/
def EP_MAX_EVENTS_X86 : Int := 178956970
/-- x86-64: offset of `data` in the packed `struct epoll_event`. -/
def epollEventDataOffX86 : Int := 4

/-! ## `struct stat` (LPS `Sys/Uapi.v:1040-1457`) -/

/-- LPS `Sys/Uapi.v:1074` `STAT_SIZE`: the asm-generic 128-byte `struct stat`. -/
def STAT_SIZE : Int := 128
/-- LPS `Sys/Uapi.v:1079` `ST_MODE_OFF`. -/
def ST_MODE_OFF : Nat := 16
/-- LPS `Sys/Uapi.v:1080` `ST_RDEV_OFF`. -/
def ST_RDEV_OFF : Nat := 32
/-- LPS `Sys/Uapi.v:1081` `ST_PAD1_OFF`. -/
def ST_PAD1_OFF : Nat := 40
/-- LPS `Sys/Uapi.v:1082` `ST_SIZE_OFF`. -/
def ST_SIZE_OFF : Nat := 48
/-- LPS `Sys/Uapi.v:1083` `ST_BLKSIZE_OFF`. -/
def ST_BLKSIZE_OFF : Nat := 56
/-- LPS `Sys/Uapi.v:1084` `ST_PAD2_OFF`. -/
def ST_PAD2_OFF : Nat := 60
/-- LPS `Sys/Uapi.v:1085` `ST_BLOCKS_OFF`. -/
def ST_BLOCKS_OFF : Nat := 64
/-- LPS `Sys/Uapi.v:1086` `ST_UNUSED45_OFF`. -/
def ST_UNUSED45_OFF : Nat := 120

/-- LPS `Sys/Uapi.v:1094` `stat_field_le`: the unsigned little-endian value of `n` bytes at
`off`. -/
def statFieldLe (off n : Nat) (bs : List Byte) : Int := bytesLeToZ ((bs.drop off).take n)

/-- LPS `Sys/Uapi.v:1104` `S_IFMT`. -/
def S_IFMT : Int := 61440
/-- LPS `Sys/Uapi.v:1105` `S_IFSOCK`. -/
def S_IFSOCK : Int := 49152
/-- LPS `Sys/Uapi.v:1106` `S_IFLNK`. -/
def S_IFLNK : Int := 40960
/-- LPS `Sys/Uapi.v:1107` `S_IFREG`. -/
def S_IFREG : Int := 32768
/-- LPS `Sys/Uapi.v:1108` `S_IFBLK`. -/
def S_IFBLK : Int := 24576
/-- LPS `Sys/Uapi.v:1109` `S_IFDIR`. -/
def S_IFDIR : Int := 16384
/-- LPS `Sys/Uapi.v:1110` `S_IFCHR`. -/
def S_IFCHR : Int := 8192
/-- LPS `Sys/Uapi.v:1111` `S_IFIFO`. -/
def S_IFIFO : Int := 4096

/-- The file-type test on an `S_IFMT` value (the body of LPS `Sys/Uapi.v:1129`
`stat_ifmt_valid`). -/
def ifmtValid (t : Int) : Bool :=
  t == S_IFSOCK || t == S_IFLNK || t == S_IFREG || t == S_IFBLK || t == S_IFDIR ||
    t == S_IFCHR || t == S_IFIFO

/-- LPS `Sys/Uapi.v:1114` `stat_ifmt`. -/
def statIfmt (bs : List Byte) : Int := zland (statFieldLe ST_MODE_OFF 4 bs) S_IFMT
/-- LPS `Sys/Uapi.v:1122` `stat_is_reg`. -/
def statIsReg (bs : List Byte) : Bool := statIfmt bs == S_IFREG
/-- LPS `Sys/Uapi.v:1129` `stat_ifmt_valid`. -/
def statIfmtValid (bs : List Byte) : Bool := ifmtValid (statIfmt bs)

/-- LPS `Sys/Uapi.v:1149` `stat_buf_wf`: 128 bytes, a file type, zero padding. -/
def statBufWf (bs : List Byte) : Bool :=
  bs.length == 128 && statIfmtValid bs && statFieldLe ST_PAD1_OFF 8 bs == 0 &&
    statFieldLe ST_PAD2_OFF 4 bs == 0 && statFieldLe ST_UNUSED45_OFF 8 bs == 0

/-- LPS `Sys/Uapi.v:1183` `stat_size_ok`: for a regular file, `st_size` is the length
(modulo `2^64`). -/
def statSizeOk (n : Nat) (bs : List Byte) : Bool :=
  !statIsReg bs || statFieldLe ST_SIZE_OFF 8 bs == uns (zw n)

/-- LPS `Sys/Uapi.v:1210` `DEVNULL_RDEV`: `new_encode_dev(MKDEV(1, 3))`. -/
def DEVNULL_RDEV : Int := 259
/-- LPS `Sys/Uapi.v:1230` `URANDOM_RDEV`: `new_encode_dev(MKDEV(1, 9))`. -/
def URANDOM_RDEV : Int := 265

/-- LPS `Sys/Uapi.v:1216` `stat_chrdev_ok`. -/
def statChrdevOk (rdev : Int) (bs : List Byte) : Bool :=
  statIfmt bs == S_IFCHR && statFieldLe ST_RDEV_OFF 8 bs == rdev &&
    statFieldLe ST_SIZE_OFF 8 bs == 0 && statFieldLe ST_BLOCKS_OFF 8 bs == 0
/-- LPS `Sys/Uapi.v:1222` `stat_devnull_ok`. -/
def statDevnullOk (bs : List Byte) : Bool := statChrdevOk DEVNULL_RDEV bs
/-- LPS `Sys/Uapi.v:1232` `stat_urandom_ok`. -/
def statUrandomOk (bs : List Byte) : Bool := statChrdevOk URANDOM_RDEV bs

/-- LPS `Sys/Uapi.v:1238` `stat_bytes_eqb`. -/
def statBytesEqb (l1 l2 : List Byte) : Bool := l1 == l2

/-- LPS `Sys/Uapi.v:1245` `stat_bytes_eqb_eq`. -/
theorem statBytesEqb_eq (l1 l2 : List Byte) : statBytesEqb l1 l2 = true ↔ l1 = l2 := by
  simp [statBytesEqb]

/-- LPS `Sys/Uapi.v:1281` `stat_stable_eqb`: bytes 0..47 and 56..63 may not change between
two `fstat`s of one file. -/
def statStableEqb (b1 b2 : List Byte) : Bool :=
  statBytesEqb (b1.take ST_PAD1_OFF) (b2.take ST_PAD1_OFF) &&
    statBytesEqb ((b1.drop ST_PAD1_OFF).take 8) ((b2.drop ST_PAD1_OFF).take 8) &&
    statBytesEqb ((b1.drop ST_BLKSIZE_OFF).take 8) ((b2.drop ST_BLKSIZE_OFF).take 8)

/-- LPS `Sys/Uapi.v:1288` `stat_stable_eqb_refl`. -/
theorem statStableEqb_refl (b : List Byte) : statStableEqb b b = true := by
  simp [statStableEqb, statBytesEqb]

/-- LPS `Sys/Uapi.v:1347` `stat_set_size`: the same `struct stat` with `st_size := n`. -/
def statSetSize (n : Nat) (bs : List Byte) : List Byte :=
  bs.take 48 ++ zToLeBytes 8 n ++ bs.drop 56

/-! ### The x86-64 `struct stat`

`arch/x86/include/uapi/asm/stat.h` (`__x86_64__`):

| member | offset | size |
| --- | ---: | ---: |
| `st_dev` | 0 | 8 |
| `st_ino` | 8 | 8 |
| `st_nlink` | 16 | 8 |
| `st_mode` | 24 | 4 |
| `st_uid` | 28 | 4 |
| `st_gid` | 32 | 4 |
| `__pad0` | 36 | 4 |
| `st_rdev` | 40 | 8 |
| `st_size` | 48 | 8 |
| `st_blksize` | 56 | 8 |
| `st_blocks` | 64 | 8 |
| `st_atime` … `st_ctime_nsec` | 72 | 48 |
| `__unused[3]` | 120 | 24 |

144 bytes, with no compiler padding. `INIT_STRUCT_STAT_PADDING` zeroes `__pad0` and
`__unused` (the other members are all assigned by `cp_new_stat`), so the envelope is the
same as LPS's: a file type, zero padding. The stable members (`st_dev` … `st_rdev`, and
`st_blksize`) occupy bytes 0..47 and 56..63, the same byte ranges as on riscv64, and
`st_size` is at 48 on both. -/

/-- The layout facts the `struct stat` predicates read. -/
structure StatLayout where
  /-- `sizeof(struct stat)`. -/
  size : Nat
  /-- offset of the 4-byte `st_mode`. -/
  modeOff : Nat
  /-- offset of the 8-byte `st_rdev`. -/
  rdevOff : Nat
  /-- offset of the 8-byte `st_size`. -/
  sizeOff : Nat
  /-- offset of the 8-byte `st_blocks`. -/
  blocksOff : Nat
  /-- the padding the kernel zeroes, as `(offset, width)`. -/
  zeroFields : List (Nat × Nat)
  /-- the byte ranges that may not change between two `fstat`s, as `(offset, width)`. -/
  stableRanges : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- LPS's (riscv64, asm-generic) `struct stat`, `Sys/Uapi.v:1074-1086`. -/
def statLayoutLps : StatLayout where
  size := 128
  modeOff := ST_MODE_OFF
  rdevOff := ST_RDEV_OFF
  sizeOff := ST_SIZE_OFF
  blocksOff := ST_BLOCKS_OFF
  zeroFields := [(ST_PAD1_OFF, 8), (ST_PAD2_OFF, 4), (ST_UNUSED45_OFF, 8)]
  stableRanges := [(0, ST_PAD1_OFF), (ST_PAD1_OFF, 8), (ST_BLKSIZE_OFF, 8)]

/-- x86-64 `STAT_SIZE`. -/
def STAT_SIZE_X86 : Int := 144
/-- x86-64 `st_nlink` offset (8 bytes). -/
def ST_NLINK_OFF_X86 : Nat := 16
/-- x86-64 `st_mode` offset. -/
def ST_MODE_OFF_X86 : Nat := 24
/-- x86-64 `__pad0` offset (4 bytes). -/
def ST_PAD0_OFF_X86 : Nat := 36
/-- x86-64 `st_rdev` offset. -/
def ST_RDEV_OFF_X86 : Nat := 40
/-- x86-64 `st_size` offset. -/
def ST_SIZE_OFF_X86 : Nat := 48
/-- x86-64 `st_blksize` offset (8 bytes). -/
def ST_BLKSIZE_OFF_X86 : Nat := 56
/-- x86-64 `st_blocks` offset. -/
def ST_BLOCKS_OFF_X86 : Nat := 64
/-- x86-64 `__unused[3]` offset (24 bytes). -/
def ST_UNUSED_OFF_X86 : Nat := 120

/-- The x86-64 `struct stat` (`arch/x86/include/uapi/asm/stat.h`). -/
def statLayoutX86 : StatLayout where
  size := 144
  modeOff := ST_MODE_OFF_X86
  rdevOff := ST_RDEV_OFF_X86
  sizeOff := ST_SIZE_OFF_X86
  blocksOff := ST_BLOCKS_OFF_X86
  zeroFields := [(ST_PAD0_OFF_X86, 4), (ST_UNUSED_OFF_X86, 24)]
  stableRanges := [(0, ST_SIZE_OFF_X86), (ST_BLKSIZE_OFF_X86, 8)]

namespace StatLayout

variable (L : StatLayout)

/-- `stat_ifmt` at a layout. -/
def ifmt (bs : List Byte) : Int := zland (statFieldLe L.modeOff 4 bs) S_IFMT
/-- `stat_is_reg` at a layout. -/
def isReg (bs : List Byte) : Bool := L.ifmt bs == S_IFREG
/-- `stat_buf_wf` at a layout. -/
def bufWf (bs : List Byte) : Bool :=
  bs.length == L.size && ifmtValid (L.ifmt bs) &&
    L.zeroFields.all fun f => statFieldLe f.1 f.2 bs == 0
/-- `stat_size_ok` at a layout. -/
def sizeOk (n : Nat) (bs : List Byte) : Bool :=
  !L.isReg bs || statFieldLe L.sizeOff 8 bs == uns (zw n)
/-- `stat_chrdev_ok` at a layout. -/
def chrdevOk (rdev : Int) (bs : List Byte) : Bool :=
  L.ifmt bs == S_IFCHR && statFieldLe L.rdevOff 8 bs == rdev &&
    statFieldLe L.sizeOff 8 bs == 0 && statFieldLe L.blocksOff 8 bs == 0
/-- `stat_stable_eqb` at a layout. -/
def stableEqb (b1 b2 : List Byte) : Bool :=
  L.stableRanges.all fun r => statBytesEqb ((b1.drop r.1).take r.2) ((b2.drop r.1).take r.2)
/-- `stat_set_size` at a layout. -/
def setSize (n : Nat) (bs : List Byte) : List Byte :=
  bs.take L.sizeOff ++ zToLeBytes 8 n ++ bs.drop (L.sizeOff + 8)

end StatLayout

theorem statLayoutLps_ifmt (bs : List Byte) : statLayoutLps.ifmt bs = statIfmt bs := rfl

theorem statLayoutLps_bufWf (bs : List Byte) : statLayoutLps.bufWf bs = statBufWf bs := by
  simp [StatLayout.bufWf, statBufWf, statLayoutLps, statIfmtValid, StatLayout.ifmt, statIfmt,
    Bool.and_assoc]

theorem statLayoutLps_sizeOk (n : Nat) (bs : List Byte) :
    statLayoutLps.sizeOk n bs = statSizeOk n bs := rfl

theorem statLayoutLps_chrdevOk (rdev : Int) (bs : List Byte) :
    statLayoutLps.chrdevOk rdev bs = statChrdevOk rdev bs := rfl

theorem statLayoutLps_stableEqb (b1 b2 : List Byte) :
    statLayoutLps.stableEqb b1 b2 = statStableEqb b1 b2 := by
  simp [StatLayout.stableEqb, statStableEqb, statLayoutLps, Bool.and_assoc]

theorem statLayoutLps_setSize (n : Nat) (bs : List Byte) :
    statLayoutLps.setSize n bs = statSetSize n bs := rfl

/-- x86-64 `stat_buf_wf`: 144 bytes, a file type at 24, `__pad0` and `__unused` zero. -/
def statBufWfX86 (bs : List Byte) : Bool := statLayoutX86.bufWf bs
/-- x86-64 `stat_is_reg`. -/
def statIsRegX86 (bs : List Byte) : Bool := statLayoutX86.isReg bs
/-- x86-64 `stat_size_ok`. -/
def statSizeOkX86 (n : Nat) (bs : List Byte) : Bool := statLayoutX86.sizeOk n bs
/-- x86-64 `stat_devnull_ok`. -/
def statDevnullOkX86 (bs : List Byte) : Bool := statLayoutX86.chrdevOk DEVNULL_RDEV bs
/-- x86-64 `stat_urandom_ok`. -/
def statUrandomOkX86 (bs : List Byte) : Bool := statLayoutX86.chrdevOk URANDOM_RDEV bs
/-- x86-64 `stat_stable_eqb`. -/
def statStableEqbX86 (b1 b2 : List Byte) : Bool := statLayoutX86.stableEqb b1 b2
/-- x86-64 `stat_set_size`. -/
def statSetSizeX86 (n : Nat) (bs : List Byte) : List Byte := statLayoutX86.setSize n bs

end Silmaril.Process.LPS
