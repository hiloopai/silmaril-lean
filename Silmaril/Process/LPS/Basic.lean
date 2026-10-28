module

public import Mathlib.Data.BitVec
public import Mathlib.Data.Int.Basic

/-!
# LPS in Lean: words, bytes and the address-space constants

This directory is an agentic translation into Lean of the Linux process layer of
**LPS** (`rocq-linux-process-semantics`, Theorem Labs, MIT licence, copyright (c) 2026
Theorem Labs, PBC), at upstream commit `f1006fe8178338a499b5e5c41be83006c4edd058`, which is
the commit that OSS Verify pins (`oss-verify-proofs/release.yaml`). The statement shapes come
from `oss-verify-proofs` (same licence) at the imported commit
`98e995d4daced70a0a4aa2c810854b88720735f1`. Its `Shapes.v` is byte-identical to the
historical `8f5f46768858af236a4270f9628e6beed9aa0e72` pin; see `docs/LPSShapesParity.md`.

Every translated definition names its upstream file and line in its docstring, written
`LPS State.v:33` for `theories/LinuxProcessSem/State.v` line 33 (`Sys/…` paths are under
`theories/LinuxProcessSem/Sys/`, `Equivalence.v` and friends under
`theories/EquivalenceDefinition/`, and `Shapes.v` under `oss-verify-proofs/theories/`).
The full correspondence table is `docs/LPSProcess.md`.

Translation conventions:

* `word` (stdpp `bv 64`) is `BitVec 64`; `byte` is `BitVec 8`, which is `Process.Byte`.
* `bv_unsigned w` is `uns w := (w.toNat : Int)`, and `Z_to_bv 64 z` is `BitVec.ofInt 64 z`.
  Rocq's `Z.div`/`Z.modulo` by a positive divisor agree with Lean's `Int` `/` and `%`.
* Integer constants stay in `Int` (`Z`), so that the arithmetic reads like the source.

This file covers `BvBase.v` and the constants at the top of `State.v`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `BvBase.v` / `Riscv/Prelude.v`: a 64-bit machine word. -/
abbrev Word := BitVec 64
/-- LPS `BvBase.v:23` `byte`. -/
abbrev Byte := BitVec 8

/-- `bv_unsigned`: the unsigned value of a bit vector, as an integer. -/
def uns {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `Z_to_bv 64`. -/
def zw (z : Int) : Word := BitVec.ofInt 64 z

/-- `Z_to_bv 8`. -/
def zb (z : Int) : Byte := BitVec.ofInt 8 z

/-- LPS `BvBase.v:31` `len_word`. -/
def lenWord {α : Type} (l : List α) : Word := zw l.length

/-- LPS `BvBase.v:35` `word_to_nat`. -/
def wordToNat (w : Word) : Nat := w.toNat

/-- LPS `BvBase.v:36` `nat_to_word`. -/
def natToWord (n : Nat) : Word := zw n

/-- LPS `BvBase.v:43` `word_to_nat_bounded`. -/
def wordToNatBounded (w : Word) (bound : Nat) : Nat :=
  if uns w ≤ bound then wordToNat w else bound

/-- LPS `BvBase.v:66` `word_le8`: the eight little-endian bytes of a word. -/
def wordLe8 (v : Word) : List Byte :=
  (List.range 8).map fun k => v.extractLsb' (8 * k) 8

/-- LPS `BvBase.v:148` `word_le4`. -/
def wordLe4 (v : Word) : List Byte :=
  (List.range 4).map fun k => v.extractLsb' (8 * k) 8

/-- LPS `BvBase.v:26` `bv_leu`: unsigned `≤` as a boolean. -/
def bvLeu {n : Nat} (a b : BitVec n) : Bool := decide (uns a ≤ uns b)

/-- LPS `BvBase.v:73` `le2`: little-endian assembly (`bv_concat` puts its first argument in
the high bits, as `++` does). -/
def le2 (b1 b0 : Byte) : BitVec 16 := b1 ++ b0
/-- LPS `BvBase.v:74` `le4`. -/
def le4 (b3 b2 b1 b0 : Byte) : BitVec 32 := le2 b3 b2 ++ le2 b1 b0
/-- LPS `BvBase.v:76` `le8`. -/
def le8 (b7 b6 b5 b4 b3 b2 b1 b0 : Byte) : Word := le4 b7 b6 b5 b4 ++ le4 b3 b2 b1 b0

/-- LPS `BvBase.v:85` `bytes_le_to_Z` (its values are non-negative, so it is computed in `ℕ`). -/
def bytesLeToNat : List Byte → Nat
  | [] => 0
  | b :: rest => b.toNat ||| (bytesLeToNat rest <<< 8)

/-- LPS `BvBase.v:85` `bytes_le_to_Z`. -/
def bytesLeToZ (bs : List Byte) : Int := bytesLeToNat bs

/-- LPS `BvBase.v:93` `le_bytes_to_word`. -/
def leBytesToWord (bs : List Byte) : Word := zw (bytesLeToZ bs)

/-- LPS `BvBase.v:101` `Z_to_le_bytes`. -/
def zToLeBytes : Nat → Int → List Byte
  | 0, _ => []
  | n + 1, z => zb z :: zToLeBytes n (z >>> 8)

/-! ## Address-space constants (LPS `State.v:33-469`) -/

/-- LPS `State.v:33` `two_pow_64`. -/
def twoPow64 : Int := 2 ^ 64
/-- LPS `State.v:34` `page_size`. -/
def pageSize : Int := 4096
/-- LPS `State.v:39` `page_round_up_Z`. -/
def pageRoundUp (n : Int) : Int := (n + pageSize - 1) / pageSize * pageSize
/-- LPS `State.v:41` `page_round_down_Z`. -/
def pageRoundDown (n : Int) : Int := n / pageSize * pageSize
/-- LPS `State.v:80` `stack_max_size`: the 8 MiB `RLIMIT_STACK` the model fixes. -/
def stackMaxSize : Int := 8 * 1024 * 1024
/-- LPS `State.v:112` `sp_window_lo`. -/
def spWindowLo : Int := 0x7fff80000000
/-- LPS `State.v:113` `sp_window_hi`. -/
def spWindowHi : Int := 0x800000000000
/-- LPS `State.v:204` `brk_aslr_max`. -/
def brkAslrMax : Int := 1 * 1024 * 1024 * 1024
/-- LPS `State.v:249` `mmap_base_min`. -/
def mmapBaseMin : Int := 0x154555557000
/-- LPS `State.v:269` `mmap_base_max`. -/
def mmapBaseMax : Int := spWindowHi - 128 * 1024 * 1024
/-- LPS `State.v:331` `TASK_SIZE` (Sv48). -/
def taskSize : Int := 0x800000000000

/-- LPS `State.v:393` `VaSize`: the declared virtual-address width. -/
inductive VaSize where
  | sv39 | sv48 | sv57
  deriving DecidableEq, Repr

/-- LPS `State.v:399` `sv39_task_size`. -/
def sv39TaskSize : Int := 0x4000000000
/-- LPS `State.v:400` `sv57_task_size`. -/
def sv57TaskSize : Int := 0x100000000000000

/-- LPS `State.v:404` `va_task_size`. -/
def vaTaskSize : VaSize → Int
  | .sv39 => sv39TaskSize
  | .sv48 => taskSize
  | .sv57 => sv57TaskSize

/-- LPS `State.v:413` `va_stack_top`. -/
def vaStackTop : VaSize → Int
  | .sv39 => sv39TaskSize
  | .sv48 => spWindowHi
  | .sv57 => spWindowHi

/-- LPS `State.v:420` `va_sp_window_hi`. -/
def vaSpWindowHi (v : VaSize) : Int := vaStackTop v
/-- LPS `State.v:421` `va_sp_window_lo`. -/
def vaSpWindowLo (v : VaSize) : Int := vaStackTop v - 2 * 1024 * 1024 * 1024
/-- LPS `State.v:424` `va_mmap_base_max`. -/
def vaMmapBaseMax (v : VaSize) : Int := vaStackTop v - 128 * 1024 * 1024
/-- LPS `State.v:426` `va_mmap_base_min`. -/
def vaMmapBaseMin : VaSize → Int
  | .sv39 => 0
  | .sv48 => mmapBaseMin
  | .sv57 => mmapBaseMin

/-- LPS `State.v:468` `source_alloc_limit`: 16 GiB for the source (plain) build. -/
def sourceAllocLimit : Int := 0x400000000
/-- LPS `State.v:469` `target_alloc_limit`: 512 GiB for the target (sanitizer) build. -/
def targetAllocLimit : Int := 0x8000000000

/-- LPS `State.v:473` `addr_is_error_b`: a return value in the errno band. -/
def addrIsError (ret : Word) : Bool := decide (twoPow64 - 4096 < uns ret)

/-- LPS `State.v:477` `errno_ret`: the raw return `-e`. -/
def errnoRet (e : Int) : Word := zw (-e)

/-! ## Errno values (LPS `State.v:480-556`) -/

/-- LPS `State.v:480` `EPERM`. -/
def EPERM : Int := 1
/-- LPS `State.v:481` `ENOENT`. -/
def ENOENT : Int := 2
/-- LPS `State.v:482` `ESRCH`. -/
def ESRCH : Int := 3
/-- LPS `State.v:517` `EINTR`. -/
def EINTR : Int := 4
/-- LPS `State.v:483` `EBADF`. -/
def EBADF : Int := 9
/-- LPS `State.v:484` `ECHILD`. -/
def ECHILD : Int := 10
/-- LPS `State.v:532` `EAGAIN`. -/
def EAGAIN : Int := 11
/-- LPS `State.v:518` `ENOMEM`. -/
def ENOMEM : Int := 12
/-- LPS `State.v:519` `EACCES`. -/
def EACCES : Int := 13
/-- LPS `State.v:485` `EFAULT`. -/
def EFAULT : Int := 14
/-- LPS `State.v:520` `EBUSY`. -/
def EBUSY : Int := 16
/-- LPS `State.v:486` `EEXIST`. -/
def EEXIST : Int := 17
/-- LPS `State.v:487` `ENOTDIR`. -/
def ENOTDIR : Int := 20
/-- LPS `State.v:488` `EISDIR`. -/
def EISDIR : Int := 21
/-- LPS `State.v:489` `EINVAL`. -/
def EINVAL : Int := 22
/-- LPS `State.v:521` `ENFILE`. -/
def ENFILE : Int := 23
/-- LPS `State.v:522` `EMFILE`. -/
def EMFILE : Int := 24
/-- LPS `State.v:490` `ENOTTY`. -/
def ENOTTY : Int := 25
/-- LPS `State.v:491` `ESPIPE`. -/
def ESPIPE : Int := 29
/-- LPS `State.v:523` `EROFS`. -/
def EROFS : Int := 30
/-- LPS `State.v:492` `EPIPE`. -/
def EPIPE : Int := 32
/-- LPS `State.v:493` `ERANGE`. -/
def ERANGE : Int := 34
/-- LPS `State.v:494` `ENAMETOOLONG`. -/
def ENAMETOOLONG : Int := 36
/-- LPS `State.v:495` `ENOTEMPTY`. -/
def ENOTEMPTY : Int := 39
/-- LPS `State.v:539` `ENOTSOCK`. -/
def ENOTSOCK : Int := 88
/-- LPS `State.v:540` `EMSGSIZE`. -/
def EMSGSIZE : Int := 90
/-- LPS `State.v:541` `ENOPROTOOPT`. -/
def ENOPROTOOPT : Int := 92
/-- LPS `State.v:542` `EPROTONOSUPPORT`. -/
def EPROTONOSUPPORT : Int := 93
/-- LPS `State.v:543` `ESOCKTNOSUPPORT`. -/
def ESOCKTNOSUPPORT : Int := 94
/-- LPS `State.v:544` `EOPNOTSUPP`. -/
def EOPNOTSUPP : Int := 95
/-- LPS `State.v:545` `EAFNOSUPPORT`. -/
def EAFNOSUPPORT : Int := 97
/-- LPS `State.v:546` `EADDRINUSE`. -/
def EADDRINUSE : Int := 98
/-- LPS `State.v:547` `ECONNRESET`. -/
def ECONNRESET : Int := 104
/-- LPS `State.v:548` `EISCONN`. -/
def EISCONN : Int := 106
/-- LPS `State.v:549` `ENOTCONN`. -/
def ENOTCONN : Int := 107
/-- LPS `State.v:550` `ETIMEDOUT`. -/
def ETIMEDOUT : Int := 110
/-- LPS `State.v:556` `ECONNREFUSED`. -/
def ECONNREFUSED : Int := 111

/-! ## UAPI constants used by the translated arms (LPS `Sys/Uapi.v:347-389`) -/

def PROT_NONE : Int := 0
def PROT_READ : Int := 1
def PROT_WRITE : Int := 2
def MAP_PRIVATE : Int := 2
def MAP_FIXED : Int := 16
def MAP_ANONYMOUS : Int := 32
def MAP_HUGETLB : Int := 262144
def MAP_FIXED_NOREPLACE : Int := 1048576
/-- LPS `Sys/Mm/Mmap.v:675` `MAP_NORESERVE`. -/
def MAP_NORESERVE : Int := 16384
def GRND_NONBLOCK : Int := 1
def GRND_RANDOM : Int := 2

end Silmaril.Process.LPS
