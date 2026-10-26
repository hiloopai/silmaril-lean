module

public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers

/-!
# Checks on the shared user-ABI layer

Positive and negative instances of the shared helpers of `Uapi`, `Uaccess` and
`StateHelpers`, each on a small concrete memory:

* pathnames: a string, `EFAULT` (an unmapped byte before the NUL) and `ENAMETOOLONG` (no NUL
  within the bound);
* `iovec` imports: success, `EINVAL` for a count over `IOV_MAX` and for a negative length,
  `EFAULT` for an unreadable descriptor and for a range `access_ok` refuses, with the
  index-ordered precedence of `copy_iovec_from_user`;
* `access_ok`: a range LPS accepts and x86-64 refuses (the last page below `2^47`);
* `struct stat`: a well-formed LPS buffer and a well-formed x86-64 buffer, each refused by
  the other layout, and a non-zero padding refused;
* derived constants, the `int` narrowings, descriptor allocation and the pipe-descriptor
  bytes.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Checks.UserAbi

open Silmaril.Process.LPS

/-- A memory holding `bs` from `base` upwards and nothing else. -/
def memOf (base : Word) (bs : List Byte) : Word → Option Byte := fun a =>
  if base.toNat ≤ a.toNat then bs[a.toNat - base.toNat]? else none

/-! ## Constants -/

example : TFD_CREATE_FLAGS = 526336 := by decide
example : EFD_FLAGS_SET = 526337 := by decide
example : FUTEX_WAIT_PRIVATE = 128 ∧ FUTEX_WAKE_PRIVATE = 129 := by decide
example : AT_FDCWD32 = 0xffffff9c := by decide
example : EP_MAX_EVENTS = 2147483647 / epollEventBytes := by decide
example : EP_MAX_EVENTS_X86 = 2147483647 / epollEventBytesX86 := by decide
example : NEW_UTSNAME_SIZE = 6 * (NEW_UTS_LEN + 1) := by decide

/-! ## Narrowings -/

example : sint32 0xffffffff = -1 := by decide
example : sint32 0x1_0000_0005 = 5 := by decide
example : uid32 0xffff_ffff_ffff_ffff = ID_MINUS_ONE := by decide
example : nfdsSigned 0x80000000 = -2147483648 := by decide

/-! ## Pathnames -/

/-- `"ab\0"` at `0x1000`. -/
def pathMem : Word → Option Byte := memOf 0x1000 [97, 98, 0]

example : readCstr pathMem 0x1000 = .ok [97, 98] := by decide
example : cstrAccessLenAux pathMem 0x1000 pathMax = 3 := by decide
/-- An unmapped byte before the NUL is `EFAULT`. -/
example : readCstr (memOf 0x1000 [97, 98]) 0x1000 = .fault := by decide
/-- No NUL within the bound is `ENAMETOOLONG`. -/
example : readCstrAux pathMem 0x1000 2 = .tooLong := by decide

/-! ## `iovec` imports -/

/-- Two descriptors at `0x1000`: `(0x2000, 5)` and `(0x3000, len1)`. -/
def iovMem (len1 : Word) : Word → Option Byte :=
  memOf 0x1000 (wordLe8 0x2000 ++ wordLe8 5 ++ wordLe8 0x3000 ++ wordLe8 len1)

example : importIovecs (iovMem 3) 0x1000 2 = .ok [(0x2000, 5), (0x3000, 3)] := by decide
example : importIovecsX86 (iovMem 3) 0x1000 2 = .ok [(0x2000, 5), (0x3000, 3)] := by decide
example : importIovecs (iovMem 3) 0x1000 0 = .ok [] := by decide
example : importIovecs (iovMem 3) 0x1000 1 = .ok [(0x2000, 5)] := by decide
/-- A count over `IOV_MAX` is `EINVAL` before any descriptor is read. -/
example : importIovecs (fun _ => none) 0x1000 1025 = .inval := by decide
/-- A length negative as `ssize_t` is `EINVAL`. -/
example : importIovecs (iovMem (2 ^ 63)) 0x1000 2 = .inval := by decide +kernel
/-- An unreadable descriptor is `EFAULT`. -/
example : importIovecs (iovMem 3) 0x1000 3 = .fault := by decide
/-- Index order: an unreadable descriptor 0 beats an `EINVAL` length at index 1. -/
example : importIovecs (memOf 0x1008 (wordLe8 5 ++ wordLe8 0x3000 ++ wordLe8 (2 ^ 63)))
    0x1000 2 = .fault := by decide
/-- A descriptor whose range leaves the address space is `EFAULT` (after the copy). -/
example : importIovecs (iovMem 0xffff_ffff_0000) 0x1000 2 = .fault := by decide
example : importIovecsAccesses (iovMem 3) 0x1000 2 = [(0x1000, 16), (0x1010, 16)] := by decide
example : iovsTotal [(0x2000, 5), (0x3000, 3)] = 8 := by decide
example : capIovecs [(0x2000, 0x7fff_f000), (0x3000, 3)] = [(0x2000, 0x7fff_f000), (0x3000, 0)] :=
  by decide

/-! ## `access_ok`: LPS against x86-64 -/

/-- A range ending exactly at `2^47`: LPS (Sv48) accepts it, x86-64 refuses it. -/
example : accessOkb (zw (2 ^ 47 - 4096)) 4096 = true := by decide
example : accessOkbX86 (zw (2 ^ 47 - 4096)) 4096 = false := by decide
/-- Both accept a range ending at `TASK_SIZE_MAX`. -/
example : accessOkbX86 (zw (2 ^ 47 - 8192)) 4096 = true := by decide
/-- A wrapping range is refused by both. -/
example : accessOkbX86 (zw (2 ^ 64 - 16)) 32 = false := by decide
example : accessOkb (zw (2 ^ 64 - 16)) 32 = false := by decide
example : copyBytesMap pathMem 0x1000 3 = some [97, 98, 0] := by decide
example : copyBytesMap pathMem (zw (2 ^ 64 - 1)) 3 = none := by decide

/-! ## `struct stat` -/

/-- A regular file's 128-byte asm-generic `struct stat` with `st_size = 3`. -/
def statLps : List Byte :=
  List.replicate 16 0 ++ [0, 0x80, 0, 0] ++ List.replicate 28 0 ++ [3] ++ List.replicate 79 0

/-- A regular file's 144-byte x86-64 `struct stat` with `st_size = 3`. -/
def statX86 : List Byte :=
  List.replicate 24 0 ++ [0, 0x80, 0, 0] ++ List.replicate 20 0 ++ [3] ++ List.replicate 95 0

example : statLps.length = 128 ∧ statX86.length = 144 := by decide +kernel
example : statBufWf statLps = true := by decide +kernel
example : statSizeOk 3 statLps = true := by decide +kernel
example : statSizeOk 4 statLps = false := by decide +kernel
example : statBufWfX86 statX86 = true := by decide +kernel
example : statSizeOkX86 3 statX86 = true := by decide +kernel
/-- Each layout refuses the other's buffer. -/
example : statBufWf statX86 = false := by decide +kernel
example : statBufWfX86 statLps = false := by decide +kernel
/-- Non-zero `__pad0` is refused on x86-64. -/
example : statBufWfX86 (statX86.set 36 1) = false := by decide +kernel
/-- No file type is refused. -/
example : statBufWf (List.replicate 128 0) = false := by decide +kernel
example : statStableEqbX86 statX86 (statSetSizeX86 9 statX86) = true := by decide +kernel
example : statSizeOkX86 9 (statSetSizeX86 9 statX86) = true := by decide +kernel
example : statStableEqbX86 statX86 (statX86.set 16 1) = false := by decide +kernel

/-! ## Descriptors, pipes and the model -/

example : allocFd [(0, .channel 0), (1, .channel 1), (2, .channel 2)] = 3 := by decide
example : allocFd2 [(0, .channel 0), (1, .channel 1), (2, .channel 2)] = 4 := by decide
example : pipeFdBytes 3 4 = [3, 0, 0, 0, 4, 0, 0, 0] := by decide
example : pipeNewId [(0, ([], 0)), (1, ([], 0))] = 2 := by decide
example : statpinLookup [([1], [7]), ([2], [8])] [2] = some [8] := by decide
example : statpinLookup [([1], [7])] [2] = none := by decide

end Silmaril.Process.LPS.Checks.UserAbi
