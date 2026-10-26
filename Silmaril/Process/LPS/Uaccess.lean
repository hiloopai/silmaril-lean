module

public import Silmaril.Process.LPS.Syscall
public import Silmaril.Process.LPS.Architecture

/-!
# LPS in Lean: the user-memory boundary (`Sys/Uaccess.v`, `State.v:1024-1760`)

The user-buffer gates of LPS `Sys/Uaccess.v` are in `Syscall` (`rwBytesMax`,
`modeledRwCount`, `modeledRwRange`, `accessOkZero`, `writeSource`, `deliveredWrites`); this
module adds the lemmas of `Sys/Uaccess.v` that discharge them, and the user-memory readers of
`State.v` that several syscall families share:

* pathnames (`read_cstr`, `cstr_access_len_aux`, `path_max`): the three answers of
  `getname()`, a string, `ENAMETOOLONG` or `EFAULT`;
* `copy_bytes_map`: `access_ok` and then the copy, the shape of `copy_{from,to}_user`;
* `struct iovec` arrays (`read_iovec_entry`, `copy_iovecs_aux`, `import_iovecs`, …): the
  index-ordered `EFAULT`/`EINVAL` of `copy_iovec_from_user` and `__import_iovec`, the
  aggregate `MAX_RW_COUNT` cap, and the scatter/gather of `readv`/`writev`;
* the remaining argument narrowings of `Sys/Syscall.v` (`uid32`, `sint32`, …) and
  `outcome_copyins`.

## x86-64: `access_ok`

LPS's `access_okb` (`State.v:1344`) is the generic `__access_ok`
(`include/asm-generic/access_ok.h`) against riscv64's Sv48 `TASK_SIZE = 2^47`. x86-64 has its
own (`arch/x86/include/asm/uaccess_64.h`, `__access_ok`):

```
if (__builtin_constant_p(size <= PAGE_SIZE) && size <= PAGE_SIZE)
        return valid_user_address(ptr);
sum = size + ptr;  return valid_user_address(sum) && sum >= ptr;
```

with `valid_user_address(x) := x <= USER_PTR_MAX` (`uaccess_64.h:56`) and
`USER_PTR_MAX = TASK_SIZE_MAX` (`arch/x86/kernel/cpu/common.c:2592`, `arch_cpu_finalize_init`;
the LAM widening there is disabled). Line numbers are Linux v6.18.46, the version LPS pins.
(v6.12 set `USER_PTR_MAX = TASK_SIZE_MAX - 1`, and v6.7 to v6.11 tested only the sign bit, so
the bound is version-specific.) Finally, `TASK_SIZE_MAX = 2^47 - PAGE_SIZE` with 4-level paging, `2^56 - PAGE_SIZE`
with LA57 (`arch/x86/include/asm/page_64_types.h`). `accessOkbX86` is the general (`sum`)
branch. The constant-size branch checks only the base pointer; it differs from the `sum`
branch only for ranges that reach into the guard page at `TASK_SIZE_MAX`, where the copy
itself then faults, so both answer `EFAULT` provided the model never maps the guard page.
The difference from LPS is the last page below `2^47`: LPS accepts a range ending there,
x86-64 refuses it. `accessOkZeroX86`, `copyBytesMapX86` and `importIovecsX86` are the
x86-64 forms of the helpers that consult `access_ok`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-! ## Lemmas of `Sys/Uaccess.v` -/

/-- LPS `State.v:1153` `rw_count_clamp_small`. -/
theorem rwCountClamp_small (count : Word) (h : uns count ≤ MAX_RW_COUNT) :
    rwCountClamp count = uns count := by
  simp [rwCountClamp, h]

/-- `Z_to_bv 64 (bv_unsigned w) = w`. -/
theorem zw_uns (w : Word) : zw (uns w) = w := by
  simp [zw, uns]

/-- LPS `Sys/Uaccess.v:406` `access_okb_intro`. -/
theorem accessOkb_intro (buf count : Word) (h : uns buf + uns count ≤ taskSize) :
    accessOkb buf (uns count) = true := by
  have hb : 0 ≤ uns buf := by simp [uns]
  have hc : 0 ≤ uns count := by simp [uns]
  simp only [accessOkb_legacy_def, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- LPS `Sys/Uaccess.v:416` `access_okb_le`. -/
theorem accessOkb_le (buf count : Word) (h : accessOkb buf (uns count) = true) :
    uns buf + uns count ≤ taskSize := by
  simp only [accessOkb_legacy_def, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- LPS `Sys/Uaccess.v:450` `rw_count_in_range`. -/
theorem rwCount_in_range (count : Word) (h : uns count ≤ rwBytesMax) :
    (!modeledRwCount count) = false := by
  simp [modeledRwCount, h]

/-- LPS `Sys/Uaccess.v:460` `rw_range_in_range`. -/
theorem rwRange_in_range (buf count : Word) (h : uns count ≤ rwBytesMax) :
    (!modeledRwRange buf count) = false := by
  simp [modeledRwRange, modeledRwCount, h]

/-- LPS `Sys/Uaccess.v:469` `rw_range_of_access_ok`. -/
theorem rwRange_of_accessOk (buf count : Word) (h : accessOkb buf (uns count) = true) :
    (!modeledRwRange buf count) = false := by
  simp [modeledRwRange, h]

/-- LPS `Sys/Uaccess.v:479` `rw_count_clamp_of_rw`. -/
theorem rwCountClamp_of_rw (count : Word) (h : uns count ≤ rwBytesMax) :
    rwCountClamp count = uns count :=
  rwCountClamp_small count (by unfold rwBytesMax at h; unfold MAX_RW_COUNT; omega)

/-- LPS `State.v:1012` `readable_bytes_length_le` (on the plain walk). -/
theorem readableBytesAux_length_le (mp : Word → Option Byte) (a : Word) (k : Nat) :
    (readableBytesAux mp a k).length ≤ k := by
  induction k generalizing a with
  | zero => simp [readableBytesAux]
  | succ k ih =>
    simp only [readableBytesAux]
    split
    · simp
    · simpa using ih (a + 1)

/-- LPS `Sys/Uaccess.v:513` `write_source_small`. -/
theorem writeSource_small (mp : Word → Option Byte) (buf count : Word)
    (h : uns count ≤ MAX_RW_COUNT) : writeSource mp buf count = readableBytes mp buf count := by
  simp [writeSource, rwCountClamp_small count h, zw_uns]

/-- LPS `Sys/Uaccess.v:523` `write_source_of_rw`. -/
theorem writeSource_of_rw (mp : Word → Option Byte) (buf count : Word)
    (h : uns count ≤ rwBytesMax) : writeSource mp buf count = readableBytes mp buf count :=
  writeSource_small mp buf count (by unfold rwBytesMax at h; unfold MAX_RW_COUNT; omega)

/-! ## Argument narrowings and copy-ins (`Sys/Syscall.v`) -/

/-- LPS `Sys/Syscall.v:56` `outcome_copyins`. -/
def outcomeCopyins (reads : List (Word × Nat)) : Outcome SyscallEffect → Outcome SyscallEffect
  | .ok eff m evs => .ok (eff.withCopyins (reads ++ eff.copyins)) m evs
  | .unmodeled => .unmodeled

/-- LPS `Sys/Syscall.v:179` `whence32`. -/
def whence32 (whence : Word) : Word := abiLow32 whence
/-- LPS `Sys/Syscall.v:196` `cmd32`. -/
def cmd32 (cmd : Word) : Word := abiLow32 cmd
/-- LPS `Sys/Syscall.v:225` `clockid32`. -/
def clockid32 (clkid : Word) : Word := abiLow32 clkid
/-- LPS `Sys/Syscall.v:249` `uid32`. -/
def uid32 (u : Word) : Word := abiLow32 u
/-- LPS `Sys/Syscall.v:277` `flag32`. -/
def flag32 (flag : Word) : Word := abiLow32 flag
/-- LPS `Sys/Syscall.v:284` `nfds32`. -/
def nfds32 (n : Word) : Word := abiLow32 n
/-- LPS `Sys/Syscall.v:295` `unfds32`. -/
def unfds32 (nfds : Word) : Word := abiLow32 nfds
/-- LPS `Sys/Syscall.v:297` `nfds_signed`: a narrowed word read as a signed `int`. -/
def nfdsSigned (n32 : Word) : Int :=
  let v := uns n32
  if v < 2 ^ 31 then v else v - 2 ^ 32
/-- LPS `Sys/Syscall.v:304` `sint32`: the low 32 bits read as a signed `int`. -/
def sint32 (w : Word) : Int :=
  let u := uns (abiLow32 w)
  if u < 2 ^ 31 then u else u - 2 ^ 32
/-- LPS `Sys/Syscall.v:316` `how32`. -/
def how32 (how : Word) : Word := abiLow32 how
/-- LPS `Sys/Syscall.v:334` `pipe_flags32`. -/
def pipeFlags32 (flags : Word) : Word := abiLow32 flags

/-! ## Pathnames (`State.v:1024-1080`) -/

/-- LPS `State.v:1024` `path_max`: `PATH_MAX`, counting the terminator. -/
def pathMax : Nat := 4096

/-- LPS `State.v:1035` `cstr_access_len_aux`: the bytes counted as read, through the first
NUL, the first unreadable byte, or the fuel. -/
def cstrAccessLenAux (mp : Word → Option Byte) (a : Word) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    match mp a with
    | none => 1
    | some b => if b == 0 then 1 else cstrAccessLenAux mp (a + 1) fuel + 1

/-- LPS `State.v:1054` `cstr_result`: a pathname read out of user memory. -/
inductive CstrResult where
  /-- NUL-terminated within `PATH_MAX`. -/
  | ok (p : List Byte)
  /-- no NUL within `PATH_MAX`: `ENAMETOOLONG`. -/
  | tooLong
  /-- an unmapped byte before the NUL: `EFAULT`. -/
  | fault
  deriving DecidableEq, Repr

/-- LPS `State.v:1059` `read_cstr_aux`. -/
def readCstrAux (mp : Word → Option Byte) (a : Word) : Nat → CstrResult
  | 0 => .tooLong
  | k + 1 =>
    match mp a with
    | none => .fault
    | some b =>
      if b == 0 then .ok []
      else match readCstrAux mp (a + 1) k with
        | .ok r => .ok (b :: r)
        | r => r

/-- LPS `State.v:1075` `read_cstr`. -/
def readCstr (mp : Word → Option Byte) (a : Word) : CstrResult := readCstrAux mp a pathMax

/-! ## `copy_{from,to}_user` (`State.v:1375`) -/

/-- LPS `State.v:1375` `copy_bytes_map`: `access_ok` over the whole range, then the copy. -/
def copyBytesMap (mp : Word → Option Byte) (a : Word) (len : Int) : Option (List Byte) :=
  if accessOkb a len then readBytesMap mp a (zw len) else none

/-- LPS `State.v:1383` `copy_bytes_map_refused`. -/
theorem copyBytesMap_refused (mp : Word → Option Byte) (a : Word) (len : Int)
    (h : accessOkb a len = false) : copyBytesMap mp a len = none := by
  simp [copyBytesMap, h]

/-- LPS `State.v:1390` `copy_bytes_map_accepted`. -/
theorem copyBytesMap_accepted (mp : Word → Option Byte) (a : Word) (len : Int)
    (h : accessOkb a len = true) : copyBytesMap mp a len = readBytesMap mp a (zw len) := by
  simp [copyBytesMap, h]

/-! ## `struct iovec` arrays (`State.v:1104-1760`) -/

/-- LPS `State.v:1104` `read_iovecs_aux`: the layout decode alone (16-byte entries, base then
length), with no validation. -/
def readIovecsAux (mp : Word → Option Byte) (a : Word) : Nat → Option (List (Word × Word))
  | 0 => some []
  | k + 1 =>
    match readU64 mp a, readU64 mp (a + 8) with
    | some base, some len => (readIovecsAux mp (a + 16) k).map ((base, len) :: ·)
    | _, _ => none

/-- LPS `State.v:1182` `IOV_MAX` (`UIO_MAXIOV`). -/
def IOV_MAX : Int := 1024

/-- LPS `State.v:1202` `read_iovecs`: at most `IOV_MAX` entries. -/
def readIovecs (mp : Word → Option Byte) (a cnt : Word) : Option (List (Word × Word)) :=
  readIovecsAux mp a (wordToNatBounded cnt IOV_MAX.toNat)

/-- LPS `State.v:1399` `iov_import`: the result of `__import_iovec`. -/
inductive IovImport where
  | ok (iovs : List (Word × Word))
  | fault
  | inval
  deriving DecidableEq, Repr

/-- LPS `State.v:1411` `iov_entry`: one descriptor as `copy_iovec_from_user` fetches it. -/
inductive IovEntry where
  | entry (base len : Word)
  | fault
  | inval
  deriving DecidableEq, Repr

/-- LPS `State.v:1416` `read_iovec_entry`: both fields are loaded, then a length negative as
`ssize_t` is `EINVAL`. -/
def readIovecEntry (mp : Word → Option Byte) (a : Word) : IovEntry :=
  match readU64 mp a, readU64 mp (a + 8) with
  | some base, some len => if 2 ^ 63 ≤ uns len then .inval else .entry base len
  | _, _ => .fault

/-- LPS `State.v:1436` `copy_iovecs_aux`: the first error in index order decides. -/
def copyIovecsAux (mp : Word → Option Byte) (a : Word) : Nat → IovImport
  | 0 => .ok []
  | k + 1 =>
    match readIovecEntry mp a with
    | .fault => .fault
    | .inval => .inval
    | .entry base len =>
      match copyIovecsAux mp (a + 16) k with
      | .ok r => .ok ((base, len) :: r)
      | r => r

/-- LPS `State.v:1456` `copy_iovecs_accesses`: the descriptor ranges read. -/
def copyIovecsAccesses (mp : Word → Option Byte) (a : Word) : Nat → List (Word × Nat)
  | 0 => []
  | k + 1 =>
    (a, 16) :: match readIovecEntry mp a with
      | .entry _ _ => copyIovecsAccesses mp (a + 16) k
      | _ => []

/-- LPS `State.v:1471` `iovs_access_okb`, over a range predicate. -/
def iovsAccessOkbWith (ok : Word → Int → Bool) (iovs : List (Word × Word)) : Bool :=
  iovs.all fun bl => ok bl.1 (uns bl.2)

/-- LPS `State.v:1471` `iovs_access_okb`: `access_ok` on every uncapped length. -/
def iovsAccessOkb (iovs : List (Word × Word)) : Bool := iovsAccessOkbWith accessOkb iovs

/-- LPS `State.v:1480` `cap_iovecs_aux`. -/
def capIovecsAux : List (Word × Word) → Int → List (Word × Word)
  | [], _ => []
  | (base, len) :: rest, left =>
    let n := min left (uns len)
    (base, zw n) :: capIovecsAux rest (left - n)

/-- LPS `State.v:1489` `cap_iovecs`: the aggregate `MAX_RW_COUNT` cap. -/
def capIovecs (iovs : List (Word × Word)) : List (Word × Word) := capIovecsAux iovs MAX_RW_COUNT

/-- LPS `State.v:1529` `import_iovecs`, over the `access_ok` predicate: a count of one takes
`__import_iovec_ubuf` (cap, then `access_ok` on the capped length); otherwise `IOV_MAX`, the
array's `access_ok`, the index-ordered copy, then `access_ok` on every uncapped length. -/
def importIovecsWith (ok : Word → Int → Bool) (mp : Word → Option Byte) (a n : Word) :
    IovImport :=
  if n == 1 then
    if !ok a 16 then .fault
    else match readIovecEntry mp a with
      | .fault => .fault
      | .inval => .inval
      | .entry base len =>
        if !ok base (min (uns len) MAX_RW_COUNT) then .fault else .ok [(base, len)]
  else if n == 0 then .ok []
  else if IOV_MAX < uns n then .inval
  else if !ok a (16 * uns n) then .fault
  else match copyIovecsAux mp a (wordToNat n) with
    | .ok iovs => if iovsAccessOkbWith ok iovs then .ok iovs else .fault
    | r => r

/-- LPS `State.v:1529` `import_iovecs`. -/
def importIovecs (mp : Word → Option Byte) (a n : Word) : IovImport :=
  importIovecsWith accessOkb mp a n

/-- LPS `State.v:1550` `import_iovecs_accesses`, over the `access_ok` predicate. -/
def importIovecsAccessesWith (ok : Word → Int → Bool) (mp : Word → Option Byte) (a n : Word) :
    List (Word × Nat) :=
  if n == 1 then (if !ok a 16 then [] else [(a, 16)])
  else if n == 0 then []
  else if IOV_MAX < uns n then []
  else if !ok a (16 * uns n) then []
  else copyIovecsAccesses mp a (wordToNat n)

/-- LPS `State.v:1550` `import_iovecs_accesses`. -/
def importIovecsAccesses (mp : Word → Option Byte) (a n : Word) : List (Word × Nat) :=
  importIovecsAccessesWith accessOkb mp a n

/-- LPS `State.v:1565` `iov_prefix_accesses`: the ranges of the first `left` bytes. -/
def iovPrefixAccesses : List (Word × Word) → Nat → List (Word × Nat)
  | _, 0 => []
  | [], _ => []
  | (base, len) :: rest, left@(_ + 1) =>
    let n := wordToNatBounded len left
    if n == 0 then iovPrefixAccesses rest left else (base, n) :: iovPrefixAccesses rest (left - n)

/-- LPS `State.v:1580` `scatter_iovecs`: lay `bs` over the vectors, every delivered byte
writable; zero-length pieces produce no write. -/
def scatterIovecs (mp : Word → Option Byte) : List (Word × Word) → List Byte →
    Option (List (Word × List Byte))
  | _, [] => some []
  | [], _ :: _ => none
  | (base, len) :: rest, bs@(_ :: _) =>
    let n := wordToNatBounded len bs.length
    let here := bs.take n
    let later := bs.drop n
    match here with
    | [] => scatterIovecs mp rest later
    | _ :: _ =>
      match readBytesMap mp base (lenWord here), scatterIovecs mp rest later with
      | some _, some writes => some ((base, here) :: writes)
      | _, _ => none

/-- LPS `State.v:1634` `scatter_iovecs_nil`. -/
theorem scatterIovecs_nil (mp : Word → Option Byte) (iovs : List (Word × Word)) :
    scatterIovecs mp iovs [] = some [] := by
  cases iovs <;> rfl

/-- LPS `State.v:1666` `gather_iovecs`: the flattened source, or `none` on any unreadable
byte. -/
def gatherIovecs (mp : Word → Option Byte) : List (Word × Word) → Option (List Byte)
  | [] => some []
  | (base, len) :: r =>
    match readBytesMap mp base len with
    | none => none
    | some bs => (gatherIovecs mp r).map (bs ++ ·)

/-- LPS `State.v:1691` `gather_prefix`: the bytes a `writev` moves before faulting. -/
def gatherPrefix (mp : Word → Option Byte) : List (Word × Word) → List Byte
  | [] => []
  | (base, len) :: r =>
    let bs := readableBytes mp base len
    if (bs.length : Int) = uns len then bs ++ gatherPrefix mp r else bs

/-- LPS `State.v:1706` `iovs_total`: the requested total, in `Int`. -/
def iovsTotal : List (Word × Word) → Int
  | [] => 0
  | (_, len) :: r => uns len + iovsTotal r

/-- LPS `State.v:1712` `iovs_total_nonneg`. -/
theorem iovsTotal_nonneg (iovs : List (Word × Word)) : 0 ≤ iovsTotal iovs := by
  induction iovs with
  | nil => simp [iovsTotal]
  | cons p r ih =>
    obtain ⟨b, l⟩ := p
    have : 0 ≤ uns l := by simp [uns]
    simp only [iovsTotal]
    omega

/-- LPS `State.v:1756` `writev_gathered`: `writev` gathers over the capped vector. -/
def writevGathered (mp : Word → Option Byte) (iovs0 : List (Word × Word)) : List Byte :=
  gatherPrefix mp (capIovecs iovs0)

/-! ## x86-64 `access_ok`

`accessOkbX86` is the whole-range (second) branch of x86-64 `__access_ok`. It is the branch
that `copy_to_user`/`copy_from_user` reach on x86-64, whatever the size at the call site:
x86-64 defines neither `INLINE_COPY_TO_USER` nor `INLINE_COPY_FROM_USER`
(`arch/x86/include/asm/uaccess.h`, `uaccess_64.h`, v6.12), so `copy_to_user` calls the
out-of-line `_copy_to_user` (`include/linux/uaccess.h`, `lib/usercopy.c`), whose
`access_ok(to, n)` sees a non-constant `n`. A constant-size `copy_to_user` (`uname`'s
`struct new_utsname`, `prlimit64`'s `struct rlimit64`, `fstat`'s `struct stat`, `pipe2`'s
two `int`s, `sched_setscheduler`'s `struct sched_param`) therefore fails `access_ok` on a
range that ends above `TASK_SIZE_MAX` and answers `-EFAULT` with no bytes copied, which is
what those arms model. The base-only branch is for accesses inlined with a constant size,
such as `get_user`/`put_user` and the futex `access_ok`; those go through
`Sys/AccessGate.lean`'s `accessGateSmallX86`. -/

/-- x86-64 `TASK_SIZE_MAX` with 4-level paging: `(1 << 47) - PAGE_SIZE`
(`arch/x86/include/asm/page_64_types.h`). -/
def taskSizeMaxX86 : Int := 2 ^ 47 - 4096

/-- x86-64 `TASK_SIZE_MAX` with 5-level paging (LA57): `(1 << 56) - PAGE_SIZE`. -/
def taskSizeMaxX86La57 : Int := 2 ^ 56 - 4096

/-- x86-64 `__access_ok` (`arch/x86/include/asm/uaccess_64.h`), general branch, against
`USER_PTR_MAX = userPtrMax`: the 64-bit sum `size + ptr` must not wrap and must be at most
`USER_PTR_MAX`. -/
def accessOkbX86With (userPtrMax : Int) (base : Word) (len : Int) : Bool :=
  let sum := (len % twoPow64 + uns base) % twoPow64
  decide (sum ≤ userPtrMax) && decide (uns base ≤ sum)

/-- x86-64 `access_ok` with 4-level paging (the x86-64 counterpart of LPS `State.v:1344`
`access_okb`). -/
def accessOkbX86 (base : Word) (len : Int) : Bool := accessOkbX86With taskSizeMaxX86 base len

/-- x86-64 form of LPS `Sys/Uaccess.v:442` `access_ok_zero`. -/
def accessOkZeroX86 (buf count : Word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if accessOkbX86 buf (uns count) then k else errRet EFAULT

/-- x86-64 form of LPS `State.v:1375` `copy_bytes_map`. -/
def copyBytesMapX86 (mp : Word → Option Byte) (a : Word) (len : Int) : Option (List Byte) :=
  if accessOkbX86 a len then readBytesMap mp a (zw len) else none

/-- x86-64 form of LPS `State.v:1529` `import_iovecs`. -/
def importIovecsX86 (mp : Word → Option Byte) (a n : Word) : IovImport :=
  importIovecsWith accessOkbX86 mp a n

/-- x86-64 form of LPS `State.v:1550` `import_iovecs_accesses`. -/
def importIovecsAccessesX86 (mp : Word → Option Byte) (a n : Word) : List (Word × Nat) :=
  importIovecsAccessesWith accessOkbX86 mp a n

/-- For a length that is a valid `unsigned long`, x86-64 `access_ok` holds exactly when the
range ends at or below `TASK_SIZE_MAX` (compare `accessOkb_le`, whose bound is `2^47`). -/
theorem accessOkbX86_iff (base : Word) (len : Int) (h0 : 0 ≤ len) (h1 : len < twoPow64) :
    accessOkbX86 base len = true ↔ uns base + len ≤ taskSizeMaxX86 := by
  have e1 : twoPow64 = 18446744073709551616 := by unfold twoPow64; decide
  have e2 : taskSizeMaxX86 = 140737488351232 := by unfold taskSizeMaxX86; decide
  have hb : base.toNat < 18446744073709551616 := base.isLt
  simp only [accessOkbX86, accessOkbX86With, Bool.and_eq_true, decide_eq_true_eq, e1, e2, uns]
  rw [e1] at h1
  omega

/-- The lanes' `TASK_SIZE_MAX` is the boundary of the x86-64 address-space profile used by the
launch code and `arch_prctl` (`Architecture.lean`). -/
theorem taskSizeMaxX86_eq : taskSizeMaxX86 = x86AddressSpace.taskSize := by
  unfold taskSizeMaxX86 x86AddressSpace; decide

/-- For a valid `unsigned long` length, the lanes' x86-64 `access_ok` (64-bit-sum form) is the
profile check `accessOkbFor x86AddressSpace` (`Architecture.lean`): one bound, two spellings. -/
theorem accessOkbX86_eq_accessOkbFor (base : Word) (len : Int) (h0 : 0 ≤ len)
    (h1 : len < twoPow64) : accessOkbX86 base len = accessOkbFor x86AddressSpace base len := by
  rw [Bool.eq_iff_iff, accessOkbX86_iff base len h0 h1, taskSizeMaxX86_eq]
  have hb : 0 ≤ uns base := Int.natCast_nonneg _
  simp only [accessOkbFor, Bool.and_eq_true, decide_eq_true_eq]
  omega

end Silmaril.Process.LPS
