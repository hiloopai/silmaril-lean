module

public import Silmaril.Process.LPS.Monad

/-!
# LPS in Lean: the calling convention and the user-buffer boundary

Translation of LPS `Sys/Syscall.v` and `Sys/Uaccess.v` (upstream commit `f1006fe8`): return
helpers, the failure model's `errno_from`, the 32-bit argument narrowing the ABI performs,
and the gates on user buffers.

## The failure model

LPS distinguishes three kinds of answer:

1. a determined errno, an `ok` outcome with a negative return (for instance `EBADF`);
2. an environment-injected failure, written `alt (e ← errnoFrom L; errRet e) …` beside the
   determined answer. These are the readings "refused without cause" (resource exhaustion,
   interruption, …) that keep a program's error handling live. Which of them a statement
   admits is the `SpuriousCfg` of `Silmaril.Process.LPS.Run`;
3. `unmodeled`: the model gives up (fail closed).
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Syscall.v:19` `ret_only`. -/
def retOnly (r : Word) : Sys SyscallEffect := Sys.pure (mkEffect r [] [])

/-- LPS `Sys/Syscall.v:22` `err_ret`. -/
def errRet (e : Int) : Sys SyscallEffect := retOnly (errnoRet e)

/-- LPS `Sys/Syscall.v:27` `record_copyins`: record the user ranges the kernel read. -/
def recordCopyins (reads : List (Word × Nat)) (spec : Sys SyscallEffect) : Sys SyscallEffect :=
  Sys.bind spec fun eff => Sys.pure (eff.withCopyins (reads ++ eff.copyins))

/-- LPS `Sys/Syscall.v:77` `errno_from`: the environment picks one errno of the list. -/
def errnoFrom (es : List Int) : Sys Int := Sys.choose (· ∈ es)

/-- LPS `Sys/Syscall.v:80` `w_is0`. -/
def wIs0 (w : Word) : Bool := w == 0

/-- LPS `Sys/Syscall.v:114` `abi_low32`: the kernel reads an `int` argument from the low
32 bits of the register. -/
def abiLow32 (w : Word) : Word := zw (uns w % 2 ^ 32)

/-- LPS `Sys/Syscall.v:151` `fd32`. -/
def fd32 (fd : Word) : Word := abiLow32 fd
/-- LPS `Sys/Syscall.v:238` `int32`. -/
def int32 (w : Word) : Word := abiLow32 w
/-- LPS `Sys/Syscall.v:324` `pid32`. -/
def pid32 (upid : Word) : Word := abiLow32 upid
/-- LPS `Sys/Syscall.v:329` `waitopts32`. -/
def waitopts32 (options : Word) : Word := abiLow32 options

/-! ## User buffers (LPS `Sys/Uaccess.v`) -/

/-- LPS `Sys/Uaccess.v:319` `rw_bytes_max`. -/
def rwBytesMax : Int := 131072

/-- LPS `Sys/Uaccess.v:329` `modeled_rw_count`. -/
def modeledRwCount (count : Word) : Bool := decide (uns count ≤ rwBytesMax)

/-- LPS `Sys/Uaccess.v:397` `modeled_rw_range`. -/
def modeledRwRange (buf count : Word) : Bool :=
  modeledRwCount count || accessOkb buf (uns count)

/-- LPS `Sys/Uaccess.v:442` `access_ok_zero`. -/
def accessOkZero (buf count : Word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if accessOkb buf (uns count) then k else errRet EFAULT

/-- LPS `Sys/Uaccess.v:499` `write_source`: the readable prefix of the source buffer. -/
def writeSource (mp : Word → Option Byte) (buf count : Word) : List Byte :=
  readableBytes mp buf (zw (rwCountClamp count))

/-- LPS `Sys/Uaccess.v:536` `delivered_writes`. -/
def deliveredWrites (buf : Word) (bs : List Byte) : List (Word × List Byte) :=
  match bs with
  | [] => []
  | _ :: _ => [(buf, bs)]

end Silmaril.Process.LPS
