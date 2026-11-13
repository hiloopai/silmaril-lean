module

public import Silmaril.X86.Sep.SysV.Defs
public import Silmaril.X86.Leaf.Defs
public import Silmaril.X86.Decompile.Md5Memcpy.Defs
/-!
# Example System V specs

* `leafSpec`: the addition leaf `mov rax, rdi; add rax, rsi; ret` (`Silmaril.X86.Leaf`):
  arguments `a, b`, no stack, result `a + b`.
* `callerSpec`: the caller `call leaf; ret` (`Silmaril.X86.Leaf.callerBytes`): the same
  arguments and result, with an eight-byte stack budget for the pushed return address.
* `md5Spec`: `MD5_memcpy(output, input, len)` compiled by `clang -O0`
  (`Silmaril.X86.Decompile.Md5Memcpy`): owns `len` writable bytes at `output` (old contents
  `old`) and `len` readable bytes at `input` (contents `src`), with `0 < len < 2 ^ 32`; uses
  32 bytes of stack (the saved `rbp` and 24 bytes of red zone); returns with `src` at
  `output` and `input` unchanged. `len` is an `unsigned int`, which System V passes in `edx`
  with the upper half of `rdx` unspecified, and the code reads only `edx`; the spec is
  stronger than the ABI here, since it requires all of `rdx` to be the zero-extended
  length (`args` is a function of `Arg`).

The proofs are in `Demo/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Demo

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- The addition leaf. -/
def leafSpec : FnSpec where
  Arg := Word × Word
  args x := [x.1, x.2]
  stack := 0
  pre _ := emp
  post x v := ⌜v = x.1 + x.2⌝

/-- The caller of the addition leaf. -/
def callerSpec : FnSpec where
  Arg := Word × Word
  args x := [x.1, x.2]
  stack := 8
  pre _ := emp
  post x v := ⌜v = x.1 + x.2⌝

/-- The logical arguments of `MD5_memcpy`. -/
structure Md5Arg where
  out : Word
  inp : Word
  src : List Byte
  old : List Byte

/-- `MD5_memcpy(output, input, len)`. -/
def md5Spec : FnSpec where
  Arg := Md5Arg
  args x := [x.out, x.inp, BitVec.ofNat 64 x.src.length]
  stack := 32
  pre x := ⌜x.old.length = x.src.length ∧ 0 < x.src.length ∧ x.src.length < 2 ^ 32⌝ ∗
    (bytesPt x.out.toNat x.old ∗ bytesPtRO x.inp.toNat x.src)
  post x _ := bytesPt x.out.toNat x.src ∗ bytesPtRO x.inp.toNat x.src

end Silmaril.X86.Sep.Demo
