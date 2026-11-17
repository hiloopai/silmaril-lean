module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Machine.Abi.Win64.Thms

/-!
# The Microsoft x64 INTEGER fragment as an ABI definition

**`win64Int`** is the integer fragment of the Microsoft x64 calling convention, judged with
the Microsoft x64 data model (`Data.Layout.msX64`, LLP64). It differs from `sysvInt` in the
data model and the convention, not in the C vocabulary:

* **the data model**: `long` and `unsigned long` are 4 bytes, so a header `long f(long)`
  lowers to `int32 → int32` here and to `int64 → int64` under `sysvInt`
  (`Thms.win64Int_lower_examples`);
* **the convention** (`Machine.Abi.Win64.win64`): the first four arguments in RCX, RDX, R8,
  R9; a 32-byte shadow area above the return address; argument `i ≥ 4` in the 8-byte slot at
  `rsp + 8 + 8 * i`; the result in RAX; RBX, RBP, RDI, RSI, R12–R15 and the low halves of
  XMM6–XMM15 callee-saved; no red zone.

The callee owns the shadow area and its stack arguments: `argArea` is `8 * max n 4` bytes
above the return address. Floating types, aggregates, `_Bool`, `char`, `short`, enums and
varargs are refused (`lowerWin64Int`).
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Data.Layout (DataModel)
open Silmaril.Data.Layout.Header (CProto)

/-- The Microsoft x64 INTEGER-fragment prototype of a C prototype: `lowerInt` under the data
model, with the Microsoft reason for refusing varargs. -/
def lowerWin64Int (dm : DataModel) (cp : CProto) :
    Except String Silmaril.Machine.Abi.SystemV.Proto :=
  if cp.variadic then
    .error "variadic: Microsoft x64 varargs duplicate floating arguments in RCX/RDX/R8/R9; \
      outside the INTEGER fragment"
  else lowerInt dm cp

/-- **Microsoft x64, INTEGER fragment**, under the LLP64 data model `msX64`: fixed-arity
prototypes of 4- and 8-byte integers and pointers (`long` is 4 bytes), with the
`Machine.Abi.Win64.win64` discipline (RCX, RDX, R8, R9, a 32-byte shadow area, then 8-byte
stack slots; result in RAX). The callee owns the shadow area and its stack arguments. -/
def win64Int : AbiDef where
  id := "x86_64-ms-x64@cpp-docs-e6106755/llp64/integer"
  source := "Microsoft, \"x64 calling convention\", \
    https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention \
    (MicrosoftDocs/cpp-docs@e61067551f92a1c7beaad20c04b9f5ccfd2b5dd6, \
    docs/build/x64-calling-convention.md): calling convention defaults, parameter passing, \
    return values, caller/callee saved registers; and \"Overview of x64 ABI conventions\", \
    https://learn.microsoft.com/en-us/cpp/build/x64-software-conventions \
    (MicrosoftDocs/cpp-docs@d25e83731f0600bc021bd0b084ad5812b6cfe88f, \
    docs/build/x64-software-conventions.md): scalar types, register volatility, stack usage"
  dm := Silmaril.Data.Layout.msX64
  V := Silmaril.Machine.Abi.SystemV.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.Win64.win64
  lower _ := lowerWin64Int Silmaril.Data.Layout.msX64
  argArea p := 8 * max p.signature.arguments.length 4
  owned _ _ _ := False

end Silmaril.Machine.Abi.Conformance

end
