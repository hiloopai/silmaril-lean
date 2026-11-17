module

public import Silmaril.Machine.Abi.Conformance.Win64.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Win64

/-!
# The Microsoft x64 INTEGER fragment: theorems

* `win64Int_lower_examples`: what `win64Int` lowers and refuses. `long` is 4 bytes under the
  Microsoft data model, so the header `long f(long);` declares `f` with the prototype
  `int32 → int32` under `win64Int` and `int64 → int64` under `sysvInt`;
* `win64Int_lower_variadic`, `win64Int_lower_double`: the refusal messages;
* `win64Int_resultAt_int32`, `win64Int_resultAt_uint32`: a 32-bit result is the low half of RAX
  (proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Win64`).
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi

/-- `long f(long)`, as a header. -/
def longHdr : HeaderSrc := ⟨[("h.h", "long f(long);")], "h.h"⟩

/-- What `win64Int` lowers and refuses, against `sysvInt` on the same C prototypes. -/
theorem win64Int_lower_examples :
    (win64Int.lower ⟨.int .long .signed, [.int .long .signed], false⟩).toOption.map
        (·.signature) = some ⟨[.int32], some .int32⟩ ∧
    (sysvInt.lower ⟨.int .long .signed, [.int .long .signed], false⟩).toOption.map
        (·.signature) = some ⟨[.int64], some .int64⟩ ∧
    ((longHdr.proto? "f").bind fun cp => (win64Int.lower cp).toOption).map (·.signature) =
      some ⟨[.int32], some .int32⟩ ∧
    ((longHdr.proto? "f").bind fun cp => (sysvInt.lower cp).toOption).map (·.signature) =
      some ⟨[.int64], some .int64⟩ ∧
    (win64Int.lower ⟨.int .long .unsigned, [.ptr .void, .int .size .unsigned,
        .int .longLong .signed], false⟩).toOption.map (·.signature) =
      some ⟨[.pointer, .uint64, .int64], some .uint32⟩ ∧
    (win64Int.lower ⟨.float .double, [.float .double], false⟩).toOption.isNone = true ∧
    (win64Int.lower ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (win64Int.lower ⟨.int .int .signed, [.int .short .signed], false⟩).toOption.isNone = true ∧
    (win64Int.lower ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩).toOption.isNone =
      true ∧
    Coverage.check win64Int ⟨[("h.h", "long f(long); double g(double); int h(int, ...);")],
      "h.h"⟩ ⟨["f"], [("g", .unsupported "SSE"), ("h", .unsupported "varargs")]⟩ = true := by
  decide +kernel

theorem win64Int_lower_variadic :
    win64Int.lower ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩ =
      .error "variadic: Microsoft x64 varargs duplicate floating arguments in RCX/RDX/R8/R9; \
        outside the INTEGER fragment" := rfl

theorem win64Int_lower_double :
    win64Int.lower ⟨.float .double, [.float .double], false⟩ =
      .error "floating type: SSE/x87 classes are outside the INTEGER fragment" := rfl

/-- A 32-bit `win64Int` result (`int`, `long`) is the low half of RAX. -/
theorem win64Int_resultAt_int32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    win64Int.conv.ResultAt ⟨⟨args, some .int32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r :=
  Silmaril.Proofs.Machine.Abi.Conformance.Win64.resultAt_int32 args h s s' r

/-- A 32-bit unsigned `win64Int` result (`unsigned`, `unsigned long`) is the low half of RAX. -/
theorem win64Int_resultAt_uint32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    win64Int.conv.ResultAt ⟨⟨args, some .uint32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r :=
  Silmaril.Proofs.Machine.Abi.Conformance.Win64.resultAt_uint32 args h s s' r

end Silmaril.Machine.Abi.Conformance

end
