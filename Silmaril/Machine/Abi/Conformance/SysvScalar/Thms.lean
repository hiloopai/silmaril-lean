module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs

/-!
# The System V scalar fragment: lowering and planning, on examples

* `sysvScalar_lower_examples`: what `sysvScalar` lowers and refuses. `double f(double, int)`
  lowers to `[double, int32] → double`, and the psABI planner (`Proto.plan`, the raw
  `SystemV.Abi.plan`) places the `double` in XMM0, the `int` in EDI and the result in XMM0;
  a ninth `float` goes to the stack while a `long` after it still gets RDI (the classes are
  counted separately); `long f(long)` is `int64 → int64` as under `sysvInt`;
* a coverage may not exclude `f` as unsupported under `sysvScalar` (it lowers), and must
  under `sysvInt`;
* `sysvScalar_lower_longDouble`, `sysvScalar_lower_float128`, `sysvScalar_lower_struct`,
  `sysvScalar_lower_variadic`: the refusal messages.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV.Scalar (Kind Proto scalarPlan)

/-- `double f(double, int)` and others, as a header. -/
def scalarHdr : HeaderSrc :=
  ⟨[("h.h", "double f(double, int); float g(float, float, float, float, float, float, float, \
    float, float, long); long double ld(long double); int printf(const char *, ...);")], "h.h"⟩

/-- What `sysvScalar` lowers, how the psABI planner places it, and what it refuses. -/
theorem sysvScalar_lower_examples :
    ((scalarHdr.proto? "f").bind fun cp => (sysvScalar.lower cp).toOption).map
        (fun p => (p.args, p.result)) = some ([.double, .int32], some .double) ∧
    ((scalarHdr.proto? "f").bind fun cp => (sysvScalar.lower cp).toOption).bind
        (fun p => (p.plan {}).toOption) =
      some ⟨[⟨Kind.double.object, [⟨0, 8, .vector 0 0⟩], none⟩,
          ⟨Kind.int32.object, [⟨0, 4, .gp .rdi⟩], none⟩],
        .direct [⟨0, 8, .vector 0 0⟩], 0, 16, 1, 1, none⟩ ∧
    ((scalarHdr.proto? "g").bind fun cp => (sysvScalar.lower cp).toOption).bind
        (fun p => (p.plan {}).toOption |>.map fun cp =>
          (cp.arguments.map (·.chunks), cp.arguments.map (·.stackOffset), cp.stackSize)) =
      some ((List.range 8).map (fun i => [⟨0, 4, .vector i 0⟩]) ++ [[], [⟨0, 8, .gp .rdi⟩]],
        List.replicate 8 none ++ [some 0, none], 16) ∧
    ((scalarHdr.proto? "g").bind fun cp => (sysvScalar.lower cp).toOption).map
        (fun p => p.stackBytes) = some 8 ∧
    (sysvScalar.lower ⟨.int .long .signed, [.int .long .signed], false⟩).toOption.map
        (fun p => (p.args, p.result)) = some ([.int64], some .int64) ∧
    (sysvScalar.lower ⟨.void, [.ptr .void, .float .float], false⟩).toOption.map
        (fun p => (p.args, p.result)) = some ([.pointer, .float], none) ∧
    ((scalarHdr.proto? "ld").bind fun cp => (sysvScalar.lower cp).toOption).isNone = true ∧
    ((scalarHdr.proto? "printf").bind fun cp => (sysvScalar.lower cp).toOption).isNone =
      true ∧
    (sysvScalar.lower ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (sysvScalar.lower ⟨.struct "s", [], false⟩).toOption.isNone = true ∧
    (sysvScalar.lower ⟨.float .float128, [], false⟩).toOption.isNone = true ∧
    Coverage.check sysvScalar scalarHdr ⟨["f", "g"], [("ld", .unsupported "x87"),
      ("printf", .unsupported "varargs")]⟩ = true ∧
    Coverage.check sysvScalar scalarHdr ⟨["g"], [("f", .unsupported "SSE"),
      ("ld", .unsupported "x87"), ("printf", .unsupported "varargs")]⟩ = false ∧
    Coverage.check sysvInt scalarHdr ⟨[], [("f", .unsupported "SSE"), ("g", .unsupported "SSE"),
      ("ld", .unsupported "x87"), ("printf", .unsupported "varargs")]⟩ = true := by
  decide +kernel

theorem sysvScalar_lower_longDouble :
    sysvScalar.lower ⟨.float .longDouble, [.float .longDouble], false⟩ =
      .error "long double: X87/X87UP class (passed in memory, returned in %st0); outside the \
        scalar fragment" := rfl

theorem sysvScalar_lower_float128 :
    sysvScalar.lower ⟨.void, [.float .float128], false⟩ =
      .error "__float128: SSE/SSEUP class; outside the scalar fragment" := rfl

theorem sysvScalar_lower_struct :
    sysvScalar.lower ⟨.float .double, [.struct "pt"], false⟩ =
      .error "struct pt by value: aggregates are outside the scalar fragment" := rfl

theorem sysvScalar_lower_variadic :
    sysvScalar.lower ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩ =
      .error "variadic: the %al vector-register count and va_list are outside the scalar \
        fragment" := rfl

end Silmaril.Machine.Abi.Conformance

end
