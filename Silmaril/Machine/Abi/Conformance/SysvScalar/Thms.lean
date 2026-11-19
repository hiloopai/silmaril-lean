module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar

/-!
# The System V scalar fragment: lowering and planning, on examples

Every example reads a header **text**, lowers a prototype with the tag definitions of the same
header (`HeaderSrc.env`, as `Declares` does) and runs the raw psABI planner (`Proto.plan`, the
ABI model's `SystemV.Abi.plan`) on the result. All are `decide +kernel`.

* `sysvScalar_lower_examples`: scalars. `double f(double, int)` lowers to
  `[double, int32] → double`, and the planner places the `double` in XMM0, the `int` in EDI
  and the result in XMM0; a ninth `float` goes to the stack while a `long` after it still gets
  RDI (the classes are counted separately); `long f(long)` is `int64 → int64` as under
  `sysvInt`;
* `sysvScalar_aggregate_classes`: the eightbyte classes `sysvScalar` computes from the member
  layouts: `struct p2 { long a; long b; }` INTEGER, INTEGER; `struct d2 { double x, y; }` SSE,
  SSE; `struct m { long a; double b; }` INTEGER, SSE; a 24-byte struct MEMORY;
  `struct f3 { float a, b, c; }` (12 bytes) SSE, SSE, and the same for `float v[3]` and for
  `struct f3` nested; `union { double; long; }` INTEGER (the merge rule); `char` and `float` in
  one eightbyte INTEGER; bit-fields INTEGER; a typedef of `struct p2` as `struct p2`;
* `sysvScalar_nested_classes`: nested structs and arrays of structs at offsets that are not
  multiples of 8 bytes are flattened to their leaves at absolute offsets:
  `struct outer { float x; struct inner { int a; float b; float c; } in; }` INTEGER, SSE (GCC's
  classes; the flat equivalent's), in RDI and XMM0, not the INTEGER, INTEGER that classifying
  `in` as a whole object gives;
* `sysvScalar_aggregate_args`: where the planner puts them: `p2` in RDI, RSI; `d2` in XMM0,
  XMM1; `m` in RDI and XMM0; the 24-byte struct on the stack (offset 0, 32 bytes reserved);
  `f3` in XMM0 (`a`, `b`: 8 bytes) and XMM1 (`c`: 4 bytes); five `long`s then `p2` then a
  `long`: `p2` would need the 6th and 7th INTEGER registers, so it goes **whole** to the stack
  and the last `long` still gets R9;
* `sysvScalar_aggregate_results`: `struct p2` returned in RAX, RDX; `struct d2` in XMM0, XMM1;
  the 24-byte struct through the hidden pointer (`Return.indirect 24 8`), so the `long`
  argument moves to RSI;
* `sysvScalar_lower_*`: the refusal messages, pinned by `rfl` or `decide +kernel`;
* `sysvScalar_tag_mismatch`, `sysvScalar_declares_sse`: the lowering reads the struct in the
  header that declares the prototype. Two headers declaring `long f(struct s)` with different
  bodies of `s` lower `f` differently; `Declares` holds with one and not the other; a tag the
  header does not define (or defines as another kind) is refused as incomplete;
* coverage: aggregates are claimable under `sysvScalar` and refused under `sysvInt`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV.Scalar (Kind Proto Arg Agg Eights scalarPlan)

/-- `double f(double, int)` and others, as a header. -/
def scalarHdr : HeaderSrc :=
  ⟨[("h.h", "double f(double, int); float g(float, float, float, float, float, float, float, \
    float, float, long); long double ld(long double); int printf(const char *, ...);")], "h.h"⟩

/-- What `sysvScalar` lowers, how the psABI planner places it, and what it refuses. -/
theorem sysvScalar_lower_examples :
    ((scalarHdr.proto? "f").bind fun cp => (sysvScalar.lower scalarHdr.env cp).toOption).map
        (fun p => (p.args, p.result)) = some ([.scalar .double, .scalar .int32], some (.scalar .double)) ∧
    ((scalarHdr.proto? "f").bind fun cp => (sysvScalar.lower scalarHdr.env cp).toOption).bind
        (fun p => (p.plan {}).toOption) =
      some ⟨[⟨Kind.double.object, [⟨0, 8, .vector 0 0⟩], none⟩,
          ⟨Kind.int32.object, [⟨0, 4, .gp .rdi⟩], none⟩],
        .direct [⟨0, 8, .vector 0 0⟩], 0, 16, 1, 1, none⟩ ∧
    ((scalarHdr.proto? "g").bind fun cp => (sysvScalar.lower scalarHdr.env cp).toOption).bind
        (fun p => (p.plan {}).toOption |>.map fun cp =>
          (cp.arguments.map (·.chunks), cp.arguments.map (·.stackOffset), cp.stackSize)) =
      some ((List.range 8).map (fun i => [⟨0, 4, .vector i 0⟩]) ++ [[], [⟨0, 8, .gp .rdi⟩]],
        List.replicate 8 none ++ [some 0, none], 16) ∧
    ((scalarHdr.proto? "g").bind fun cp => (sysvScalar.lower scalarHdr.env cp).toOption).map
        (fun p => p.stackBytes) = some 8 ∧
    (sysvScalar.lower [] ⟨.int .long .signed, [.int .long .signed], false⟩).toOption.map
        (fun p => (p.args, p.result)) = some ([.scalar .int64], some (.scalar .int64)) ∧
    (sysvScalar.lower [] ⟨.void, [.ptr .void, .float .float], false⟩).toOption.map
        (fun p => (p.args, p.result)) = some ([.scalar .pointer, .scalar .float], none) ∧
    ((scalarHdr.proto? "ld").bind fun cp => (sysvScalar.lower scalarHdr.env cp).toOption).isNone =
      true ∧
    ((scalarHdr.proto? "printf").bind fun cp =>
      (sysvScalar.lower scalarHdr.env cp).toOption).isNone = true ∧
    (sysvScalar.lower [] ⟨.int .int .signed, [.struct "s"], false⟩).toOption.isNone = true ∧
    (sysvScalar.lower [] ⟨.struct "s", [], false⟩).toOption.isNone = true ∧
    (sysvScalar.lower [] ⟨.float .float128, [], false⟩).toOption.isNone = true ∧
    Coverage.check sysvScalar scalarHdr ⟨["f", "g"], [("ld", .unsupported "x87"),
      ("printf", .unsupported "varargs")]⟩ = true ∧
    Coverage.check sysvScalar scalarHdr ⟨["g"], [("f", .unsupported "SSE"),
      ("ld", .unsupported "x87"), ("printf", .unsupported "varargs")]⟩ = false ∧
    Coverage.check sysvInt scalarHdr ⟨[], [("f", .unsupported "SSE"), ("g", .unsupported "SSE"),
      ("ld", .unsupported "x87"), ("printf", .unsupported "varargs")]⟩ = true := by
  decide +kernel

/-! ## Aggregates by value -/

/-- Structs and unions by value, as a header. -/
def aggHdr : HeaderSrc :=
  ⟨[("agg.h", "struct p2 { long a; long b; };
struct d2 { double x; double y; };
struct m { long a; double b; };
struct big { long a; long b; long c; };
struct f3 { float a, b, c; };
struct nest { struct f3 s; };
struct arr { float v[3]; };
union u { double d; long l; };
struct cf { char c; float f; };
struct bf { unsigned a : 3; unsigned b : 5; };
struct ld { long double x; };
struct ub { int a; int : 3; };
struct al { _Alignas(16) long a; long b; };
typedef struct p2 p2_t;
long sum_p2(struct p2 v);
double sum_d2(struct d2 v);
double mix(struct m v);
long sum_big(struct big v);
float sum_f3(struct f3 v);
float nest_f(struct nest v);
float arr_f(struct arr v);
long sum_u(union u v);
float cf_f(struct cf v);
unsigned bf_f(struct bf v);
long td_f(p2_t v);
long exhaust(long a, long b, long c, long d, long e, struct p2 v, long f);
struct p2 mk_p2(long a, long b);
struct d2 mk_d2(double a);
struct big mk_big(long a);
long double ld_f(struct ld v);
int ub_f(struct ub v);
long al_f(struct al v);
")], "agg.h"⟩

/-- The raw planner's call plan for `f` (`sysvScalar`, SSE profile), if it lowers and plans. -/
def aggPlan (f : String) : Option CallPlan :=
  (aggHdr.lowered sysvScalar f).bind fun p => (p.plan {}).toOption

/-- The classified objects `sysvScalar` computes from the member layouts. -/
theorem sysvScalar_aggregate_classes :
    (aggHdr.lowered sysvScalar "sum_p2").map (·.args.map Arg.object) =
      some [⟨16, 8, [.integer, .integer]⟩] ∧
    (aggHdr.lowered sysvScalar "sum_d2").map (·.args.map Arg.object) =
      some [⟨16, 8, [.sse, .sse]⟩] ∧
    (aggHdr.lowered sysvScalar "mix").map (·.args.map Arg.object) =
      some [⟨16, 8, [.integer, .sse]⟩] ∧
    (aggHdr.lowered sysvScalar "sum_big").map (·.args.map Arg.object) =
      some [⟨24, 8, [.memory]⟩] ∧
    (aggHdr.lowered sysvScalar "sum_f3").map (·.args.map Arg.object) =
      some [⟨12, 4, [.sse, .sse]⟩] ∧
    (aggHdr.lowered sysvScalar "nest_f").map (·.args.map Arg.object) =
      some [⟨12, 4, [.sse, .sse]⟩] ∧
    (aggHdr.lowered sysvScalar "arr_f").map (·.args.map Arg.object) =
      some [⟨12, 4, [.sse, .sse]⟩] ∧
    (aggHdr.lowered sysvScalar "sum_u").map (·.args.map Arg.object) =
      some [⟨8, 8, [.integer]⟩] ∧
    (aggHdr.lowered sysvScalar "cf_f").map (·.args.map Arg.object) =
      some [⟨8, 4, [.integer]⟩] ∧
    (aggHdr.lowered sysvScalar "bf_f").map (·.args.map Arg.object) =
      some [⟨4, 4, [.integer]⟩] ∧
    (aggHdr.lowered sysvScalar "td_f").map (·.args) =
      (aggHdr.lowered sysvScalar "sum_p2").map (·.args) := by
  decide +kernel

/-- Nested aggregates at offsets that are not multiples of 8 bytes (GCC 13 `-O2` regressions).
Each struct is 16 bytes; GCC passes it in RDI and XMM0 (INTEGER, SSE), as compiling a function
reading the member at offset 8 shows (`movq %xmm0, …`/a bare `ret` when it is already in
XMM0). -/
def nestHdr : HeaderSrc :=
  ⟨[("nest.h", "struct inner { int a; float b; float c; };
struct outer { float x; struct inner in; };
struct inner2 { int a; float b; };
struct outerA { float x; struct inner2 in[1]; float y; };
struct flat { float x; int a; float b; float c; };
struct pq { float p; float q; };
struct al { int a; struct pq in; float z; };
long f_outer(struct outer o);
long f_outerA(struct outerA o);
long f_flat(struct flat o);
long f_al(struct al o);
struct outer r_outer(void);")], "nest.h"⟩

/-- **Nested aggregates are classified from their leaves at absolute offsets** (`leavesOf`):
`struct outer { float x; struct inner { int a; float b; float c; } in; }` is INTEGER, SSE (the
first eightbyte holds `x` and `in.a`, the second `in.b` and `in.c`), as GCC passes it and as
the flat `struct flat { float x; int a; float b; float c; }` is; likewise an array of one
`struct { int a; float b; }` at offset 4 followed by a `float`, and `struct pq` at offset 4.
The planner then passes each in RDI and XMM0, and returns `struct outer` in RAX and XMM0.

The last conjunct is what classifying `in` as a whole object relative to its own start
(INTEGER, SSE over its 12 bytes) and merging that into the outer eightbytes computes:
INTEGER, INTEGER, which is wrong. -/
theorem sysvScalar_nested_classes :
    (nestHdr.lowered sysvScalar "f_outer").map (·.args.map Arg.object) =
      some [⟨16, 4, [.integer, .sse]⟩] ∧
    (nestHdr.lowered sysvScalar "f_outerA").map (·.args.map Arg.object) =
      some [⟨16, 4, [.integer, .sse]⟩] ∧
    (nestHdr.lowered sysvScalar "f_flat").map (·.args.map Arg.object) =
      some [⟨16, 4, [.integer, .sse]⟩] ∧
    (nestHdr.lowered sysvScalar "f_al").map (·.args.map Arg.object) =
      some [⟨16, 4, [.integer, .sse]⟩] ∧
    ((nestHdr.lowered sysvScalar "f_outer").bind fun p => (p.plan {}).toOption).map
        (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .gp .rdi⟩, ⟨8, 8, .vector 0 0⟩]] ∧
    ((nestHdr.lowered sysvScalar "f_outerA").bind fun p => (p.plan {}).toOption).map
        (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .gp .rdi⟩, ⟨8, 8, .vector 0 0⟩]] ∧
    ((nestHdr.lowered sysvScalar "r_outer").bind fun p => (p.plan {}).toOption).map
        (·.result) =
      some (.direct [⟨0, 8, .gp .rax⟩, ⟨8, 8, .vector 0 0⟩]) ∧
    aggregate 16 4 [⟨0, .floating .binary32, none⟩, ⟨32, ⟨12, 4, [.integer, .sse]⟩, none⟩] =
      ⟨16, 4, [.integer, .integer]⟩ := by
  decide +kernel

/-- Where the raw planner passes them. -/
theorem sysvScalar_aggregate_args :
    (aggPlan "sum_p2").map (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .gp .rdi⟩, ⟨8, 8, .gp .rsi⟩]] ∧
    (aggPlan "sum_d2").map (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩]] ∧
    (aggPlan "mix").map (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .gp .rdi⟩, ⟨8, 8, .vector 0 0⟩]] ∧
    (aggPlan "sum_big").map (fun cp =>
        (cp.arguments.map (·.chunks), cp.arguments.map (·.stackOffset), cp.stackSize)) =
      some ([[]], [some 0], 32) ∧
    (aggPlan "sum_f3").map (·.arguments.map (·.chunks)) =
      some [[⟨0, 8, .vector 0 0⟩, ⟨8, 4, .vector 1 0⟩]] ∧
    (aggPlan "exhaust").map (fun cp =>
        (cp.arguments.map (·.chunks), cp.arguments.map (·.stackOffset), cp.stackSize)) =
      some ([[⟨0, 8, .gp .rdi⟩], [⟨0, 8, .gp .rsi⟩], [⟨0, 8, .gp .rdx⟩], [⟨0, 8, .gp .rcx⟩],
          [⟨0, 8, .gp .r8⟩], [], [⟨0, 8, .gp .r9⟩]],
        [none, none, none, none, none, some 0, none], 16) := by
  decide +kernel

/-- How the raw planner returns them: a MEMORY result through the hidden pointer in RDI. -/
theorem sysvScalar_aggregate_results :
    (aggPlan "mk_p2").map (·.result) =
      some (.direct [⟨0, 8, .gp .rax⟩, ⟨8, 8, .gp .rdx⟩]) ∧
    (aggPlan "mk_d2").map (·.result) =
      some (.direct [⟨0, 8, .vector 0 0⟩, ⟨8, 8, .vector 1 0⟩]) ∧
    (aggPlan "mk_big").map (fun cp => (cp.result, cp.arguments.map (·.chunks), cp.gpUsed)) =
      some (.indirect 24 8, [[⟨0, 8, .gp .rsi⟩]], 2) ∧
    (aggHdr.lowered sysvScalar "mk_big").map (·.indirect) = some true ∧
    (aggHdr.lowered sysvScalar "mk_p2").map (·.indirect) = some false := by
  decide +kernel

/-! ## Refusals -/

theorem sysvScalar_lower_longDouble :
    sysvScalar.lower [] ⟨.float .longDouble, [.float .longDouble], false⟩ =
      .error "long double: X87/X87UP class (passed in memory, returned in %st0); outside the \
        scalar fragment" := rfl

theorem sysvScalar_lower_float128 :
    sysvScalar.lower [] ⟨.void, [.float .float128], false⟩ =
      .error "__float128: SSE/SSEUP class; outside the scalar fragment" := rfl

/-- A struct the environment does not define is incomplete. -/
theorem sysvScalar_lower_struct :
    sysvScalar.lower [] ⟨.float .double, [.struct "pt"], false⟩ =
      .error "struct pt by value: struct pt: no definition (incomplete type)" := rfl

theorem sysvScalar_lower_variadic :
    sysvScalar.lower [] ⟨.int .int .signed, [.ptr (.int .char .plain)], true⟩ =
      .error "variadic: the %al vector-register count and va_list are outside the scalar \
        fragment" := rfl

/-- A member of type `long double`, an unnamed bit-field, an eightbyte of padding only, and an
alignment above 8, read from the header text. -/
theorem sysvScalar_lower_members :
    ((aggHdr.proto? "ld_f").map fun cp => sysvScalar.lower aggHdr.env cp |>.toOption.isNone) =
      some true ∧
    ((aggHdr.proto? "ld_f").bind fun cp => match sysvScalar.lower aggHdr.env cp with
      | .error e => some e | .ok _ => none) =
      some "struct ld by value: long double member: X87/X87UP class; outside the scalar \
        fragment" ∧
    ((aggHdr.proto? "ub_f").bind fun cp => match sysvScalar.lower aggHdr.env cp with
      | .error e => some e | .ok _ => none) =
      some "struct ub by value: unnamed bit-field of nonzero width: outside the scalar fragment" ∧
    ((aggHdr.proto? "al_f").bind fun cp => match sysvScalar.lower aggHdr.env cp with
      | .error e => some e | .ok _ => none) =
      some "struct al by value: aligned to more than 8 bytes or larger than 2^32 bytes; outside \
        the scalar fragment" ∧
    (match sysvScalar.lower aggHdr.env ⟨.float .longDouble, [], false⟩ with
      | .error e => some e | .ok _ => none) =
      some "result: long double: X87/X87UP class (passed in memory, returned in %st0); outside \
        the scalar fragment" := by
  decide +kernel

/-- `__int128` and flexible (or zero-length) array members, which the header reader does not
read, refused by the lowering on a hand-written environment. -/
theorem sysvScalar_lower_int128 :
    sysvScalar.lower [⟨.struct, "w", [⟨"v", .int .int128 .signed, none, none⟩]⟩]
        ⟨.void, [.struct "w"], false⟩ =
      .error "struct w by value: __int128 member: a 16-byte-aligned INTEGER pair; outside the \
        scalar fragment" := rfl

theorem sysvScalar_lower_flexible :
    sysvScalar.lower [⟨.struct, "fl", [⟨"n", .int .long .signed, none, none⟩,
        ⟨"d", .array (.int .long .signed) 0, none, none⟩]⟩] ⟨.void, [.struct "fl"], false⟩ =
      .error "struct fl by value: zero-length or flexible array member" := rfl

/-! ## The struct is the one the header defines -/

theorem sysvScalar_declares_sse : Declares sysvScalar tagHdrB "f" sseProto :=
  Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.declares_sse

/-- The same C prototype in a header where `s` is two `long`s is not that prototype: the
lowering reads the struct of the header that declares `f`. A tag the header does not define,
or defines as a struct and is used as a union, is refused as incomplete. -/
theorem sysvScalar_tag_mismatch :
    ¬ Declares sysvScalar tagHdrA "f" sseProto ∧
    (tagHdrA.lowered sysvScalar "f").map (·.args.map Arg.eights) = some [.two false false] ∧
    (match sysvScalar.lower tagHdrA.env ⟨.int .long .signed, [.struct "t"], false⟩ with
      | .error e => some e | .ok _ => none) =
      some "struct t by value: struct t: no definition (incomplete type)" ∧
    (match sysvScalar.lower tagHdrA.env ⟨.int .long .signed, [.union "s"], false⟩ with
      | .error e => some e | .ok _ => none) =
      some "union s by value: union s: no definition (incomplete type)" :=
  ⟨Silmaril.Proofs.Machine.Abi.Conformance.SysvScalar.not_declares_mismatch, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Aggregates are claimable under `sysvScalar` (those it classifies) and refused under
`sysvInt`. -/
theorem sysvScalar_aggregate_coverage :
    Coverage.check sysvScalar aggHdr ⟨["sum_p2", "sum_d2", "mix", "sum_big", "sum_f3", "nest_f",
      "arr_f", "sum_u", "cf_f", "bf_f", "td_f", "exhaust", "mk_p2", "mk_d2", "mk_big"],
      [("ld_f", .unsupported "x87"), ("ub_f", .unsupported "unnamed bit-field"),
       ("al_f", .unsupported "over-aligned")]⟩ = true ∧
    Coverage.check sysvInt aggHdr ⟨[], ["sum_p2", "sum_d2", "mix", "sum_big", "sum_f3", "nest_f",
      "arr_f", "sum_u", "cf_f", "bf_f", "td_f", "exhaust", "mk_p2", "mk_d2", "mk_big", "ld_f",
      "ub_f", "al_f"].map (·, .unsupported "aggregate")⟩ = true := by
  decide +kernel

end Silmaril.Machine.Abi.Conformance

end
