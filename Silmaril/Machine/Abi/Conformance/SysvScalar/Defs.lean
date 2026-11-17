module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Machine.Abi.SystemV.Scalar.Thms

/-!
# The System V scalar fragment as an ABI definition

**`sysvScalar`** extends `sysvInt` with the scalar floating types: `float` and `double` are
SSE class (psABI §3.2.3) and travel in XMM0–XMM7, mixed with INTEGER-class arguments in RDI…R9,
each class counted separately; arguments that find no register of their class take 8-byte
stack slots in argument order; the result is in RAX (INTEGER) or XMM0 (SSE). The convention is
`Machine.Abi.SystemV.Scalar.sysv`: the psABI planner (`plan`, whose closed form on this
fragment is `scalarPlan`) with the full `Ffi.Entry`/`Ffi.Return`/`Ffi.ResultAt` discipline.

The floating types' sizes come from the data model (`DataModel.floatShape`): a 4-byte type is
IEEE binary32, an 8-byte type binary64. `lowerScalar` refuses, with a reason:
* `long double` (X87 and X87UP classes: passed in memory, returned in `%st0`);
* `__float128` (SSE and SSEUP classes);
* `_Bool`, `char`, `short`, enums, structs and unions by value, arrays;
* varargs (the `%al` vector-register count and `va_list`).

**What a row does not cover.** The standard machines (`Open`, `Open9`) model no SSE
instruction, so code that reads an XMM argument or writes XMM0 is stuck on them and has no
`sysvScalar` row there. A row on such a machine is for code that receives floating arguments
and does not touch them (they are carried by `callModelOf`, unchanged); a row about floating
computation needs a machine with SSE steps.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance

open Silmaril.Data.Layout (CTy DataModel)
open Silmaril.Data.Layout.Header (CProto)
open Silmaril.Machine.Abi.SystemV.Scalar (Kind)

/-- The scalar of a C type under a data model, or why the scalar fragment has none. -/
def kindOf (dm : DataModel) : CTy → Except String Kind
  | .typedef _ t => kindOf dm t
  | .ptr _ => .ok .pointer
  | .int k s => match dm.intShape k with
    | some ⟨4, _⟩ => .ok (if dm.isSigned k s then .int32 else .uint32)
    | some ⟨8, _⟩ => .ok (if dm.isSigned k s then .int64 else .uint64)
    | some ⟨n, _⟩ => .error s!"{n}-byte integer: outside the scalar fragment (4- and 8-byte \
        integers, pointers, float and double)"
    | none => .error "integer kind without a size in the data model"
  | .float .longDouble => .error "long double: X87/X87UP class (passed in memory, returned in \
      %st0); outside the scalar fragment"
  | .float .float128 => .error "__float128: SSE/SSEUP class; outside the scalar fragment"
  | .float k => match dm.floatShape k with
    | some ⟨4, 4⟩ => .ok .float
    | some ⟨8, 8⟩ => .ok .double
    | some ⟨n, _⟩ => .error s!"{n}-byte floating type: outside the scalar fragment (binary32 \
        and binary64)"
    | none => .error "floating kind without a size in the data model"
  | .bool => .error "_Bool: outside the scalar fragment (4- and 8-byte integers, pointers, \
      float and double)"
  | .struct t => .error s!"struct {t} by value: aggregates are outside the scalar fragment"
  | .union t => .error s!"union {t} by value: aggregates are outside the scalar fragment"
  | .enum t _ => .error s!"enum {t}: enumerations are outside the scalar fragment"
  | .array .. => .error "array object type"
  | .void => .error "void object type"

/-- The scalar-fragment prototype of a C prototype. -/
def lowerScalar (dm : DataModel) (cp : CProto) :
    Except String Silmaril.Machine.Abi.SystemV.Scalar.Proto :=
  if cp.variadic then
    .error "variadic: the %al vector-register count and va_list are outside the scalar fragment"
  else
    match Silmaril.Data.Layout.traverse (kindOf dm) cp.params,
        (match cp.ret with
          | .void => (Except.ok none : Except String (Option Kind))
          | t => some <$> kindOf dm t) with
    | .error e, _ => .error e
    | _, .error e => .error s!"result: {e}"
    | .ok ps, .ok r =>
      if h : ps.length ≤ Silmaril.Machine.Abi.SystemV.maxArity then .ok ⟨ps, r, h⟩
      else .error "more than 127 parameters"

/-- **System V AMD64, scalar fragment**: fixed-arity prototypes of 4- and 8-byte integers,
pointers, `float` and `double`, planned by the psABI planner (`scalarPlan`), with the full
`Ffi.Entry`/`Ffi.Return` discipline. Arguments without a register of their class are 8-byte
stack slots above the return address; the callee owns that area. -/
def sysvScalar : AbiDef where
  id := "x86_64-sysv-psabi@e1ce0983/lp64/scalar"
  source := "System V Application Binary Interface, AMD64 Architecture Processor Supplement, \
    x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 (Function Calling \
    Sequence): register save and red zone (§3.2.1–3.2.2), parameter passing and \
    classification of INTEGER and SSE scalars, returning of values (§3.2.3)"
  dm := Silmaril.Data.Layout.sysvX86_64
  V := Silmaril.Machine.Abi.SystemV.Scalar.vocab
  D := Silmaril.Machine.Abi.SystemV.CallSite
  conv := Silmaril.Machine.Abi.SystemV.Scalar.sysv {}
  lower := lowerScalar Silmaril.Data.Layout.sysvX86_64
  argArea p := p.stackBytes
  owned _ _ _ := False

end Silmaril.Machine.Abi.Conformance

end
