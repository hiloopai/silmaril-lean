module

public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
/-! # `Silmaril.C.Api.Scalar` as Cerberus `Ctype`

The System V INTEGER/pointer convention `Silmaril.Machine.Abi.SystemV.convention`
is keyed by `Silmaril.C.Api.Scalar`; the native compiler's ABI correspondence
(the native call-convention correspondence) and the ABI model's `objectOfCtype` are keyed by Cerberus `Ctype`. This
header gives the one translation between the two vocabularies:

* `Scalar.toCtype`: `int32 ↦ int`, `uint32 ↦ unsigned int`, `int64 ↦ long`,
  `uint64 ↦ unsigned long`, `pointer ↦ void *`, all unannotated and unqualified
  (LP64, as in `Kind.ctype`);
* `ctypePlan`: the `Ctype`-keyed planner, i.e. the ABI model's `plan` applied to the
  `objectOfCtype` classification of argument and result types;
* `Proto.ctypes`, `Proto.resultCtype`: the Cerberus prototype of a fragment
  prototype;
* `sigOf`: the typed the ABI model FFI signature that `convention` uses for a prototype.

The theorems (`Thms`) say that the classification agrees with `Kind.object`
for every tag environment and that the `Ctype` planner gives the convention's
descriptor. No declaration here is named `Convention`, and this file does not
open `Silmaril.Compile.Category`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CtypeBridge

open Silmaril.C.Api (Scalar)
open Silmaril.Cerberus (Ctype CtypeNode BasicType IntegerType IntegerBaseType Qualifiers)
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi (Object Profile CallPlan objectOfCtype)

/-- No `const`, `restrict` or `volatile`. -/
def unqualified : Qualifiers := ⟨false, false, false⟩

/-- An unannotated signed or unsigned integer type of the given base. -/
def integerCtype (signed : Bool) (base : IntegerBaseType) : Ctype :=
  .mk [] (.basic (.integer (if signed then .signed base else .unsigned base)))

/-- The Cerberus C type of a fragment scalar (LP64). -/
def Scalar.toCtype : Scalar → Ctype
  | .int32 => integerCtype true .int
  | .uint32 => integerCtype false .int
  | .int64 => integerCtype true .long
  | .uint64 => integerCtype false .long
  | .pointer => .mk [] (.pointer unqualified (.mk [] .void))

/-- the ABI model's planner keyed by Cerberus types: classify every argument and the
result with `objectOfCtype`, then plan a fixed-arity call. -/
def ctypePlan (profile : Profile) (tags : Tags) (arguments : List Ctype)
    (result : Option Ctype) : Except String CallPlan := do
  let objects ← arguments.mapM (objectOfCtype tags)
  let resultObject ← result.mapM (objectOfCtype tags)
  Silmaril.Machine.SystemV.Abi.plan profile objects resultObject arguments.length false

/-- The Cerberus argument types of a fragment prototype. -/
def Proto.ctypes (p : Abi.SystemV.Proto) : List Ctype :=
  p.signature.arguments.map Scalar.toCtype

/-- The Cerberus result type of a fragment prototype (`none` is `void`). -/
def Proto.resultCtype (p : Abi.SystemV.Proto) : Option Ctype :=
  p.signature.result.map Scalar.toCtype

/-- The typed the ABI model FFI signature used by `Abi.SystemV.convention` for `p`. -/
def sigOf (profile : Profile) (p : Abi.SystemV.Proto) :
    Silmaril.Machine.SystemV.Abi.Ffi.Signature :=
  p.ffi profile (Abi.SystemV.plan_intPlan profile)

end Silmaril.Machine.Abi.CtypeBridge
