module
public import Silmaril.Compiler.C.Types.Defs
/-! Native operations on address-backed x87 values. These are explicit effectful
intrinsics carried beside Mir; they are not C calls or new generic Mir operators.
This vocabulary supplies operand shapes, not numerical or execution semantics. -/
@[expose] public section
namespace Silmaril.Compiler.Native.X87
open Silmaril.Cerberus
open Silmaril.Compile.C (CType)

inductive Format where
  | extended | float32 | float64 | integer (bytes : Nat) (signed : Bool) | boolean
  deriving DecidableEq, Repr

def Format.supported : Format → Bool
  | .integer bytes _ => [1, 2, 4, 8].contains bytes
  | _ => true

def Format.ofType : CType → Except String Format
  | .agg (.mk _ (.basic (.floating (.realFloating .longDouble)))) => .ok .extended
  | .float 4 => .ok .float32
  | .float 8 => .ok .float64
  | .int bytes signed =>
      if [1, 2, 4, 8].contains bytes then .ok (.integer bytes signed)
      else .error "native x87 conversion requires an ordinary integer of at most 64 bits"
  | .bool => .ok .boolean
  | _ => .error "native x87 operation does not support this scalar representation"

inductive Comparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive Arithmetic where
  | add | sub | mul | div
  deriving DecidableEq, Repr

inductive Operation where
  | convert (source target : Format)
  | compare (condition : Comparison)
  | arithmetic (operator : Arithmetic)
  | negate
  | truth
  deriving DecidableEq, Repr

/-- A memory result is an explicit first operand, pointing to sixteen writable
bytes; every extended input points to sixteen readable bytes. Scalar operands
and scalar results use the ordinary canonical Mir register representation. -/
def Operation.memoryResult : Operation → Bool
  | .convert _ .extended | .arithmetic _ | .negate => true
  | _ => false

def Operation.operands (operation : Operation) : Nat :=
  (if operation.memoryResult then 1 else 0) +
    (match operation with | .compare _ | .arithmetic _ => 2 | _ => 1)

def Operation.results (operation : Operation) : Nat :=
  if operation.memoryResult then 0 else 1

/-- Reject invalid widths and conversions unrelated to the extended carrier
before selecting any assembly. Ordinary scalar conversions keep their own path. -/
def Operation.supported : Operation → Bool
  | .convert source target =>
      source.supported && target.supported && (source == .extended || target == .extended)
  | _ => true

structure Intrinsic where
  key : String
  operation : Operation
  deriving Repr

end Silmaril.Compiler.Native.X87
