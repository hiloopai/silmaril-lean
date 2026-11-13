module
public import Silmaril.Compiler.C.Types.Defs
public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs

/-! Preserve native address-backed values that the frozen compiler's scalar
view erased. In particular x87 objects occupy sixteen bytes of storage and are
passed/returned through the ABI using their original C type. Arithmetic for
extended integer values remains a separate lowering obligation. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Types
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Compile.C (CType)

def addressFormat : CType → Nat
  | .agg (.mk _ (.basic (.floating (.realFloating .longDouble)))) => 1
  | .agg (.mk _ (.basic (.integer _))) => 2
  | _ => 0

def addressScalar (type : CType) : Bool := addressFormat type != 0

def integerType (whole : Ctype) (type : IntegerType) : CType :=
  match Silmaril.Machine.SystemV.Abi.integerObject ∅ type with
  | .error why => .unsupported why
  | .ok object =>
    if object.size > 8 then .agg whole
    else match type with
      | .bool => .bool
      | .unsigned _ | .size | .ptraddr | .wint => .int object.size false
      | _ => .int object.size true

def ofCtype (type : Ctype) : CType :=
  let .mk annotations _ := type
  if !Silmaril.Machine.SystemV.Abi.annotationsSupported annotations then
    .unsupported "native type attributes require retained layout metadata"
  else
  match type with
  | .mk _ (.basic (.integer integer)) => integerType type integer
  | .mk _ (.basic (.floating (.realFloating .longDouble))) => .agg type
  | .mk _ (.atomic _) => .unsupported "native atomic operations require target metadata"
  | _ => Silmaril.Compile.C.ofCtype type

/-- Native ordinary integer resolution must not fall back to the imported
consumer's alias layout. In particular Linux LP64 `wint_t` is unsigned int.
Extended integer arithmetic keeps a separate address-backed lowering obligation.
-/
def ordinaryIntegerLayout (type : IntegerType) : Except String (Nat × Bool) :=
  match integerType (.mk [] (.basic (.integer type))) type with
  | .int bytes signed => .ok (bytes, signed)
  | .bool => .ok (1, false)
  | .unsupported why => .error why
  | _ => .error "native promoted integer needs retained extended metadata"

/-- Literal spelling uses the imported standard candidate selection, but an
out-of-range value must not be silently truncated into its fallback width.
Bound constants retain their native implementation type and its guards. -/
def constantIntegerLayout (constant : IntegerConstant) : Except String (Nat × Bool) := do
  match constant with
  | .max type | .min type => ordinaryIntegerLayout type
  | .iconstant value _ _ =>
      let (bytes, signed) := Silmaril.Compile.C.constantType constant
      let limit : Int := 2 ^ (8 * bytes - (if signed then 1 else 0))
      let lower := if signed then -limit else 0
      unless lower ≤ value && value < limit do
        throw "native integer constant exceeds its resolved ordinary representation"
      return (bytes, signed)

/-- Bounds of native ordinary integer values. `_Bool` has only the values
zero and one despite occupying a whole byte of storage. -/
def integerBounds (type : IntegerType) : Except String (Int × Int) := do
  if type == .bool then return (0, 1)
  let (bytes, signed) ← ordinaryIntegerLayout type
  let limit : Int := 2 ^ (8 * bytes - (if signed then 1 else 0))
  return (if signed then -limit else 0, limit - 1)

/-- Native bound values use the same scalar layouts as native generic types.
Unknown enum/alias implementations and extended values cannot use the imported
consumer's signed-int fallback. Literal values must fit their resolved type. -/
def integerConstantValue (constant : IntegerConstant) : Except String Int := do
  match constant with
  | .max type => return (← integerBounds type).2
  | .min type => return (← integerBounds type).1
  | .iconstant value _ _ =>
      let _ ← constantIntegerLayout constant
      return value

/-- Promotions and usual conversions use native scalar layouts throughout.
Resolving aliases first prevents the old consumer's signedness/default-width
choices from reappearing inside a compound generic integer annotation. -/
def resolveInteger : GenIntegerType → Except String (Nat × Bool)
  | .concrete type => ordinaryIntegerLayout type
  | .sizeT | .ptraddrT => .ok (8, false)
  | .ptrdiffT => .ok (8, true)
  | .unknown constant => constantIntegerLayout constant
  | .promote type => Silmaril.Compile.C.promote <$> resolveInteger type
  | .usual first second => do
      return Silmaril.Compile.C.usual (← resolveInteger first) (← resolveInteger second)

def ordinaryInteger (type : GenIntegerType) : Bool :=
  match resolveInteger type with | .ok _ => true | .error _ => false

def ofGenType : GenType → CType
  | .basic (.integer (.concrete integer)) =>
      integerType (.mk [] (.basic (.integer integer))) integer
  | .basic (.integer integer) =>
      match resolveInteger integer with
      | .ok (bytes, signed) => .int bytes signed
      | .error why => .unsupported why
  | .basic (.floating (.realFloating .longDouble)) =>
      .agg (.mk [] (.basic (.floating (.realFloating .longDouble))))
  | .atomic _ => .unsupported "native atomic operations require target metadata"
  | type => Silmaril.Compile.C.ofGenType type

def typeOf (expression : TypedExpression) : CType :=
  match expression.annotation with
  | .lvalue _ type _ => ofCtype type
  | .rvalue type => ofGenType type

/-- Extended real values take precedence in the usual arithmetic conversions;
ordinary float/double conversions retain the imported scalar rule. -/
def floatCommon (first second : CType) : Option CType :=
  if addressFormat first == 1 then some first
  else if addressFormat second == 1 then some second
  else Silmaril.Compile.C.floatCommon first second

end Silmaril.Compiler.Native.Types
