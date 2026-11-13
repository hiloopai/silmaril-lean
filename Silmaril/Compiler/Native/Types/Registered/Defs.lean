module

public import Silmaril.Compiler.Native.Types.Defs
/-! Native scalar conversion with an explicit implementation registry. An enum
uses its registered integer width and signedness; absent or recursive entries
remain errors. The original empty-registry APIs remain available unchanged. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Types.Registered
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Compile.C (CType)

/-- The independent native classifier admits one registered ordinary integer
implementation. A registration pointing to another enum is rejected explicitly,
so no implicit chain traversal or guessed implementation is introduced. -/
def implementation (tags : Tags) : IntegerType → Except String IntegerType
  | .enum tag => do
      let some underlying := tags.enums.lookup tag
        | throw "native enum ABI needs an explicit underlying type registration"
      match underlying with
      | .enum _ => throw "recursive enum implementation type"
      | integer => return integer
  | integer => .ok integer

/-- Ordinary enum values use the same scalar representation as their resolved
integer implementation. Only genuinely extended integers keep address storage. -/
def integerType (tags : Tags) (whole : Ctype) (integer : IntegerType) : CType :=
  match implementation tags integer with
  | .error why => .unsupported why
  | .ok resolved => Silmaril.Compiler.Native.Types.integerType whole resolved

def ofCtype (tags : Tags) (type : Ctype) : CType :=
  let .mk annotations node := type
  if !Silmaril.Machine.SystemV.Abi.annotationsSupported annotations then
    Silmaril.Compiler.Native.Types.ofCtype type
  else match node with
    | .basic (.integer integer) => integerType tags type integer
    | _ => Silmaril.Compiler.Native.Types.ofCtype type

def ordinaryIntegerLayout (tags : Tags) (integer : IntegerType) : Except String (Nat × Bool) :=
  match integerType tags (.mk [] (.basic (.integer integer))) integer with
  | .int bytes signed => .ok (bytes, signed)
  | .bool => .ok (1, false)
  | .unsupported why => .error why
  | _ => .error "native promoted integer needs retained extended metadata"

def constantIntegerLayout (tags : Tags) (constant : IntegerConstant) : Except String (Nat × Bool) :=
  match constant with
  | .max integer | .min integer => ordinaryIntegerLayout tags integer
  | .iconstant .. => Silmaril.Compiler.Native.Types.constantIntegerLayout constant

def integerBounds (tags : Tags) (integer : IntegerType) : Except String (Int × Int) := do
  Silmaril.Compiler.Native.Types.integerBounds (← implementation tags integer)

def integerConstantValue (tags : Tags) (constant : IntegerConstant) : Except String Int := do
  match constant with
  | .max integer => return (← integerBounds tags integer).2
  | .min integer => return (← integerBounds tags integer).1
  | .iconstant .. => Silmaril.Compiler.Native.Types.integerConstantValue constant

/-- General integer annotations resolve the same registry before promotions and
usual conversions. Recursion follows the actual finite annotation tree. -/
def resolveInteger (tags : Tags) : GenIntegerType → Except String (Nat × Bool)
  | .concrete integer => ordinaryIntegerLayout tags integer
  | .sizeT | .ptraddrT => .ok (8, false)
  | .ptrdiffT => .ok (8, true)
  | .unknown constant => constantIntegerLayout tags constant
  | .promote integer => Silmaril.Compile.C.promote <$> resolveInteger tags integer
  | .usual first second => do
      return Silmaril.Compile.C.usual (← resolveInteger tags first) (← resolveInteger tags second)

def ofGenType (tags : Tags) : GenType → CType
  | .basic (.integer (.concrete integer)) =>
      integerType tags (.mk [] (.basic (.integer integer))) integer
  | .basic (.integer integer) =>
      match resolveInteger tags integer with
      | .ok (bytes, signed) => .int bytes signed
      | .error why => .unsupported why
  | type => Silmaril.Compiler.Native.Types.ofGenType type

def typeOf (tags : Tags) (expression : TypedExpression) : CType :=
  match expression.annotation with
  | .lvalue _ type _ => ofCtype tags type
  | .rvalue type => ofGenType tags type

end Silmaril.Compiler.Native.Types.Registered
