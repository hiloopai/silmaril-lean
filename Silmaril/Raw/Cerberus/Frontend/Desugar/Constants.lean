module

public import Silmaril.Cerberus.Frontend.Desugar.Effect.Defs

/-! # Constants and operators

The translations of Cabs constants, string literals and operators to Ail
(`cabs_to_ail.lem:1078-1245`), with `Decode.decode_integer_constant`
(`ocaml_frontend/decode.ml:8-36`), which reads the value of an integer constant.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `read_digit` of `Decode.decode_integer_constant` (`decode.ml:9-16`). -/
def readDigit (c : Char) : Nat :=
  match c with
  | 'a' | 'A' => 10
  | 'b' | 'B' => 11
  | 'c' | 'C' => 12
  | 'd' | 'D' => 13
  | 'e' | 'E' => 14
  | 'f' | 'F' => 15
  | n => n.toNat - '0'.toNat

/-- `Decode.decode_integer_constant` (`decode.ml:8-36`): the basis and value of a
well-formed integer constant without suffix; a leading `0` alone is octal. -/
def decodeIntegerConstant (str : String) : Basis × Int :=
  let cs := str.toList
  let (digits, basisN, basis) : List Char × Nat × Basis :=
    match cs with
    | '0' :: 'x' :: ds | '0' :: 'X' :: ds => (ds, 16, .hexadecimal)
    | '0' :: 'b' :: ds | '0' :: 'B' :: ds => (ds, 2, .binary)
    | '0' :: ds => (ds, 8, .octal)
    | ds => (ds, 10, .decimal)
  (basis, (digits.foldl (fun acc c => acc * basisN + readDigit c) 0 : Nat))

/-- `translate_integer_suffix` (`cabs_to_ail.lem:1079`). -/
def translateIntegerSuffix : Cabs.IntegerSuffix → IntegerSuffix
  | .u => .u
  | .ul => .ul
  | .ull => .ull
  | .l => .l
  | .ll => .ll

/-- `translate_integer_constant` (`cabs_to_ail.lem:1088`). -/
def translateIntegerConstant : Cabs.IntegerConstant → IntegerConstant
  | (str, suffOpt) =>
    let (basis, n) := decodeIntegerConstant str
    .iconstant n basis (suffOpt.map translateIntegerSuffix)

/-- `translate_floating_suffix` (`cabs_to_ail.lem:1096`). -/
def translateFloatingSuffix : Cabs.FloatingSuffix → FloatingSuffix
  | .f => .f
  | .l => .l

/-- `translate_floating_constant` (`cabs_to_ail.lem:1102`). -/
def translateFloatingConstant : Cabs.FloatingConstant → FloatingConstant
  | (str, suffOpt) => (str, suffOpt.map translateFloatingSuffix)

/-- `translate_character_prefix` (`cabs_to_ail.lem:1107`). -/
def translateCharacterPrefix : Cabs.CharacterPrefix → CharacterPrefix
  | .wide => .wide
  | .utf16 => .utf16
  | .utf32 => .utf32

/-- `translate_character_constant` (`cabs_to_ail.lem:1115`). -/
def translateCharacterConstant : Cabs.CharacterConstant → CharacterConstant
  | (prefOpt, str) => (prefOpt.map translateCharacterPrefix, .utf8 str)

/-- `translate_unary_operator` (`cabs_to_ail.lem:1154`); `!` is desugared before, so it is a
Lem `error`. -/
def translateUnaryOperator : Cabs.UnaryOperator → DesugM UnaryOperator
  | .address => return .address
  | .indirection => return .indirection
  | .plus => return .plus
  | .minus => return .minus
  | .bnot => return .bnot
  | .not => internalError "[Cabs_to_ail.translate_unary_operator] Not"

/-- `translate_arithmetic_operator` (`cabs_to_ail.lem:1166`), on the operators allowed in a
compound assignment (STD §6.5.16#1); the others are a Lem `error`, never reached. -/
def translateArithmeticOperator : Cabs.BinaryOperator → Option ArithmeticOperator
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .band => some .band
  | .bxor => some .bxor
  | .bor => some .bor
  | .shl => some .shl
  | .shr => some .shr
  | _ => none

/-- `translate_binary_operator` (`cabs_to_ail.lem:1183`). -/
def translateBinaryOperator : Cabs.BinaryOperator → BinaryOperator
  | .and => .and
  | .or => .or
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .gt => .gt
  | .le => .le
  | .ge => .ge
  | op => .arithmetic ((translateArithmeticOperator op).getD .add)

/-- `translate_assignment_operator` (`cabs_to_ail.lem:1197`). -/
def translateAssignmentOperator : Cabs.AssignmentOperator → Option ArithmeticOperator
  | .assign => none
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .add => some .add
  | .sub => some .sub
  | .shl => some .shl
  | .shr => some .shr
  | .band => some .band
  | .bxor => some .bxor
  | .bor => some .bor

/-- `desugar_cabs_constant` (`cabs_to_ail.lem:1217`). -/
def desugarCabsConstant : Cabs.Constant → Constant
  | .integer iCst => .integer (translateIntegerConstant iCst)
  | .floating fCst => .floating (translateFloatingConstant fCst)
  | .character cCst => .character (translateCharacterConstant cCst)

/-- `translate_cabs_encoding_prefix` (`cabs_to_ail.lem:1228`). -/
def translateCabsEncodingPrefix : Cabs.EncodingPrefix → EncodingPrefix
  | .utf8 => .utf8
  | .utf16 => .utf16
  | .utf32 => .utf32
  | .wide => .wide

/-- `translate_cabs_string_literal` (`cabs_to_ail.lem:1241`). -/
def translateCabsStringLiteral : Cabs.StringLiteral → StringLiteral
  | (prefOpt, strs) => (prefOpt.map translateCabsEncodingPrefix, strs)

end Silmaril.Cerberus.Frontend.Desugar
