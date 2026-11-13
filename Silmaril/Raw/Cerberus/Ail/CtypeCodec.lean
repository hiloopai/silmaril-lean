module

public import Silmaril.Cerberus.Mem.Defs
public import Silmaril.Cerberus.Cabs.Codec.Defs

/-! # Linear wire codec for symbols, C types and annotations

The types that the Ail documents delegate to the Core exporter's `wire.ml`
(`Symbol.sym`, `IntegerType.*`, `Ctype.*`, `Annot.*`) print exactly as in Core documents;
`Silmaril.Cerberus.Codec.{Symbol,Ctype}` encode them through `TaggedCodec`, whose trees cost
`O(n²)` for a node of `n` children. This module emits and decodes the same bytes in linear
time, on the `Sx` trees and the `Out` buffer of `Silmaril.Cerberus.Cabs.Wire`. Tags are the Lem
names of `Silmaril.Cerberus.Names`.

A digest prints as `($str "<lowercase hex>")`: the MD5 of the input file, or `""` for the
symbols of `std.core`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail.Codec

open Silmaril.Cerberus Cabs.Wire
open Silmaril.Cerberus.Cabs.Codec (emitLoc decodeLoc emitIdentifier decodeIdentifier
  emitAttributes decodeAttributes hex unhex)

/-! ## Symbols -/

def emitDigest (d : Digest) (o : Out) : Out := emitStr (hex ⟨d.bytes.toArray⟩) o

def decodeDigest (t : Sx) : Except String Digest := do
  let s ← decodeStr t
  match unhex s with
  | some b => return ⟨b.toList⟩
  | none => throw s!"invalid digest {s.take 40}"

def emitSymbolDescription (x : SymbolDescription) (o : Out) : Out :=
  match x with
  | .none => o ++ "(SD_None)"
  | .unnamedTag l => o |> open_ "SD_unnamed_tag" |> arg (emitLoc l) |> close
  | .id s => o |> open_ "SD_Id" |> arg (emitStr s) |> close
  | .cnId s => o |> open_ "SD_CN_Id" |> arg (emitStr s) |> close
  | .objectAddress s => o |> open_ "SD_ObjectAddress" |> arg (emitStr s) |> close
  | .return_ => o ++ "(SD_Return)"
  | .funArgValue s => o |> open_ "SD_FunArgValue" |> arg (emitStr s) |> close
  | .funArg l n => o |> open_ "SD_FunArg" |> arg (emitLoc l) |> arg (emitNat n) |> close

def decodeSymbolDescription : Sx → Except String SymbolDescription
  | .node "SD_None" #[] => return .none
  | .node "SD_unnamed_tag" #[l] => return .unnamedTag (← decodeLoc l)
  | .node "SD_Id" #[s] => return .id (← decodeStr s)
  | .node "SD_CN_Id" #[s] => return .cnId (← decodeStr s)
  | .node "SD_ObjectAddress" #[s] => return .objectAddress (← decodeStr s)
  | .node "SD_Return" #[] => return .return_
  | .node "SD_FunArgValue" #[s] => return .funArgValue (← decodeStr s)
  | .node "SD_FunArg" #[l, n] => return .funArg (← decodeLoc l) (← decodeNat n)
  | t => mismatch "Symbol.symbol_description" t

def emitSym (x : Sym) (o : Out) : Out :=
  o |> open_ "Symbol" |> arg (emitDigest x.digest) |> arg (emitNat x.number)
    |> arg (emitSymbolDescription x.description) |> close

def decodeSym : Sx → Except String Sym
  | .node "Symbol" #[d, n, s] =>
    return ⟨← decodeDigest d, ← decodeNat n, ← decodeSymbolDescription s⟩
  | t => mismatch "Symbol.sym" t

/-! ## Integer types -/

def emitIntegerBaseType (x : IntegerBaseType) (o : Out) : Out :=
  match x with
  | .ichar => o ++ "(Ichar)"
  | .short => o ++ "(Short)"
  | .int => o ++ "(Int_)"
  | .long => o ++ "(Long)"
  | .longLong => o ++ "(LongLong)"
  | .intN n => o |> open_ "IntN_t" |> arg (emitNat n) |> close
  | .intLeastN n => o |> open_ "Int_leastN_t" |> arg (emitNat n) |> close
  | .intFastN n => o |> open_ "Int_fastN_t" |> arg (emitNat n) |> close
  | .intmax => o ++ "(Intmax_t)"
  | .intptr => o ++ "(Intptr_t)"

def decodeIntegerBaseType : Sx → Except String IntegerBaseType
  | .node "Ichar" #[] => return .ichar
  | .node "Short" #[] => return .short
  | .node "Int_" #[] => return .int
  | .node "Long" #[] => return .long
  | .node "LongLong" #[] => return .longLong
  | .node "IntN_t" #[n] => return .intN (← decodeNat n)
  | .node "Int_leastN_t" #[n] => return .intLeastN (← decodeNat n)
  | .node "Int_fastN_t" #[n] => return .intFastN (← decodeNat n)
  | .node "Intmax_t" #[] => return .intmax
  | .node "Intptr_t" #[] => return .intptr
  | t => mismatch "IntegerType.integerBaseType" t

def emitIntegerType (x : IntegerType) (o : Out) : Out :=
  match x with
  | .char => o ++ "(Char)"
  | .bool => o ++ "(Bool)"
  | .signed b => o |> open_ "Signed" |> arg (emitIntegerBaseType b) |> close
  | .unsigned b => o |> open_ "Unsigned" |> arg (emitIntegerBaseType b) |> close
  | .enum s => o |> open_ "Enum" |> arg (emitSym s) |> close
  | .wchar => o ++ "(Wchar_t)"
  | .wint => o ++ "(Wint_t)"
  | .size => o ++ "(Size_t)"
  | .ptrdiff => o ++ "(Ptrdiff_t)"
  | .ptraddr => o ++ "(Ptraddr_t)"

def decodeIntegerType : Sx → Except String IntegerType
  | .node "Char" #[] => return .char
  | .node "Bool" #[] => return .bool
  | .node "Signed" #[b] => return .signed (← decodeIntegerBaseType b)
  | .node "Unsigned" #[b] => return .unsigned (← decodeIntegerBaseType b)
  | .node "Enum" #[s] => return .enum (← decodeSym s)
  | .node "Wchar_t" #[] => return .wchar
  | .node "Wint_t" #[] => return .wint
  | .node "Size_t" #[] => return .size
  | .node "Ptrdiff_t" #[] => return .ptrdiff
  | .node "Ptraddr_t" #[] => return .ptraddr
  | t => mismatch "IntegerType.integerType" t

/-! ## Annotations -/

def emitLabelAnnot (x : LabelAnnot) (o : Out) : Out :=
  match x with
  | .loop n => o |> open_ "LAloop" |> arg (emitNat n) |> close
  | .loopContinue n => o |> open_ "LAloop_continue" |> arg (emitNat n) |> close
  | .loopBreak n => o |> open_ "LAloop_break" |> arg (emitNat n) |> close
  | .return_ => o ++ "(LAreturn)"
  | .switch => o ++ "(LAswitch)"
  | .case_ => o ++ "(LAcase)"
  | .default => o ++ "(LAdefault)"
  | .actualLabel => o ++ "(LAactual_label)"

def decodeLabelAnnot : Sx → Except String LabelAnnot
  | .node "LAloop" #[n] => return .loop (← decodeNat n)
  | .node "LAloop_continue" #[n] => return .loopContinue (← decodeNat n)
  | .node "LAloop_break" #[n] => return .loopBreak (← decodeNat n)
  | .node "LAreturn" #[] => return .return_
  | .node "LAswitch" #[] => return .switch
  | .node "LAcase" #[] => return .case_
  | .node "LAdefault" #[] => return .default
  | .node "LAactual_label" #[] => return .actualLabel
  | t => mismatch "Annot.label_annot" t

def emitAnnot (x : Annot) (o : Out) : Out :=
  match x with
  | .std s => o |> open_ "Astd" |> arg (emitStr s) |> close
  | .loc l => o |> open_ "Aloc" |> arg (emitLoc l) |> close
  | .uid s => o |> open_ "Auid" |> arg (emitStr s) |> close
  | .marker n => o |> open_ "Amarker" |> arg (emitNat n) |> close
  | .markerObjectTypes n => o |> open_ "Amarker_object_types" |> arg (emitNat n) |> close
  | .bmc (.id n) => o |> open_ "Abmc" |> arg (fun o => o |> open_ "Abmc_id" |> arg (emitNat n)
      |> close) |> close
  | .attrs a => o |> open_ "Aattrs" |> arg (emitAttributes a) |> close
  | .typedef s => o |> open_ "Atypedef" |> arg (emitSym s) |> close
  | .label a => o |> open_ "Alabel" |> arg (emitLabelAnnot a) |> close
  | .cerb (.withAddress n) => o |> open_ "Acerb"
      |> arg (fun o => o |> open_ "ACerb_with_address" |> arg (emitInt n) |> close) |> close
  | .cerb .hidden => o |> open_ "Acerb" |> arg (· ++ "(ACerb_hidden)") |> close
  | .value (.integer t) => o |> open_ "Avalue"
      |> arg (fun o => o |> open_ "Ainteger" |> arg (emitIntegerType t) |> close) |> close
  | .inlinedLabel (l, s, a) => o |> open_ "Ainlined_label"
      |> arg (fun o => o |> open_ "$tuple" |> arg (emitLoc l) |> arg (emitSym s)
        |> arg (emitLabelAnnot a) |> close) |> close
  | .stmt => o ++ "(Astmt)"
  | .expr => o ++ "(Aexpr)"

def decodeAnnot : Sx → Except String Annot
  | .node "Astd" #[s] => return .std (← decodeStr s)
  | .node "Aloc" #[l] => return .loc (← decodeLoc l)
  | .node "Auid" #[s] => return .uid (← decodeStr s)
  | .node "Amarker" #[n] => return .marker (← decodeNat n)
  | .node "Amarker_object_types" #[n] => return .markerObjectTypes (← decodeNat n)
  | .node "Abmc" #[.node "Abmc_id" #[n]] => return .bmc (.id (← decodeNat n))
  | .node "Aattrs" #[a] => return .attrs (← decodeAttributes a)
  | .node "Atypedef" #[s] => return .typedef (← decodeSym s)
  | .node "Alabel" #[a] => return .label (← decodeLabelAnnot a)
  | .node "Acerb" #[.node "ACerb_with_address" #[n]] => return .cerb (.withAddress (← decodeInt n))
  | .node "Acerb" #[.node "ACerb_hidden" #[]] => return .cerb .hidden
  | .node "Avalue" #[.node "Ainteger" #[t]] => return .value (.integer (← decodeIntegerType t))
  | .node "Ainlined_label" #[.node "$tuple" #[l, s, a]] =>
    return .inlinedLabel (← decodeLoc l, ← decodeSym s, ← decodeLabelAnnot a)
  | .node "Astmt" #[] => return .stmt
  | .node "Aexpr" #[] => return .expr
  | t => mismatch "Annot.annot" t

def emitLoopAttribute (x : LoopAttribute) (o : Out) : Out :=
  o |> open_ "loop_attribute" |> arg (emitNat x.markerId) |> arg (emitAttributes x.attributes)
    |> arg (emitLoc x.conditionLoc) |> arg (emitLoc x.loopLoc) |> close

def decodeLoopAttribute : Sx → Except String LoopAttribute
  | .node "loop_attribute" #[m, a, c, l] =>
    return ⟨← decodeNat m, ← decodeAttributes a, ← decodeLoc c, ← decodeLoc l⟩
  | t => mismatch "Annot.loop_attribute" t

/-! ## C types -/

def emitFloatingType (x : FloatingType) (o : Out) : Out :=
  match x with
  | .realFloating .float => o ++ "(RealFloating (Float))"
  | .realFloating .double => o ++ "(RealFloating (Double))"
  | .realFloating .longDouble => o ++ "(RealFloating (LongDouble))"

def decodeFloatingType : Sx → Except String FloatingType
  | .node "RealFloating" #[.node "Float" #[]] => return .realFloating .float
  | .node "RealFloating" #[.node "Double" #[]] => return .realFloating .double
  | .node "RealFloating" #[.node "LongDouble" #[]] => return .realFloating .longDouble
  | t => mismatch "Ctype.floatingType" t

def emitBasicType (x : BasicType) (o : Out) : Out :=
  match x with
  | .integer t => o |> open_ "Integer" |> arg (emitIntegerType t) |> close
  | .floating t => o |> open_ "Floating" |> arg (emitFloatingType t) |> close

def decodeBasicType : Sx → Except String BasicType
  | .node "Integer" #[t] => return .integer (← decodeIntegerType t)
  | .node "Floating" #[t] => return .floating (← decodeFloatingType t)
  | t => mismatch "Ctype.basicType" t

def emitQualifiers (q : Qualifiers) (o : Out) : Out :=
  o |> open_ "qualifiers" |> arg (emitBool q.const) |> arg (emitBool q.restrict)
    |> arg (emitBool q.volatile) |> close

def decodeQualifiers : Sx → Except String Qualifiers
  | .node "qualifiers" #[c, r, v] => return ⟨← decodeBool c, ← decodeBool r, ← decodeBool v⟩
  | t => mismatch "Ctype.qualifiers" t

mutual

partial def emitCtype (x : Ctype) (o : Out) : Out :=
  match x with
  | .mk as t => o |> open_ "Ctype" |> arg (emitList emitAnnot as) |> arg (emitCtypeNode t) |> close

partial def emitCtypeNode (x : CtypeNode) (o : Out) : Out :=
  match x with
  | .void => o ++ "(Void)"
  | .basic b => o |> open_ "Basic" |> arg (emitBasicType b) |> close
  | .array t n => o |> open_ "Array" |> arg (emitCtype t) |> arg (emitOption emitInt n) |> close
  | .function r ps v =>
    o |> open_ "Function" |> arg (emitTuple2 emitQualifiers emitCtype r)
      |> arg (emitList emitParam ps) |> arg (emitBool v) |> close
  | .functionNoParams r =>
    o |> open_ "FunctionNoParams" |> arg (emitTuple2 emitQualifiers emitCtype r) |> close
  | .pointer q t => o |> open_ "Pointer" |> arg (emitQualifiers q) |> arg (emitCtype t) |> close
  | .atomic t => o |> open_ "Atomic" |> arg (emitCtype t) |> close
  | .struct s => o |> open_ "Struct" |> arg (emitSym s) |> close
  | .union s => o |> open_ "Union" |> arg (emitSym s) |> close
  | .byte => o ++ "(Byte)"

/-- A parameter `(qualifiers * ctype * bool)`, a flat triple. -/
partial def emitParam (p : Qualifiers × Ctype × Bool) (o : Out) : Out :=
  o |> open_ "$tuple" |> arg (emitQualifiers p.1) |> arg (emitCtype p.2.1) |> arg (emitBool p.2.2)
    |> close

end

mutual

partial def decodeCtype : Sx → Except String Ctype
  | .node "Ctype" #[as, t] => return .mk (← decodeList decodeAnnot as) (← decodeCtypeNode t)
  | t => mismatch "Ctype.ctype" t

partial def decodeCtypeNode : Sx → Except String CtypeNode
  | .node "Void" #[] => return .void
  | .node "Basic" #[b] => return .basic (← decodeBasicType b)
  | .node "Array" #[t, n] => return .array (← decodeCtype t) (← decodeOption decodeInt n)
  | .node "Function" #[r, ps, v] =>
    return .function (← decodeTuple2 decodeQualifiers decodeCtype r) (← decodeList decodeParam ps)
      (← decodeBool v)
  | .node "FunctionNoParams" #[r] =>
    return .functionNoParams (← decodeTuple2 decodeQualifiers decodeCtype r)
  | .node "Pointer" #[q, t] => return .pointer (← decodeQualifiers q) (← decodeCtype t)
  | .node "Atomic" #[t] => return .atomic (← decodeCtype t)
  | .node "Struct" #[s] => return .struct (← decodeSym s)
  | .node "Union" #[s] => return .union (← decodeSym s)
  | .node "Byte" #[] => return .byte
  | t => mismatch "Ctype.ctype_" t

partial def decodeParam : Sx → Except String (Qualifiers × Ctype × Bool)
  | .node "$tuple" #[q, t, b] => return (← decodeQualifiers q, ← decodeCtype t, ← decodeBool b)
  | t => mismatch "a parameter" t

end

def emitAlignment (x : Alignment) (o : Out) : Out :=
  match x with
  | .integer n => o |> open_ "AlignInteger" |> arg (emitInt n) |> close
  | .ctype t => o |> open_ "AlignType" |> arg (emitCtype t) |> close

def decodeAlignment : Sx → Except String Alignment
  | .node "AlignInteger" #[n] => return .integer (← decodeInt n)
  | .node "AlignType" #[t] => return .ctype (← decodeCtype t)
  | t => mismatch "Ctype.alignment" t

def emitFlexibleArrayMember (x : FlexibleArrayMember) (o : Out) : Out :=
  match x with
  | .mk a i q t => o |> open_ "FlexibleArrayMember" |> arg (emitAttributes a)
      |> arg (emitIdentifier i) |> arg (emitQualifiers q) |> arg (emitCtype t) |> close

def decodeFlexibleArrayMember : Sx → Except String FlexibleArrayMember
  | .node "FlexibleArrayMember" #[a, i, q, t] =>
    return .mk (← decodeAttributes a) (← decodeIdentifier i) (← decodeQualifiers q) (← decodeCtype t)
  | t => mismatch "Ctype.flexible_array_member" t

/-- A member `(identifier * (attributes * maybe alignment * qualifiers * ctype))`. -/
def emitMember (m : Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)) (o : Out) :
    Out :=
  let (i, a, n, q, t) := m
  o |> open_ "$tuple" |> arg (emitIdentifier i)
    |> arg (fun o => o |> open_ "$tuple" |> arg (emitAttributes a) |> arg (emitOption emitAlignment n)
      |> arg (emitQualifiers q) |> arg (emitCtype t) |> close) |> close

def decodeMember : Sx → Except String (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))
  | .node "$tuple" #[i, .node "$tuple" #[a, n, q, t]] =>
    return (← decodeIdentifier i, ← decodeAttributes a, ← decodeOption decodeAlignment n,
      ← decodeQualifiers q, ← decodeCtype t)
  | t => mismatch "a member" t

def emitTagDefinition (x : TagDefinition) (o : Out) : Out :=
  match x with
  | .struct ms f => o |> open_ "StructDef" |> arg (emitList emitMember ms)
      |> arg (emitOption emitFlexibleArrayMember f) |> close
  | .union ms => o |> open_ "UnionDef" |> arg (emitList emitMember ms) |> close

def decodeTagDefinition : Sx → Except String TagDefinition
  | .node "StructDef" #[ms, f] =>
    return .struct (← decodeList decodeMember ms) (← decodeOption decodeFlexibleArrayMember f)
  | .node "UnionDef" #[ms] => return .union (← decodeList decodeMember ms)
  | t => mismatch "Ctype.tag_definition" t

/-! ## Operators (`AilSyntax`, shared with Core) -/

def emitArithmeticOperator (x : ArithmeticOperator) (o : Out) : Out :=
  o ++ match x with
  | .mul => "(Mul)" | .div => "(Div)" | .mod => "(Mod)" | .add => "(Add)" | .sub => "(Sub)"
  | .shl => "(Shl)" | .shr => "(Shr)" | .band => "(Band)" | .bxor => "(Bxor)" | .bor => "(Bor)"

def decodeArithmeticOperator : Sx → Except String ArithmeticOperator
  | .node "Mul" #[] => return .mul
  | .node "Div" #[] => return .div
  | .node "Mod" #[] => return .mod
  | .node "Add" #[] => return .add
  | .node "Sub" #[] => return .sub
  | .node "Shl" #[] => return .shl
  | .node "Shr" #[] => return .shr
  | .node "Band" #[] => return .band
  | .node "Bxor" #[] => return .bxor
  | .node "Bor" #[] => return .bor
  | t => mismatch "AilSyntax.arithmeticOperator" t

def emitUnaryOperator (x : UnaryOperator) (o : Out) : Out :=
  o ++ match x with
  | .plus => "(Plus)" | .minus => "(Minus)" | .bnot => "(Bnot)" | .address => "(Address)"
  | .indirection => "(Indirection)" | .postfixIncr => "(PostfixIncr)"
  | .postfixDecr => "(PostfixDecr)"

def decodeUnaryOperator : Sx → Except String UnaryOperator
  | .node "Plus" #[] => return .plus
  | .node "Minus" #[] => return .minus
  | .node "Bnot" #[] => return .bnot
  | .node "Address" #[] => return .address
  | .node "Indirection" #[] => return .indirection
  | .node "PostfixIncr" #[] => return .postfixIncr
  | .node "PostfixDecr" #[] => return .postfixDecr
  | t => mismatch "AilSyntax.unaryOperator" t

def emitBinaryOperator (x : BinaryOperator) (o : Out) : Out :=
  match x with
  | .arithmetic a => o |> open_ "Arithmetic" |> arg (emitArithmeticOperator a) |> close
  | .comma => o ++ "(Comma)"
  | .and => o ++ "(And)"
  | .or => o ++ "(Or)"
  | .lt => o ++ "(Lt)"
  | .gt => o ++ "(Gt)"
  | .le => o ++ "(Le)"
  | .ge => o ++ "(Ge)"
  | .eq => o ++ "(Eq)"
  | .ne => o ++ "(Ne)"

def decodeBinaryOperator : Sx → Except String BinaryOperator
  | .node "Arithmetic" #[a] => return .arithmetic (← decodeArithmeticOperator a)
  | .node "Comma" #[] => return .comma
  | .node "And" #[] => return .and
  | .node "Or" #[] => return .or
  | .node "Lt" #[] => return .lt
  | .node "Gt" #[] => return .gt
  | .node "Le" #[] => return .le
  | .node "Ge" #[] => return .ge
  | .node "Eq" #[] => return .eq
  | .node "Ne" #[] => return .ne
  | t => mismatch "AilSyntax.binaryOperator" t

end Silmaril.Cerberus.Ail.Codec
