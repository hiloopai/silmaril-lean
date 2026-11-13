module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.Cerberus.Ail.CtypeCodec.Defs

/-! # The wire codec of Ail and typed-Ail documents

Cerberus's oracle (`cerb-oracle --level ail|tail`) prints the Ail of a translation unit, or the
error that stopped it, in the tagged S-expression dialect of `docs/projects/cerberus.md`:

```
($document_ail 1 ($str "<cerberus commit>") ($str "<impl>") <AilSyntax.ail_program unit>)
($document_tail 1 ($str "<cerberus commit>") ($str "<impl>") <AilSyntax.ail_program GenTypes.genTypeCategory>)
($reject 1 ($str "<cerberus commit>") ($str "<impl>") ($str "<stage>") <loc> ($str "<message>"))
```

each followed by one newline. Tags are the Lem names of `Silmaril.Cerberus.Ail.Names`; the
types delegated to the Core exporter (symbols, C types, annotations) are encoded by
`Silmaril.Cerberus.Ail.CtypeCodec`, and CN, locations, identifiers, attributes and raw strings
by `Silmaril.Cerberus.Cabs.Codec`. Lem tuples print flat (`(a, (b, c))` of a Lem triple is
`($tuple a b c)`), and Lem maps print as `($map ($tuple k v)…)` in key order.

The reject location is a `Loc.t` or, for some typing errors, the `$loc_regions` dialect
extension of the Silmaril exporter: `RejectLoc`.

Every emitter and decoder of an annotated tree takes the codec of the annotation, so the same
functions serve untyped Ail (`Unit`, `$unit`) and typed Ail (`GenTypeCategory`).
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail.Codec

open Silmaril.Cerberus Cabs.Wire
open Silmaril.Cerberus.Cabs (RawString)
open Silmaril.Cerberus.Cabs.Codec (emitLoc decodeLoc emitIdentifier decodeIdentifier
  emitAttributes decodeAttributes emitRawString decodeRawString emitCnFunction decodeCnFunction
  emitCnLemma decodeCnLemma emitCnPredicate decodeCnPredicate emitCnDatatype decodeCnDatatype
  emitCnDeclSpec decodeCnDeclSpec emitTypeName decodeTypeName)

/-! ## Flat tuples and maps -/

@[inline] def emitTuple3 {α β γ : Type} (ea : α → Out → Out) (eb : β → Out → Out)
    (ec : γ → Out → Out) (p : α × β × γ) (o : Out) : Out :=
  o |> open_ "$tuple" |> arg (ea p.1) |> arg (eb p.2.1) |> arg (ec p.2.2) |> close

@[inline] def decodeTuple3 {α β γ : Type} (da : Sx → Except String α) (db : Sx → Except String β)
    (dc : Sx → Except String γ) : Sx → Except String (α × β × γ)
  | .node "$tuple" #[a, b, c] => return (← da a, ← db b, ← dc c)
  | t => mismatch "a triple" t

/-- A Lem map, as its bindings in key order. -/
@[inline] def emitMap {κ ν : Type} (ek : κ → Out → Out) (ev : ν → Out → Out) (xs : List (κ × ν))
    (o : Out) : Out :=
  close (xs.foldl (fun o x => arg (emitTuple2 ek ev x) o) (open_ "$map" o))

@[inline] def decodeMap {κ ν : Type} (dk : Sx → Except String κ) (dv : Sx → Except String ν) :
    Sx → Except String (List (κ × ν))
  | .node "$map" xs => return (← xs.mapM (decodeTuple2 dk dv)).toList
  | t => mismatch "a map" t

def emitUnit (_ : Unit) (o : Out) : Out := o ++ "($unit)"

def decodeUnit : Sx → Except String Unit
  | .node "$unit" #[] => return ()
  | t => mismatch "$unit" t

/-! ## Constants -/

def emitIntegerSuffix (x : IntegerSuffix) (o : Out) : Out :=
  o ++ match x with
  | .u => "(U)" | .ul => "(UL)" | .ull => "(ULL)" | .l => "(L)" | .ll => "(LL)"

def decodeIntegerSuffix : Sx → Except String IntegerSuffix
  | .node "U" #[] => return .u
  | .node "UL" #[] => return .ul
  | .node "ULL" #[] => return .ull
  | .node "L" #[] => return .l
  | .node "LL" #[] => return .ll
  | t => mismatch "AilSyntax.integerSuffix" t

def emitBasis (x : Basis) (o : Out) : Out :=
  o ++ match x with
  | .octal => "(Octal)" | .decimal => "(Decimal)" | .hexadecimal => "(Hexadecimal)"
  | .binary => "(Binary)"

def decodeBasis : Sx → Except String Basis
  | .node "Octal" #[] => return .octal
  | .node "Decimal" #[] => return .decimal
  | .node "Hexadecimal" #[] => return .hexadecimal
  | .node "Binary" #[] => return .binary
  | t => mismatch "AilSyntax.basis" t

def emitIntegerConstant (x : IntegerConstant) (o : Out) : Out :=
  match x with
  | .iconstant v b s => o |> open_ "IConstant" |> arg (emitInt v) |> arg (emitBasis b)
      |> arg (emitOption emitIntegerSuffix s) |> close
  | .max t => o |> open_ "IConstantMax" |> arg (emitIntegerType t) |> close
  | .min t => o |> open_ "IConstantMin" |> arg (emitIntegerType t) |> close

def decodeIntegerConstant : Sx → Except String IntegerConstant
  | .node "IConstant" #[v, b, s] =>
    return .iconstant (← decodeInt v) (← decodeBasis b) (← decodeOption decodeIntegerSuffix s)
  | .node "IConstantMax" #[t] => return .max (← decodeIntegerType t)
  | .node "IConstantMin" #[t] => return .min (← decodeIntegerType t)
  | t => mismatch "AilSyntax.integerConstant" t

def emitFloatingSuffix (x : FloatingSuffix) (o : Out) : Out :=
  o ++ match x with | .f => "(Fsuf_F)" | .l => "(Fsuf_L)"

def decodeFloatingSuffix : Sx → Except String FloatingSuffix
  | .node "Fsuf_F" #[] => return .f
  | .node "Fsuf_L" #[] => return .l
  | t => mismatch "AilSyntax.floatingSuffix" t

def emitFloatingConstant (x : FloatingConstant) (o : Out) : Out :=
  emitTuple2 emitStr (emitOption emitFloatingSuffix) x o

def decodeFloatingConstant : Sx → Except String FloatingConstant :=
  decodeTuple2 decodeStr (decodeOption decodeFloatingSuffix)

def emitCharacterPrefix (x : CharacterPrefix) (o : Out) : Out :=
  o ++ match x with | .wide => "(Pref_L)" | .utf16 => "(Pref_u)" | .utf32 => "(Pref_U)"

def decodeCharacterPrefix : Sx → Except String CharacterPrefix
  | .node "Pref_L" #[] => return .wide
  | .node "Pref_u" #[] => return .utf16
  | .node "Pref_U" #[] => return .utf32
  | t => mismatch "AilSyntax.characterPrefix" t

def emitCharacterConstant (x : CharacterConstant) (o : Out) : Out :=
  emitTuple2 (emitOption emitCharacterPrefix) emitRawString x o

def decodeCharacterConstant : Sx → Except String CharacterConstant :=
  decodeTuple2 (decodeOption decodeCharacterPrefix) decodeRawString

def emitPredefinedConstant (x : PredefinedConstant) (o : Out) : Out :=
  o ++ match x with | .false_ => "(PConstantFalse)" | .true_ => "(PConstantTrue)"

def decodePredefinedConstant : Sx → Except String PredefinedConstant
  | .node "PConstantFalse" #[] => return .false_
  | .node "PConstantTrue" #[] => return .true_
  | t => mismatch "AilSyntax.predefinedConstant" t

def emitEncodingPrefix (x : EncodingPrefix) (o : Out) : Out :=
  o ++ match x with
  | .utf8 => "(Enc_u8)" | .utf16 => "(Enc_u)" | .utf32 => "(Enc_U)" | .wide => "(Enc_L)"

def decodeEncodingPrefix : Sx → Except String EncodingPrefix
  | .node "Enc_u8" #[] => return .utf8
  | .node "Enc_u" #[] => return .utf16
  | .node "Enc_U" #[] => return .utf32
  | .node "Enc_L" #[] => return .wide
  | t => mismatch "AilSyntax.encodingPrefix" t

def emitStringLiteral (s : StringLiteral) (o : Out) : Out :=
  emitTuple2 (emitOption emitEncodingPrefix) (emitList (emitTuple2 emitLoc
      (emitList emitRawString))) s o

def decodeStringLiteral : Sx → Except String StringLiteral :=
  decodeTuple2 (decodeOption decodeEncodingPrefix) (decodeList (decodeTuple2 decodeLoc
      (decodeList decodeRawString)))

partial def emitConstant (x : Constant) (o : Out) : Out :=
  match x with
  | .indeterminate t => o |> open_ "ConstantIndeterminate" |> arg (emitCtype t) |> close
  | .null => o ++ "(ConstantNull)"
  | .integer c => o |> open_ "ConstantInteger" |> arg (emitIntegerConstant c) |> close
  | .floating c => o |> open_ "ConstantFloating" |> arg (emitFloatingConstant c) |> close
  | .character c => o |> open_ "ConstantCharacter" |> arg (emitCharacterConstant c) |> close
  | .array t cs => o |> open_ "ConstantArray" |> arg (emitCtype t) |> arg (emitList emitConstant cs)
      |> close
  | .struct s ms => o |> open_ "ConstantStruct" |> arg (emitSym s)
      |> arg (emitList (emitTuple2 emitIdentifier emitConstant) ms) |> close
  | .union s m c => o |> open_ "ConstantUnion" |> arg (emitSym s) |> arg (emitIdentifier m)
      |> arg (emitConstant c) |> close
  | .predefined c => o |> open_ "ConstantPredefined" |> arg (emitPredefinedConstant c) |> close

partial def decodeConstant : Sx → Except String Constant
  | .node "ConstantIndeterminate" #[t] => return .indeterminate (← decodeCtype t)
  | .node "ConstantNull" #[] => return .null
  | .node "ConstantInteger" #[c] => return .integer (← decodeIntegerConstant c)
  | .node "ConstantFloating" #[c] => return .floating (← decodeFloatingConstant c)
  | .node "ConstantCharacter" #[c] => return .character (← decodeCharacterConstant c)
  | .node "ConstantArray" #[t, cs] => return .array (← decodeCtype t) (← decodeList decodeConstant cs)
  | .node "ConstantStruct" #[s, ms] =>
    return .struct (← decodeSym s) (← decodeList (decodeTuple2 decodeIdentifier decodeConstant) ms)
  | .node "ConstantUnion" #[s, m, c] =>
    return .union (← decodeSym s) (← decodeIdentifier m) (← decodeConstant c)
  | .node "ConstantPredefined" #[c] => return .predefined (← decodePredefinedConstant c)
  | t => mismatch "AilSyntax.constant" t

/-! ## Builtins, storage and declarations -/

def emitBuiltinAtomic (x : BuiltinAtomic) (o : Out) : Out :=
  o ++ match x with
  | .threadFence => "(AilBAthread_fence)" | .store => "(AilBAstore)" | .load => "(AilBAload)"
  | .exchange => "(AilBAexchange)"
  | .compareExchangeStrong => "(AilBAcompare_exchange_strong)"
  | .compareExchangeWeak => "(AilBAcompare_exchange_weak)"
  | .fetchKey => "(AilBAfetch_key)"

def decodeBuiltinAtomic : Sx → Except String BuiltinAtomic
  | .node "AilBAthread_fence" #[] => return .threadFence
  | .node "AilBAstore" #[] => return .store
  | .node "AilBAload" #[] => return .load
  | .node "AilBAexchange" #[] => return .exchange
  | .node "AilBAcompare_exchange_strong" #[] => return .compareExchangeStrong
  | .node "AilBAcompare_exchange_weak" #[] => return .compareExchangeWeak
  | .node "AilBAfetch_key" #[] => return .fetchKey
  | t => mismatch "AilSyntax.ail_builtin_atomic" t

def emitBuiltinLinux (x : BuiltinLinux) (o : Out) : Out :=
  o ++ match x with
  | .fence => "(AilBLfence)" | .read => "(AilBLread)" | .write => "(AilBLwrite)"
  | .rmw => "(AilBLrmw)"

def decodeBuiltinLinux : Sx → Except String BuiltinLinux
  | .node "AilBLfence" #[] => return .fence
  | .node "AilBLread" #[] => return .read
  | .node "AilBLwrite" #[] => return .write
  | .node "AilBLrmw" #[] => return .rmw
  | t => mismatch "AilSyntax.ail_builtin_linux" t

def emitBuiltin (x : Builtin) (o : Out) : Out :=
  match x with
  | .atomic b => o |> open_ "AilBatomic" |> arg (emitBuiltinAtomic b) |> close
  | .linux b => o |> open_ "AilBlinux" |> arg (emitBuiltinLinux b) |> close
  | .copyAllocId => o ++ "(AilBcopy_alloc_id)"
  | .cheri s => o |> open_ "AilBCHERI" |> arg (emitStr s) |> close

def decodeBuiltin : Sx → Except String Builtin
  | .node "AilBatomic" #[b] => return .atomic (← decodeBuiltinAtomic b)
  | .node "AilBlinux" #[b] => return .linux (← decodeBuiltinLinux b)
  | .node "AilBcopy_alloc_id" #[] => return .copyAllocId
  | .node "AilBCHERI" #[s] => return .cheri (← decodeStr s)
  | t => mismatch "AilSyntax.ail_builtin" t

def emitStorageDuration (x : StorageDuration) (o : Out) : Out :=
  o ++ match x with | .static => "(Static)" | .thread => "(Thread)" | .automatic => "(Automatic)"

def decodeStorageDuration : Sx → Except String StorageDuration
  | .node "Static" #[] => return .static
  | .node "Thread" #[] => return .thread
  | .node "Automatic" #[] => return .automatic
  | t => mismatch "AilSyntax.storageDuration" t

/-- One binding `(ail_identifier * ((Loc.t * storageDuration * bool) * maybe alignment *
qualifiers * ctype))`. -/
def emitBinding (b : Sym × ((Loc × StorageDuration × Bool) × Option Alignment × Qualifiers × Ctype))
    (o : Out) : Out :=
  let (x, (l, d, r), a, q, t) := b
  o |> open_ "$tuple" |> arg (emitSym x)
    |> arg (fun o => o |> open_ "$tuple"
      |> arg (emitTuple3 emitLoc emitStorageDuration emitBool (l, d, r))
      |> arg (emitOption emitAlignment a) |> arg (emitQualifiers q) |> arg (emitCtype t) |> close)
    |> close

def decodeBinding :
    Sx → Except String (Sym × ((Loc × StorageDuration × Bool) × Option Alignment × Qualifiers × Ctype))
  | .node "$tuple" #[x, .node "$tuple" #[s, a, q, t]] =>
    return (← decodeSym x, ← decodeTuple3 decodeLoc decodeStorageDuration decodeBool s,
      ← decodeOption decodeAlignment a, ← decodeQualifiers q, ← decodeCtype t)
  | t => mismatch "a binding" t

def emitBindings (b : Bindings) (o : Out) : Out := emitList emitBinding b o

def decodeBindings : Sx → Except String Bindings := decodeList decodeBinding

def emitDesugCase (x : DesugCase) (o : Out) : Out :=
  o ++ match x with | .forloop => "(Desug_forloop)" | .continue_ => "(Desug_continue)"

def decodeDesugCase : Sx → Except String DesugCase
  | .node "Desug_forloop" #[] => return .forloop
  | .node "Desug_continue" #[] => return .continue_
  | t => mismatch "AilSyntax.desug_case" t

def emitDesugInfo (x : DesugInfo) (o : Out) : Out :=
  o |> open_ "desug_info" |> arg (emitBool x.isForloopBody)
    |> arg (emitOption emitDesugCase x.desugCase) |> close

def decodeDesugInfo : Sx → Except String DesugInfo
  | .node "desug_info" #[b, c] => return ⟨← decodeBool b, ← decodeOption decodeDesugCase c⟩
  | t => mismatch "AilSyntax.desug_info" t

def emitInvalidReason (x : InvalidReason) (o : Out) : Out :=
  match x with
  | .desugaringInitFailed s =>
    o |> open_ "AilInvalid_desugaring_init_failed" |> arg (emitStr s) |> close
  | .other s => o |> open_ "AilInvalid_other" |> arg (emitStr s) |> close

def decodeInvalidReason : Sx → Except String InvalidReason
  | .node "AilInvalid_desugaring_init_failed" #[s] => return .desugaringInitFailed (← decodeStr s)
  | .node "AilInvalid_other" #[s] => return .other (← decodeStr s)
  | t => mismatch "AilSyntax.ail_invalid_reason" t

/-! ## Generic types (typed Ail) -/

partial def emitGenIntegerType (x : GenIntegerType) (o : Out) : Out :=
  match x with
  | .concrete t => o |> open_ "Concrete" |> arg (emitIntegerType t) |> close
  | .sizeT => o ++ "(SizeT)"
  | .ptrdiffT => o ++ "(PtrdiffT)"
  | .ptraddrT => o ++ "(PtraddrT)"
  | .unknown c => o |> open_ "Unknown" |> arg (emitIntegerConstant c) |> close
  | .promote t => o |> open_ "Promote" |> arg (emitGenIntegerType t) |> close
  | .usual a b => o |> open_ "Usual" |> arg (emitGenIntegerType a) |> arg (emitGenIntegerType b)
      |> close

partial def decodeGenIntegerType : Sx → Except String GenIntegerType
  | .node "Concrete" #[t] => return .concrete (← decodeIntegerType t)
  | .node "SizeT" #[] => return .sizeT
  | .node "PtrdiffT" #[] => return .ptrdiffT
  | .node "PtraddrT" #[] => return .ptraddrT
  | .node "Unknown" #[c] => return .unknown (← decodeIntegerConstant c)
  | .node "Promote" #[t] => return .promote (← decodeGenIntegerType t)
  | .node "Usual" #[a, b] => return .usual (← decodeGenIntegerType a) (← decodeGenIntegerType b)
  | t => mismatch "GenTypes.genIntegerType" t

def emitGenBasicType (x : GenBasicType) (o : Out) : Out :=
  match x with
  | .integer t => o |> open_ "GenInteger" |> arg (emitGenIntegerType t) |> close
  | .floating t => o |> open_ "GenFloating" |> arg (emitFloatingType t) |> close

def decodeGenBasicType : Sx → Except String GenBasicType
  | .node "GenInteger" #[t] => return .integer (← decodeGenIntegerType t)
  | .node "GenFloating" #[t] => return .floating (← decodeFloatingType t)
  | t => mismatch "GenTypes.genBasicType" t

partial def emitGenType (x : GenType) (o : Out) : Out :=
  match x with
  | .void => o ++ "(GenVoid)"
  | .basic t => o |> open_ "GenBasic" |> arg (emitGenBasicType t) |> close
  | .array t n => o |> open_ "GenArray" |> arg (emitCtype t) |> arg (emitOption emitInt n) |> close
  | .function r ps v => o |> open_ "GenFunction" |> arg (emitTuple2 emitQualifiers emitCtype r)
      |> arg (emitList emitParam ps) |> arg (emitBool v) |> close
  | .functionNoParams r =>
    o |> open_ "GenFunctionNoParams" |> arg (emitTuple2 emitQualifiers emitCtype r) |> close
  | .pointer q t => o |> open_ "GenPointer" |> arg (emitQualifiers q) |> arg (emitCtype t) |> close
  | .struct s => o |> open_ "GenStruct" |> arg (emitSym s) |> close
  | .union s => o |> open_ "GenUnion" |> arg (emitSym s) |> close
  | .atomic t => o |> open_ "GenAtomic" |> arg (emitGenType t) |> close
  | .byte => o ++ "(GenByte)"

partial def decodeGenType : Sx → Except String GenType
  | .node "GenVoid" #[] => return .void
  | .node "GenBasic" #[t] => return .basic (← decodeGenBasicType t)
  | .node "GenArray" #[t, n] => return .array (← decodeCtype t) (← decodeOption decodeInt n)
  | .node "GenFunction" #[r, ps, v] =>
    return .function (← decodeTuple2 decodeQualifiers decodeCtype r) (← decodeList decodeParam ps)
      (← decodeBool v)
  | .node "GenFunctionNoParams" #[r] =>
    return .functionNoParams (← decodeTuple2 decodeQualifiers decodeCtype r)
  | .node "GenPointer" #[q, t] => return .pointer (← decodeQualifiers q) (← decodeCtype t)
  | .node "GenStruct" #[s] => return .struct (← decodeSym s)
  | .node "GenUnion" #[s] => return .union (← decodeSym s)
  | .node "GenAtomic" #[t] => return .atomic (← decodeGenType t)
  | .node "GenByte" #[] => return .byte
  | t => mismatch "GenTypes.genType" t

def emitGenTypeCategory (x : GenTypeCategory) (o : Out) : Out :=
  match x with
  | .lvalue q t r => o |> open_ "GenLValueType" |> arg (emitQualifiers q) |> arg (emitCtype t)
      |> arg (emitBool r) |> close
  | .rvalue t => o |> open_ "GenRValueType" |> arg (emitGenType t) |> close

def decodeGenTypeCategory : Sx → Except String GenTypeCategory
  | .node "GenLValueType" #[q, t, r] =>
    return .lvalue (← decodeQualifiers q) (← decodeCtype t) (← decodeBool r)
  | .node "GenRValueType" #[t] => return .rvalue (← decodeGenType t)
  | t => mismatch "GenTypes.genTypeCategory" t

/-! ## Expressions and statements -/

section Trees

variable {α : Type}

mutual

partial def emitExpressionNode (ea : α → Out → Out) (x : ExpressionNode α) (o : Out) : Out :=
  let e := emitExpression ea
  match x with
  | .unary op a => o |> open_ "AilEunary" |> arg (emitUnaryOperator op) |> arg (e a) |> close
  | .binary a op b => o |> open_ "AilEbinary" |> arg (e a) |> arg (emitBinaryOperator op)
      |> arg (e b) |> close
  | .assign a b => o |> open_ "AilEassign" |> arg (e a) |> arg (e b) |> close
  | .compoundAssign a op b => o |> open_ "AilEcompoundAssign" |> arg (e a)
      |> arg (emitArithmeticOperator op) |> arg (e b) |> close
  | .cond c a b => o |> open_ "AilEcond" |> arg (e c) |> arg (emitOption e a) |> arg (e b) |> close
  | .cast q t a => o |> open_ "AilEcast" |> arg (emitQualifiers q) |> arg (emitCtype t) |> arg (e a)
      |> close
  | .call f args => o |> open_ "AilEcall" |> arg (e f) |> arg (emitList e args) |> close
  | .assert a => o |> open_ "AilEassert" |> arg (e a) |> close
  | .offsetof t m => o |> open_ "AilEoffsetof" |> arg (emitCtype t) |> arg (emitIdentifier m) |> close
  | .generic a n gas => o |> open_ "AilEgeneric" |> arg (e a) |> arg (emitOption emitNat n)
      |> arg (emitList (emitGenericAssociation ea) gas) |> close
  | .array b t xs => o |> open_ "AilEarray" |> arg (emitBool b) |> arg (emitCtype t)
      |> arg (emitList (emitOption e) xs) |> close
  | .struct s ms => o |> open_ "AilEstruct" |> arg (emitSym s)
      |> arg (emitList (emitTuple2 emitIdentifier (emitOption e)) ms) |> close
  | .union s m v => o |> open_ "AilEunion" |> arg (emitSym s) |> arg (emitIdentifier m)
      |> arg (emitOption e v) |> close
  | .compound q t a => o |> open_ "AilEcompound" |> arg (emitQualifiers q) |> arg (emitCtype t)
      |> arg (e a) |> close
  | .memberof a m => o |> open_ "AilEmemberof" |> arg (e a) |> arg (emitIdentifier m) |> close
  | .memberofptr a m => o |> open_ "AilEmemberofptr" |> arg (e a) |> arg (emitIdentifier m) |> close
  | .builtin b => o |> open_ "AilEbuiltin" |> arg (emitBuiltin b) |> close
  | .str s => o |> open_ "AilEstr" |> arg (emitStringLiteral s) |> close
  | .const c => o |> open_ "AilEconst" |> arg (emitConstant c) |> close
  | .ident x => o |> open_ "AilEident" |> arg (emitSym x) |> close
  | .sizeof q t => o |> open_ "AilEsizeof" |> arg (emitQualifiers q) |> arg (emitCtype t) |> close
  | .sizeofExpr a => o |> open_ "AilEsizeof_expr" |> arg (e a) |> close
  | .alignof q t => o |> open_ "AilEalignof" |> arg (emitQualifiers q) |> arg (emitCtype t) |> close
  | .annot t a => o |> open_ "AilEannot" |> arg (emitCtype t) |> arg (e a) |> close
  | .vaStart a x => o |> open_ "AilEva_start" |> arg (e a) |> arg (emitSym x) |> close
  | .vaArg a t => o |> open_ "AilEva_arg" |> arg (e a) |> arg (emitCtype t) |> close
  | .vaCopy a b => o |> open_ "AilEva_copy" |> arg (e a) |> arg (e b) |> close
  | .vaEnd a => o |> open_ "AilEva_end" |> arg (e a) |> close
  | .printType a => o |> open_ "AilEprint_type" |> arg (e a) |> close
  | .bmcAssume a => o |> open_ "AilEbmc_assume" |> arg (e a) |> close
  | .regLoad r => o |> open_ "AilEreg_load" |> arg (emitNat r) |> close
  | .rvalue a => o |> open_ "AilErvalue" |> arg (e a) |> close
  | .arrayDecay a => o |> open_ "AilEarray_decay" |> arg (e a) |> close
  | .functionDecay a => o |> open_ "AilEfunction_decay" |> arg (e a) |> close
  | .atomic a => o |> open_ "AilEatomic" |> arg (e a) |> close
  | .labelAddressGnu l => o |> open_ "AilElabel_addressGNU" |> arg (emitSym l) |> close
  | .gccStatement bs ss => o |> open_ "AilEgcc_statement" |> arg (emitBindings bs)
      |> arg (emitList (emitStatement ea) ss) |> close
  | .invalid t r => o |> open_ "AilEinvalid" |> arg (emitCtype t) |> arg (emitInvalidReason r)
      |> close

partial def emitGenericAssociation (ea : α → Out → Out) (x : GenericAssociation α) (o : Out) : Out :=
  match x with
  | .type_ q t a => o |> open_ "AilGAtype" |> arg (emitQualifiers q) |> arg (emitCtype t)
      |> arg (emitExpression ea a) |> close
  | .default a => o |> open_ "AilGAdefault" |> arg (emitExpression ea a) |> close

partial def emitExpression (ea : α → Out → Out) (x : Expression α) (o : Out) : Out :=
  match x with
  | .mk a as l n => o |> open_ "AnnotatedExpression" |> arg (ea a) |> arg (emitList emitAnnot as)
      |> arg (emitLoc l) |> arg (emitExpressionNode ea n) |> close

partial def emitStatementNode (ea : α → Out → Out) (x : StatementNode α) (o : Out) : Out :=
  let e := emitExpression ea
  let s := emitStatement ea
  match x with
  | .skip => o ++ "(AilSskip)"
  | .expr a => o |> open_ "AilSexpr" |> arg (e a) |> close
  | .block bs ss => o |> open_ "AilSblock" |> arg (emitBindings bs) |> arg (emitList s ss) |> close
  | .if_ c a b => o |> open_ "AilSif" |> arg (e c) |> arg (s a) |> arg (s b) |> close
  | .while_ c b n => o |> open_ "AilSwhile" |> arg (e c) |> arg (s b) |> arg (emitNat n) |> close
  | .do_ b c n => o |> open_ "AilSdo" |> arg (s b) |> arg (e c) |> arg (emitNat n) |> close
  | .break_ => o ++ "(AilSbreak)"
  | .continue_ => o ++ "(AilScontinue)"
  | .returnVoid => o ++ "(AilSreturnVoid)"
  | .return_ a => o |> open_ "AilSreturn" |> arg (e a) |> close
  | .switch a b => o |> open_ "AilSswitch" |> arg (e a) |> arg (s b) |> close
  | .case_ v b => o |> open_ "AilScase" |> arg (emitInt v) |> arg (s b) |> close
  | .caseRangeGnu lo hi b => o |> open_ "AilScase_rangeGNU" |> arg (emitInt lo) |> arg (emitInt hi)
      |> arg (s b) |> close
  | .default b => o |> open_ "AilSdefault" |> arg (s b) |> close
  | .label l b a => o |> open_ "AilSlabel" |> arg (emitSym l) |> arg (s b)
      |> arg (emitOption emitLabelAnnot a) |> close
  | .goto l => o |> open_ "AilSgoto" |> arg (emitSym l) |> close
  | .declaration ds => o |> open_ "AilSdeclaration"
      |> arg (emitList (emitTuple2 emitSym (emitOption e)) ds) |> close
  | .par ss => o |> open_ "AilSpar" |> arg (emitList s ss) |> close
  | .regStore r a => o |> open_ "AilSreg_store" |> arg (emitNat r) |> arg (e a) |> close
  | .marker n b => o |> open_ "AilSmarker" |> arg (emitNat n) |> arg (s b) |> close

partial def emitStatement (ea : α → Out → Out) (x : Statement α) (o : Out) : Out :=
  match x with
  | .mk l d as n => o |> open_ "statement" |> arg (emitLoc l) |> arg (emitDesugInfo d)
      |> arg (emitAttributes as) |> arg (emitStatementNode ea n) |> close

end

mutual

partial def decodeExpressionNode (da : Sx → Except String α) : Sx → Except String (ExpressionNode α)
  | .node "AilEunary" #[op, a] =>
    return .unary (← decodeUnaryOperator op) (← decodeExpression da a)
  | .node "AilEbinary" #[a, op, b] =>
    return .binary (← decodeExpression da a) (← decodeBinaryOperator op) (← decodeExpression da b)
  | .node "AilEassign" #[a, b] => return .assign (← decodeExpression da a) (← decodeExpression da b)
  | .node "AilEcompoundAssign" #[a, op, b] =>
    return .compoundAssign (← decodeExpression da a) (← decodeArithmeticOperator op)
      (← decodeExpression da b)
  | .node "AilEcond" #[c, a, b] =>
    return .cond (← decodeExpression da c) (← decodeOption (decodeExpression da) a)
      (← decodeExpression da b)
  | .node "AilEcast" #[q, t, a] =>
    return .cast (← decodeQualifiers q) (← decodeCtype t) (← decodeExpression da a)
  | .node "AilEcall" #[f, args] =>
    return .call (← decodeExpression da f) (← decodeList (decodeExpression da) args)
  | .node "AilEassert" #[a] => return .assert (← decodeExpression da a)
  | .node "AilEoffsetof" #[t, m] => return .offsetof (← decodeCtype t) (← decodeIdentifier m)
  | .node "AilEgeneric" #[a, n, gas] =>
    return .generic (← decodeExpression da a) (← decodeOption decodeNat n)
      (← decodeList (decodeGenericAssociation da) gas)
  | .node "AilEarray" #[b, t, xs] =>
    return .array (← decodeBool b) (← decodeCtype t)
      (← decodeList (decodeOption (decodeExpression da)) xs)
  | .node "AilEstruct" #[s, ms] =>
    return .struct (← decodeSym s)
      (← decodeList (decodeTuple2 decodeIdentifier (decodeOption (decodeExpression da))) ms)
  | .node "AilEunion" #[s, m, v] =>
    return .union (← decodeSym s) (← decodeIdentifier m) (← decodeOption (decodeExpression da) v)
  | .node "AilEcompound" #[q, t, a] =>
    return .compound (← decodeQualifiers q) (← decodeCtype t) (← decodeExpression da a)
  | .node "AilEmemberof" #[a, m] => return .memberof (← decodeExpression da a) (← decodeIdentifier m)
  | .node "AilEmemberofptr" #[a, m] =>
    return .memberofptr (← decodeExpression da a) (← decodeIdentifier m)
  | .node "AilEbuiltin" #[b] => return .builtin (← decodeBuiltin b)
  | .node "AilEstr" #[s] => return .str (← decodeStringLiteral s)
  | .node "AilEconst" #[c] => return .const (← decodeConstant c)
  | .node "AilEident" #[x] => return .ident (← decodeSym x)
  | .node "AilEsizeof" #[q, t] => return .sizeof (← decodeQualifiers q) (← decodeCtype t)
  | .node "AilEsizeof_expr" #[a] => return .sizeofExpr (← decodeExpression da a)
  | .node "AilEalignof" #[q, t] => return .alignof (← decodeQualifiers q) (← decodeCtype t)
  | .node "AilEannot" #[t, a] => return .annot (← decodeCtype t) (← decodeExpression da a)
  | .node "AilEva_start" #[a, x] => return .vaStart (← decodeExpression da a) (← decodeSym x)
  | .node "AilEva_arg" #[a, t] => return .vaArg (← decodeExpression da a) (← decodeCtype t)
  | .node "AilEva_copy" #[a, b] => return .vaCopy (← decodeExpression da a) (← decodeExpression da b)
  | .node "AilEva_end" #[a] => return .vaEnd (← decodeExpression da a)
  | .node "AilEprint_type" #[a] => return .printType (← decodeExpression da a)
  | .node "AilEbmc_assume" #[a] => return .bmcAssume (← decodeExpression da a)
  | .node "AilEreg_load" #[r] => return .regLoad (← decodeNat r)
  | .node "AilErvalue" #[a] => return .rvalue (← decodeExpression da a)
  | .node "AilEarray_decay" #[a] => return .arrayDecay (← decodeExpression da a)
  | .node "AilEfunction_decay" #[a] => return .functionDecay (← decodeExpression da a)
  | .node "AilEatomic" #[a] => return .atomic (← decodeExpression da a)
  | .node "AilElabel_addressGNU" #[l] => return .labelAddressGnu (← decodeSym l)
  | .node "AilEgcc_statement" #[bs, ss] =>
    return .gccStatement (← decodeBindings bs) (← decodeList (decodeStatement da) ss)
  | .node "AilEinvalid" #[t, r] => return .invalid (← decodeCtype t) (← decodeInvalidReason r)
  | t => mismatch "AilSyntax.expression_" t

partial def decodeGenericAssociation (da : Sx → Except String α) :
    Sx → Except String (GenericAssociation α)
  | .node "AilGAtype" #[q, t, a] =>
    return .type_ (← decodeQualifiers q) (← decodeCtype t) (← decodeExpression da a)
  | .node "AilGAdefault" #[a] => return .default (← decodeExpression da a)
  | t => mismatch "AilSyntax.generic_association" t

partial def decodeExpression (da : Sx → Except String α) : Sx → Except String (Expression α)
  | .node "AnnotatedExpression" #[a, as, l, n] =>
    return .mk (← da a) (← decodeList decodeAnnot as) (← decodeLoc l) (← decodeExpressionNode da n)
  | t => mismatch "AilSyntax.expression" t

partial def decodeStatementNode (da : Sx → Except String α) : Sx → Except String (StatementNode α)
  | .node "AilSskip" #[] => return .skip
  | .node "AilSexpr" #[a] => return .expr (← decodeExpression da a)
  | .node "AilSblock" #[bs, ss] =>
    return .block (← decodeBindings bs) (← decodeList (decodeStatement da) ss)
  | .node "AilSif" #[c, a, b] =>
    return .if_ (← decodeExpression da c) (← decodeStatement da a) (← decodeStatement da b)
  | .node "AilSwhile" #[c, b, n] =>
    return .while_ (← decodeExpression da c) (← decodeStatement da b) (← decodeNat n)
  | .node "AilSdo" #[b, c, n] =>
    return .do_ (← decodeStatement da b) (← decodeExpression da c) (← decodeNat n)
  | .node "AilSbreak" #[] => return .break_
  | .node "AilScontinue" #[] => return .continue_
  | .node "AilSreturnVoid" #[] => return .returnVoid
  | .node "AilSreturn" #[a] => return .return_ (← decodeExpression da a)
  | .node "AilSswitch" #[a, b] => return .switch (← decodeExpression da a) (← decodeStatement da b)
  | .node "AilScase" #[v, b] => return .case_ (← decodeInt v) (← decodeStatement da b)
  | .node "AilScase_rangeGNU" #[lo, hi, b] =>
    return .caseRangeGnu (← decodeInt lo) (← decodeInt hi) (← decodeStatement da b)
  | .node "AilSdefault" #[b] => return .default (← decodeStatement da b)
  | .node "AilSlabel" #[l, b, a] =>
    return .label (← decodeSym l) (← decodeStatement da b) (← decodeOption decodeLabelAnnot a)
  | .node "AilSgoto" #[l] => return .goto (← decodeSym l)
  | .node "AilSdeclaration" #[ds] =>
    return .declaration (← decodeList (decodeTuple2 decodeSym (decodeOption (decodeExpression da))) ds)
  | .node "AilSpar" #[ss] => return .par (← decodeList (decodeStatement da) ss)
  | .node "AilSreg_store" #[r, a] => return .regStore (← decodeNat r) (← decodeExpression da a)
  | .node "AilSmarker" #[n, b] => return .marker (← decodeNat n) (← decodeStatement da b)
  | t => mismatch "AilSyntax.statement_" t

partial def decodeStatement (da : Sx → Except String α) : Sx → Except String (Statement α)
  | .node "statement" #[l, d, as, n] =>
    return .mk (← decodeLoc l) (← decodeDesugInfo d) (← decodeAttributes as)
      (← decodeStatementNode da n)
  | t => mismatch "AilSyntax.statement" t

end

end Trees

/-! ## Programs -/

def emitDeclaration (x : Declaration) (o : Out) : Out :=
  match x with
  | .object s a q t => o |> open_ "Decl_object" |> arg (emitTuple2 emitStorageDuration emitBool s)
      |> arg (emitOption emitAlignment a) |> arg (emitQualifiers q) |> arg (emitCtype t) |> close
  | .function p r ps v i n => o |> open_ "Decl_function" |> arg (emitBool p)
      |> arg (emitTuple2 emitQualifiers emitCtype r) |> arg (emitList emitParam ps)
      |> arg (emitBool v) |> arg (emitBool i) |> arg (emitBool n) |> close

def decodeDeclaration : Sx → Except String Declaration
  | .node "Decl_object" #[s, a, q, t] =>
    return .object (← decodeTuple2 decodeStorageDuration decodeBool s)
      (← decodeOption decodeAlignment a) (← decodeQualifiers q) (← decodeCtype t)
  | .node "Decl_function" #[p, r, ps, v, i, n] =>
    return .function (← decodeBool p) (← decodeTuple2 decodeQualifiers decodeCtype r)
      (← decodeList decodeParam ps) (← decodeBool v) (← decodeBool i) (← decodeBool n)
  | t => mismatch "AilSyntax.declaration" t

def emitIdKind (x : IdKind) (o : Out) : Out :=
  o ++ match x with
  | .declaration => "(IK_declaration)" | .tentative => "(IK_tentative)"
  | .definition => "(IK_definition)"

def decodeIdKind : Sx → Except String IdKind
  | .node "IK_declaration" #[] => return .declaration
  | .node "IK_tentative" #[] => return .tentative
  | .node "IK_definition" #[] => return .definition
  | t => mismatch "AilSyntax.id_kind" t

def emitCnNamespace (x : CnNamespace) (o : Out) : Out :=
  o ++ match x with
  | .predicate => "(CN_predicate)" | .function => "(CN_function)" | .lemma => "(CN_lemma)"
  | .funSpec => "(CN_fun_spec)" | .datatype => "(CN_datatype_nm)"
  | .constructor => "(CN_constructor)" | .vars => "(CN_vars)" | .oarg => "(CN_oarg)"
  | .typeName => "(CN_type_nm)"

def decodeCnNamespace : Sx → Except String CnNamespace
  | .node "CN_predicate" #[] => return .predicate
  | .node "CN_function" #[] => return .function
  | .node "CN_lemma" #[] => return .lemma
  | .node "CN_fun_spec" #[] => return .funSpec
  | .node "CN_datatype_nm" #[] => return .datatype
  | .node "CN_constructor" #[] => return .constructor
  | .node "CN_vars" #[] => return .vars
  | .node "CN_oarg" #[] => return .oarg
  | .node "CN_type_nm" #[] => return .typeName
  | t => mismatch "Cn.cn_namespace" t

/-- `sigma_declaration` and `sigma_tag_definition`: `(sym * (Loc.t * attributes * x))`, the
inner triple flat. -/
def emitSigmaEntry {β : Type} (eb : β → Out → Out) (x : Sym × (Loc × Attributes × β)) (o : Out) :
    Out :=
  emitTuple2 emitSym (emitTuple3 emitLoc emitAttributes eb) x o

def decodeSigmaEntry {β : Type} (db : Sx → Except String β) :
    Sx → Except String (Sym × (Loc × Attributes × β)) :=
  decodeTuple2 decodeSym (decodeTuple3 decodeLoc decodeAttributes db)

section Programs

variable {α : Type}

/-- `sigma_function_definition`: `(sym * (Loc.t * nat * attributes * list sym * statement))`. -/
def emitFunctionDefinition (ea : α → Out → Out) (x : Sym × FunctionDefinition α) (o : Out) : Out :=
  let (s, ⟨l, m, as, ps, b⟩) := x
  o |> open_ "$tuple" |> arg (emitSym s)
    |> arg (fun o => o |> open_ "$tuple" |> arg (emitLoc l) |> arg (emitNat m)
      |> arg (emitAttributes as) |> arg (emitList emitSym ps) |> arg (emitStatement ea b) |> close)
    |> close

def decodeFunctionDefinition (da : Sx → Except String α) :
    Sx → Except String (Sym × FunctionDefinition α)
  | .node "$tuple" #[s, .node "$tuple" #[l, m, as, ps, b]] =>
    return (← decodeSym s, ⟨← decodeLoc l, ← decodeNat m, ← decodeAttributes as,
      ← decodeList decodeSym ps, ← decodeStatement da b⟩)
  | t => mismatch "AilSyntax.sigma_function_definition" t

def emitSigma (ea : α → Out → Out) (x : Sigma α) (o : Out) : Out :=
  o |> open_ "sigma"
    |> arg (emitList (emitSigmaEntry emitDeclaration) x.declarations)
    |> arg (emitList (emitTuple2 emitSym (emitExpression ea)) x.objectDefinitions)
    |> arg (emitList (emitFunctionDefinition ea) x.functionDefinitions)
    |> arg (emitList (emitTuple2 (emitExpression ea) emitStringLiteral) x.staticAssertions)
    |> arg (emitList (emitSigmaEntry emitTagDefinition) x.tagDefinitions)
    |> arg (emitMap emitIdentifier (emitTuple2 emitSym emitIdKind) x.externIdmap)
    |> arg (emitMap emitSym emitAttributes x.typedefAttributes)
    |> arg (emitMap emitNat emitLoopAttribute x.loopAttributes)
    |> arg (emitList (emitCnFunction emitSym emitCtype) x.cnFunctions)
    |> arg (emitList (emitCnLemma emitSym emitCtype) x.cnLemmata)
    |> arg (emitList (emitCnPredicate emitSym emitCtype) x.cnPredicates)
    |> arg (emitList (emitCnDatatype emitSym) x.cnDatatypes)
    |> arg (emitList (emitTuple3 emitNat emitSym (emitCnDeclSpec emitIdentifier emitTypeName))
      x.cnDeclSpecs)
    |> arg (emitMap (emitTuple2 emitCnNamespace emitIdentifier) emitSym x.cnIdents)
    |> close

def decodeSigma (da : Sx → Except String α) : Sx → Except String (Sigma α)
  | .node "sigma" #[ds, ods, fds, sas, tds, eim, tas, las, cfs, cls, cps, cdts, cdss, cis] =>
    return {
      declarations := ← decodeList (decodeSigmaEntry decodeDeclaration) ds
      objectDefinitions := ← decodeList (decodeTuple2 decodeSym (decodeExpression da)) ods
      functionDefinitions := ← decodeList (decodeFunctionDefinition da) fds
      staticAssertions := ← decodeList (decodeTuple2 (decodeExpression da) decodeStringLiteral) sas
      tagDefinitions := ← decodeList (decodeSigmaEntry decodeTagDefinition) tds
      externIdmap := ← decodeMap decodeIdentifier (decodeTuple2 decodeSym decodeIdKind) eim
      typedefAttributes := ← decodeMap decodeSym decodeAttributes tas
      loopAttributes := ← decodeMap decodeNat decodeLoopAttribute las
      cnFunctions := ← decodeList (decodeCnFunction decodeSym decodeCtype) cfs
      cnLemmata := ← decodeList (decodeCnLemma decodeSym decodeCtype) cls
      cnPredicates := ← decodeList (decodeCnPredicate decodeSym decodeCtype) cps
      cnDatatypes := ← decodeList (decodeCnDatatype decodeSym) cdts
      cnDeclSpecs := ← decodeList (decodeTuple3 decodeNat decodeSym
        (decodeCnDeclSpec decodeIdentifier decodeTypeName)) cdss
      cnIdents := ← decodeMap (decodeTuple2 decodeCnNamespace decodeIdentifier) decodeSym cis }
  | t => mismatch "AilSyntax.sigma" t

/-- `ail_program`: `($tuple <maybe startup> <sigma>)`. -/
def emitProgram (ea : α → Out → Out) (x : Program α) (o : Out) : Out :=
  emitTuple2 (emitOption emitSym) (emitSigma ea) x o

def decodeProgram (da : Sx → Except String α) : Sx → Except String (Program α) :=
  decodeTuple2 (decodeOption decodeSym) (decodeSigma da)

end Programs

/-! ## Documents and rejects -/

/-- A source position `($str file) line column`, as the parts of a `Loc_regions` print it. -/
structure Position where
  file : String
  line : Int
  column : Int
  deriving DecidableEq, Repr

/-- The cursor of a `Loc_regions`. -/
inductive Cursor where
  | none
  | point (p : Position)
  | region (a b : Position)
  deriving DecidableEq, Repr

/-- The location of a reject: a `Loc.t`, or the `$loc_regions` extension of the Silmaril exporter
(`Cerb_location.Loc_regions`, which some typing errors report: operand regions and a cursor). -/
inductive RejectLoc where
  | loc (l : Loc)
  | regions (regions : List (Position × Position)) (cursor : Cursor)
  deriving Repr

/-- `($str file) line col`, three children of the enclosing node. -/
def emitPositionParts (p : Position) (o : Out) : Out :=
  o |> arg (emitStr p.file) |> arg (emitInt p.line) |> arg (emitInt p.column)

def decodePosition (f l c : Sx) : Except String Position :=
  return ⟨← decodeStr f, ← decodeInt l, ← decodeInt c⟩

def emitRejectLoc (x : RejectLoc) (o : Out) : Out :=
  match x with
  | .loc l => emitLoc l o
  | .regions rs c =>
    let region (r : Position × Position) (o : Out) : Out :=
      o |> open_ "$tuple" |> emitPositionParts r.1 |> emitPositionParts r.2 |> close
    let cursor (o : Out) : Out := match c with
      | .none => o ++ "($none)"
      | .point p => o |> open_ "$some" |> arg (fun o => o |> open_ "$tuple" |> emitPositionParts p
          |> close) |> close
      | .region a b => o |> open_ "$some" |> arg (fun o => o |> open_ "$tuple"
          |> emitPositionParts a |> emitPositionParts b |> close) |> close
    o |> open_ "$loc_regions" |> arg (emitList region rs) |> arg cursor |> close

def decodeRejectLoc : Sx → Except String RejectLoc
  | .node "$loc_regions" #[rs, c] => do
    let region : Sx → Except String (Position × Position)
      | .node "$tuple" #[f, l, c, f', l', c'] =>
        return (← decodePosition f l c, ← decodePosition f' l' c')
      | t => mismatch "a region" t
    let cursor ← match c with
      | .node "$none" #[] => pure Cursor.none
      | .node "$some" #[.node "$tuple" #[f, l, c]] => Cursor.point <$> decodePosition f l c
      | .node "$some" #[.node "$tuple" #[f, l, c, f', l', c']] =>
        pure (Cursor.region (← decodePosition f l c) (← decodePosition f' l' c'))
      | t => mismatch "a cursor" t
    return .regions (← decodeList region rs) cursor
  | t => return .loc (← decodeLoc t)

/-- One oracle output at the typed-Ail level: a program, or the reject that stopped Cerberus
(stage `cpp`, `parse`, `desugar` or `typing`), with the Cerberus commit and the implementation
name of the header. -/
inductive TailOutput where
  | document (commit impl : String) (prog : TypedProgram)
  | reject (commit impl stage : String) (loc : RejectLoc) (msg : String)

def emitReject (commit impl stage : String) (loc : RejectLoc) (msg : String) (o : Out) : Out :=
  o |> open_ "$reject" |> arg (emitInt 1) |> arg (emitStr commit) |> arg (emitStr impl)
    |> arg (emitStr stage) |> arg (emitRejectLoc loc) |> arg (emitStr msg) |> close

def emitTailOutput (x : TailOutput) (o : Out) : Out :=
  match x with
  | .document commit impl prog =>
    o |> open_ "$document_tail" |> arg (emitInt 1) |> arg (emitStr commit) |> arg (emitStr impl)
      |> arg (emitProgram emitGenTypeCategory prog) |> close
  | .reject commit impl stage loc msg => emitReject commit impl stage loc msg o

def decodeTailOutput : Sx → Except String TailOutput
  | .node "$document_tail" #[.atom "1", commit, impl, prog] =>
    return .document (← decodeStr commit) (← decodeStr impl)
      (← decodeProgram decodeGenTypeCategory prog)
  | .node "$reject" #[.atom "1", commit, impl, stage, l, msg] =>
    return .reject (← decodeStr commit) (← decodeStr impl) (← decodeStr stage) (← decodeRejectLoc l)
      (← decodeStr msg)
  | t => mismatch "a version 1 $document_tail or $reject" t

/-- The canonical text of a typed-Ail output, with its final newline. -/
def printTailDocument (x : TailOutput) : String := (emitTailOutput x "").push '\n'

/-- Decode a typed-Ail output without checking its layout. -/
def readTailDocument (text : String) : Except String TailOutput := do
  decodeTailOutput (← read text.toByteArray)

/-- Decode a typed-Ail output and check that printing it gives back exactly `text`. -/
def parseTailDocument (text : String) : Except String TailOutput := do
  let x ← readTailDocument text
  if printTailDocument x == text then return x else throw "noncanonical document"

/-- One oracle output at the untyped-Ail level (`--level ail`). -/
inductive AilOutput where
  | document (commit impl : String) (prog : Program Unit)
  | reject (commit impl stage : String) (loc : RejectLoc) (msg : String)

def emitAilOutput (x : AilOutput) (o : Out) : Out :=
  match x with
  | .document commit impl prog =>
    o |> open_ "$document_ail" |> arg (emitInt 1) |> arg (emitStr commit) |> arg (emitStr impl)
      |> arg (emitProgram emitUnit prog) |> close
  | .reject commit impl stage loc msg => emitReject commit impl stage loc msg o

def decodeAilOutput : Sx → Except String AilOutput
  | .node "$document_ail" #[.atom "1", commit, impl, prog] =>
    return .document (← decodeStr commit) (← decodeStr impl) (← decodeProgram decodeUnit prog)
  | .node "$reject" #[.atom "1", commit, impl, stage, l, msg] =>
    return .reject (← decodeStr commit) (← decodeStr impl) (← decodeStr stage) (← decodeRejectLoc l)
      (← decodeStr msg)
  | t => mismatch "a version 1 $document_ail or $reject" t

/-- The canonical text of an untyped-Ail output, with its final newline. -/
def printAilDocument (x : AilOutput) : String := (emitAilOutput x "").push '\n'

/-- Decode an untyped-Ail output without checking its layout. -/
def readAilDocument (text : String) : Except String AilOutput := do
  decodeAilOutput (← read text.toByteArray)

end Silmaril.Cerberus.Ail.Codec
