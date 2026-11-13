module

public import Silmaril.Cerberus.Core.Syntax.Defs
public import Silmaril.Cerberus.Codec.Mem.Defs
public import Silmaril.Cerberus.Codec.Undefined.Defs

/-! # Wire codecs for Core values, patterns and pure expressions

Codecs for the untyped pure expressions that Cerberus exports, `Pexpr` over
`wireModel`, and for everything they reach. Six families are recursive, each
with a `Layer`: object types, base types, memory constraints, values (with
object and loaded values nested inside), patterns and pure expressions.

Nested encoders recurse through `List.map` and products using well-founded
recursion; `codec_decreasing` proves the size inequalities. Their codec
obligations rewrite the resulting equation lemmas. Each layer proves that it
consumes a tag before its recursive slots. Total helper codecs expose `_budget`
lemmas so the guard proof can reduce the depth arithmetic.

`PexprNode` contains the abstract `M.IntegerValue`. Its derived size uses
`instSizeOfDefault`, even when this wire model instantiates it with `Int`.
The local `SizeOf Int` instance below matches that derived size. It affects only
termination proofs, not integer encoding or decoding.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec
open Core

abbrev M := wireModel

def encodeImplementationConstant : ImplementationConstant → Tree
  | .environmentStartupName => node (tag% ImplementationConstant.environmentStartupName) []
  | .environmentStartupType => node (tag% ImplementationConstant.environmentStartupType) []
  | .charactersBitsInByte => node (tag% ImplementationConstant.charactersBitsInByte) []
  | .charactersExecutionCharacterSetValues => node (tag% ImplementationConstant.charactersExecutionCharacterSetValues) []
  | .charactersTodo1 => node (tag% ImplementationConstant.charactersTodo1) []
  | .charactersTodo2 => node (tag% ImplementationConstant.charactersTodo2) []
  | .charactersPlainCharIsSigned => node (tag% ImplementationConstant.charactersPlainCharIsSigned) []
  | .charactersTodo3 => node (tag% ImplementationConstant.charactersTodo3) []
  | .charactersTodo4 => node (tag% ImplementationConstant.charactersTodo4) []
  | .charactersTodo5 => node (tag% ImplementationConstant.charactersTodo5) []
  | .charactersTodo6 => node (tag% ImplementationConstant.charactersTodo6) []
  | .charactersTodo7 => node (tag% ImplementationConstant.charactersTodo7) []
  | .charactersTodo8 => node (tag% ImplementationConstant.charactersTodo8) []
  | .charactersTodo9 => node (tag% ImplementationConstant.charactersTodo9) []
  | .charactersTodo10 => node (tag% ImplementationConstant.charactersTodo10) []
  | .integerEncode => node (tag% ImplementationConstant.integerEncode) []
  | .integerDecode => node (tag% ImplementationConstant.integerDecode) []
  | .integerConvNonrepresentableSignedInteger => node (tag% ImplementationConstant.integerConvNonrepresentableSignedInteger) []
  | .sizeof => node (tag% ImplementationConstant.sizeof) []
  | .alignof => node (tag% ImplementationConstant.alignof) []
  | .shrSignedNegative => node (tag% ImplementationConstant.shrSignedNegative) []
  | .bitwiseComplement => node (tag% ImplementationConstant.bitwiseComplement) []
  | .plainBitfieldSign => node (tag% ImplementationConstant.plainBitfieldSign) []
  | .bitfieldOtherTypes => node (tag% ImplementationConstant.bitfieldOtherTypes) []
  | .atomicBitfieldPermitted => node (tag% ImplementationConstant.atomicBitfieldPermitted) []
  | .ctypeMin => node (tag% ImplementationConstant.ctypeMin) []
  | .ctypeMax => node (tag% ImplementationConstant.ctypeMax) []
  | .builtinFunction s => node (tag% ImplementationConstant.builtinFunction) [str.enc s]

def implementationConstant : Codec ImplementationConstant := ofLeaves encodeImplementationConstant
  [leafPair% ImplementationConstant.environmentStartupName,
   leafPair% ImplementationConstant.environmentStartupType,
   leafPair% ImplementationConstant.charactersBitsInByte,
   leafPair% ImplementationConstant.charactersExecutionCharacterSetValues,
   leafPair% ImplementationConstant.charactersTodo1,
   leafPair% ImplementationConstant.charactersTodo2,
   leafPair% ImplementationConstant.charactersPlainCharIsSigned,
   leafPair% ImplementationConstant.charactersTodo3,
   leafPair% ImplementationConstant.charactersTodo4,
   leafPair% ImplementationConstant.charactersTodo5,
   leafPair% ImplementationConstant.charactersTodo6,
   leafPair% ImplementationConstant.charactersTodo7,
   leafPair% ImplementationConstant.charactersTodo8,
   leafPair% ImplementationConstant.charactersTodo9,
   leafPair% ImplementationConstant.charactersTodo10,
   leafPair% ImplementationConstant.integerEncode,
   leafPair% ImplementationConstant.integerDecode,
   leafPair% ImplementationConstant.integerConvNonrepresentableSignedInteger,
   leafPair% ImplementationConstant.sizeof,
   leafPair% ImplementationConstant.alignof,
   leafPair% ImplementationConstant.shrSignedNegative,
   leafPair% ImplementationConstant.bitwiseComplement,
   leafPair% ImplementationConstant.plainBitfieldSign,
   leafPair% ImplementationConstant.bitfieldOtherTypes,
   leafPair% ImplementationConstant.atomicBitfieldPermitted,
   leafPair% ImplementationConstant.ctypeMin,
   leafPair% ImplementationConstant.ctypeMax]
  [alt% ImplementationConstant.builtinFunction str]
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

@[simp] theorem implementationConstant_budget : implementationConstant.budget = none := by
  simp [implementationConstant]

/-! ## Base types -/

def encodeCoreObjectType : ObjectType → Tree
  | .integer => node (tag% Core.ObjectType.integer) []
  | .floating => node (tag% Core.ObjectType.floating) []
  | .pointer => node (tag% Core.ObjectType.pointer) []
  | .array t => node (tag% Core.ObjectType.array) [encodeCoreObjectType t]
  | .struct s => node (tag% Core.ObjectType.struct) [sym.enc s]
  | .union s => node (tag% Core.ObjectType.union) [sym.enc s]

def objectTypeLayer : Layer ObjectType encodeCoreObjectType where
  build c h := ofAlts encodeCoreObjectType
    [leaf% Core.ObjectType.integer,
     leaf% Core.ObjectType.floating,
     leaf% Core.ObjectType.pointer,
     alt% Core.ObjectType.array (slot c encodeCoreObjectType h),
     alt% Core.ObjectType.struct sym,
     alt% Core.ObjectType.union sym]
    (by codec_nodup) (by codec_enc) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [hk]; omega

def objectType : Codec ObjectType := fix encodeCoreObjectType objectTypeLayer

def encodeCoreBaseType : BaseType → Tree
  | .unit => node (tag% Core.BaseType.unit) []
  | .boolean => node (tag% Core.BaseType.boolean) []
  | .ctype => node (tag% Core.BaseType.ctype) []
  | .list t => node (tag% Core.BaseType.list) [encodeCoreBaseType t]
  | .tuple ts => node (tag% Core.BaseType.tuple) [node "$list" (ts.map encodeCoreBaseType)]
  | .object t => node (tag% Core.BaseType.object) [objectType.enc t]
  | .loaded t => node (tag% Core.BaseType.loaded) [objectType.enc t]
  | .storable => node (tag% Core.BaseType.storable) []
decreasing_by codec_decreasing

def baseTypeLayer : Layer BaseType encodeCoreBaseType where
  build c h :=
    let t := slot c encodeCoreBaseType h
    ofAlts encodeCoreBaseType
    [leaf% Core.BaseType.unit,
     leaf% Core.BaseType.boolean,
     leaf% Core.BaseType.ctype,
     alt% Core.BaseType.list t,
     alt% Core.BaseType.tuple (list t),
     alt% Core.BaseType.object objectType,
     alt% Core.BaseType.loaded objectType,
     leaf% Core.BaseType.storable]
    (by codec_nodup) (by codec_enc [encodeCoreBaseType]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [hk, objectType]; omega

def baseType : Codec BaseType := fix encodeCoreBaseType baseTypeLayer

/-! ## Operators and constructors -/

def encodeBinop : BinOp → Tree
  | .add => node (tag% Core.BinOp.add) []
  | .sub => node (tag% Core.BinOp.sub) []
  | .mul => node (tag% Core.BinOp.mul) []
  | .div => node (tag% Core.BinOp.div) []
  | .remT => node (tag% Core.BinOp.remT) []
  | .remF => node (tag% Core.BinOp.remF) []
  | .exp => node (tag% Core.BinOp.exp) []
  | .eq => node (tag% Core.BinOp.eq) []
  | .gt => node (tag% Core.BinOp.gt) []
  | .lt => node (tag% Core.BinOp.lt) []
  | .ge => node (tag% Core.BinOp.ge) []
  | .le => node (tag% Core.BinOp.le) []
  | .and => node (tag% Core.BinOp.and) []
  | .or => node (tag% Core.BinOp.or) []

def binOp : Codec BinOp := ofLeaves encodeBinop
  [leafPair% Core.BinOp.add, leafPair% Core.BinOp.sub, leafPair% Core.BinOp.mul, leafPair% Core.BinOp.div,
   leafPair% Core.BinOp.remT, leafPair% Core.BinOp.remF, leafPair% Core.BinOp.exp, leafPair% Core.BinOp.eq,
   leafPair% Core.BinOp.gt, leafPair% Core.BinOp.lt, leafPair% Core.BinOp.ge, leafPair% Core.BinOp.le, leafPair% Core.BinOp.and,
   leafPair% Core.BinOp.or] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeIop : IntOp → Tree
  | .add => node (tag% Core.IntOp.add) []
  | .sub => node (tag% Core.IntOp.sub) []
  | .mul => node (tag% Core.IntOp.mul) []
  | .shl => node (tag% Core.IntOp.shl) []
  | .shr => node (tag% Core.IntOp.shr) []
  | .div => node (tag% Core.IntOp.div) []
  | .remT => node (tag% Core.IntOp.remT) []

def intOp : Codec IntOp := ofLeaves encodeIop
  [leafPair% Core.IntOp.add, leafPair% Core.IntOp.sub, leafPair% Core.IntOp.mul, leafPair% Core.IntOp.shl,
   leafPair% Core.IntOp.shr, leafPair% Core.IntOp.div, leafPair% Core.IntOp.remT] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeCtor : Ctor → Tree
  | .nil t => node (tag% Core.Ctor.nil) [baseType.enc t]
  | .cons => node (tag% Core.Ctor.cons) []
  | .tuple => node (tag% Core.Ctor.tuple) []
  | .array => node (tag% Core.Ctor.array) []
  | .ivMax => node (tag% Core.Ctor.ivMax) []
  | .ivMin => node (tag% Core.Ctor.ivMin) []
  | .ivSizeof => node (tag% Core.Ctor.ivSizeof) []
  | .ivAlignof => node (tag% Core.Ctor.ivAlignof) []
  | .ivCompl => node (tag% Core.Ctor.ivCompl) []
  | .ivAnd => node (tag% Core.Ctor.ivAnd) []
  | .ivOr => node (tag% Core.Ctor.ivOr) []
  | .ivXor => node (tag% Core.Ctor.ivXor) []
  | .specified => node (tag% Core.Ctor.specified) []
  | .unspecified => node (tag% Core.Ctor.unspecified) []
  | .fvFromInt => node (tag% Core.Ctor.fvFromInt) []
  | .ivFromFloat => node (tag% Core.Ctor.ivFromFloat) []
  | .ivNullCap b => node (tag% Core.Ctor.ivNullCap) [boolean.enc b]

def ctor : Codec Ctor := ofLeaves encodeCtor
  [leafPair% Core.Ctor.cons, leafPair% Core.Ctor.tuple, leafPair% Core.Ctor.array, leafPair% Core.Ctor.ivMax,
   leafPair% Core.Ctor.ivMin, leafPair% Core.Ctor.ivSizeof, leafPair% Core.Ctor.ivAlignof,
   leafPair% Core.Ctor.ivCompl, leafPair% Core.Ctor.ivAnd, leafPair% Core.Ctor.ivOr, leafPair% Core.Ctor.ivXor,
   leafPair% Core.Ctor.specified, leafPair% Core.Ctor.unspecified, leafPair% Core.Ctor.fvFromInt,
   leafPair% Core.Ctor.ivFromFloat]
  [alt% Core.Ctor.nil baseType, alt% Core.Ctor.ivNullCap boolean]
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeGenericName : Core.Name Sym → Tree
  | .sym s => node (tag% Core.Name.sym) [sym.enc s]
  | .impl i => node (tag% Core.Name.impl) [implementationConstant.enc i]

def name : Codec (Core.Name Sym) := ofAlts encodeGenericName
  [alt% Core.Name.sym sym, alt% Core.Name.impl implementationConstant]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeArithmeticOperator : ArithmeticOperator → Tree
  | .mul => node (tag% ArithmeticOperator.mul) []
  | .div => node (tag% ArithmeticOperator.div) []
  | .mod => node (tag% ArithmeticOperator.mod) []
  | .add => node (tag% ArithmeticOperator.add) []
  | .sub => node (tag% ArithmeticOperator.sub) []
  | .shl => node (tag% ArithmeticOperator.shl) []
  | .shr => node (tag% ArithmeticOperator.shr) []
  | .band => node (tag% ArithmeticOperator.band) []
  | .bxor => node (tag% ArithmeticOperator.bxor) []
  | .bor => node (tag% ArithmeticOperator.bor) []

def arithmeticOperator : Codec ArithmeticOperator := ofLeaves encodeArithmeticOperator
  [leafPair% ArithmeticOperator.mul, leafPair% ArithmeticOperator.div, leafPair% ArithmeticOperator.mod, leafPair% ArithmeticOperator.add, leafPair% ArithmeticOperator.sub, leafPair% ArithmeticOperator.shl,
   leafPair% ArithmeticOperator.shr, leafPair% ArithmeticOperator.band, leafPair% ArithmeticOperator.bxor, leafPair% ArithmeticOperator.bor] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeUnaryOperator : UnaryOperator → Tree
  | .plus => node (tag% UnaryOperator.plus) []
  | .minus => node (tag% UnaryOperator.minus) []
  | .bnot => node (tag% UnaryOperator.bnot) []
  | .address => node (tag% UnaryOperator.address) []
  | .indirection => node (tag% UnaryOperator.indirection) []
  | .postfixIncr => node (tag% UnaryOperator.postfixIncr) []
  | .postfixDecr => node (tag% UnaryOperator.postfixDecr) []

def unaryOperator : Codec UnaryOperator := ofLeaves encodeUnaryOperator
  [leafPair% UnaryOperator.plus, leafPair% UnaryOperator.minus, leafPair% UnaryOperator.bnot, leafPair% UnaryOperator.address,
   leafPair% UnaryOperator.indirection, leafPair% UnaryOperator.postfixIncr, leafPair% UnaryOperator.postfixDecr] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeBinaryOperator : BinaryOperator → Tree
  | .arithmetic o => node (tag% BinaryOperator.arithmetic) [arithmeticOperator.enc o]
  | .comma => node (tag% BinaryOperator.comma) []
  | .and => node (tag% BinaryOperator.and) []
  | .or => node (tag% BinaryOperator.or) []
  | .lt => node (tag% BinaryOperator.lt) []
  | .gt => node (tag% BinaryOperator.gt) []
  | .le => node (tag% BinaryOperator.le) []
  | .ge => node (tag% BinaryOperator.ge) []
  | .eq => node (tag% BinaryOperator.eq) []
  | .ne => node (tag% BinaryOperator.ne) []

def binaryOperator : Codec BinaryOperator := ofLeaves encodeBinaryOperator
  [leafPair% BinaryOperator.comma, leafPair% BinaryOperator.and, leafPair% BinaryOperator.or, leafPair% BinaryOperator.lt, leafPair% BinaryOperator.gt, leafPair% BinaryOperator.le,
   leafPair% BinaryOperator.ge, leafPair% BinaryOperator.eq, leafPair% BinaryOperator.ne]
  [alt% BinaryOperator.arithmetic arithmeticOperator]
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeDerivecapOp : DeriveCapOp → Tree
  | .unary o => node (tag% DeriveCapOp.unary) [unaryOperator.enc o]
  | .binary o => node (tag% DeriveCapOp.binary) [binaryOperator.enc o]

def deriveCapOp : Codec DeriveCapOp := ofAlts encodeDerivecapOp
  [alt% DeriveCapOp.unary unaryOperator, alt% DeriveCapOp.binary binaryOperator]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodePureMemop : PureMemOp → Tree
  | .deriveCap o b => node (tag% PureMemOp.deriveCap) [deriveCapOp.enc o, boolean.enc b]
  | .capAssignValue => node (tag% PureMemOp.capAssignValue) []
  | .ptrTIntValue => node (tag% PureMemOp.ptrTIntValue) []
  | .byteFromInt => node (tag% PureMemOp.byteFromInt) []
  | .intFromByte => node (tag% PureMemOp.intFromByte) []

def pureMemOp : Codec PureMemOp := ofAlts encodePureMemop
  [alt% PureMemOp.deriveCap (deriveCapOp ⊗ boolean),
   leaf% PureMemOp.capAssignValue,
   leaf% PureMemOp.ptrTIntValue,
   leaf% PureMemOp.byteFromInt,
   leaf% PureMemOp.intFromByte]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-! ## Memory constraints, generic in the constrained values -/

variable {a : Type} (ca : Codec a) in
def encodeMemConstraint : MemConstraint a → Tree
  | .empty => node (tag% MemConstraint.empty) []
  | .eq x y => node (tag% MemConstraint.eq) [ca.enc x, ca.enc y]
  | .le x y => node (tag% MemConstraint.le) [ca.enc x, ca.enc y]
  | .lt x y => node (tag% MemConstraint.lt) [ca.enc x, ca.enc y]
  | .inDevice x => node (tag% MemConstraint.inDevice) [ca.enc x]
  | .or x y => node (tag% MemConstraint.or) [encodeMemConstraint x, encodeMemConstraint y]
  | .conj xs => node (tag% MemConstraint.conj) [node "$list" (xs.map encodeMemConstraint)]
  | .not x => node (tag% MemConstraint.not) [encodeMemConstraint x]
decreasing_by codec_decreasing

def memConstraintLayer {a : Type} (ca : Codec a) (hca : ca.budget = none) :
    Layer (MemConstraint a) (encodeMemConstraint ca) where
  build c h :=
    let t := slot c (encodeMemConstraint ca) h
    ofAlts (encodeMemConstraint ca)
    [leaf% MemConstraint.empty,
     alt% MemConstraint.eq (ca ⊗ ca),
     alt% MemConstraint.le (ca ⊗ ca),
     alt% MemConstraint.lt (ca ⊗ ca),
     alt% MemConstraint.inDevice ca,
     alt% MemConstraint.or (t ⊗ t),
     alt% MemConstraint.conj (list t),
     alt% MemConstraint.not t]
    (by codec_nodup) (by codec_enc [encodeMemConstraint]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [hk, hca]; omega

def memConstraint {a : Type} (ca : Codec a) (hca : ca.budget = none) : Codec (MemConstraint a) :=
  fix (encodeMemConstraint ca) (memConstraintLayer ca hca)

/-! ## Values -/

mutual

def encodeObjectValue : ObjectValue M → Tree
  | .integer n => node (tag% Core.ObjectValue.integer) [integerValue.enc n]
  | .floating f => node (tag% Core.ObjectValue.floating) [floatingValue.enc f]
  | .pointer p => node (tag% Core.ObjectValue.pointer) [pointerValue.enc p]
  | .array vs => node (tag% Core.ObjectValue.array) [node "$list" (vs.map encodeLoadedValue)]
  | .struct s ms => node (tag% Core.ObjectValue.struct) [sym.enc s,
      (list (tuple (identifier ⊗ ctype ⊗ empty))).enc ms]
  | .union s i v => node (tag% Core.ObjectValue.union) [sym.enc s, identifier.enc i, empty.enc v]
decreasing_by codec_decreasing

def encodeLoadedValue : LoadedValue M → Tree
  | .specified v => node (tag% Core.LoadedValue.specified) [encodeObjectValue v]
  | .unspecified t => node (tag% Core.LoadedValue.unspecified) [ctype.enc t]

end

def loadedValue_ (c : Codec (ObjectValue M)) (h : c.enc = encodeObjectValue) :
    Codec (LoadedValue M) := ofAlts encodeLoadedValue
  [alt% Core.LoadedValue.specified (slot c encodeObjectValue h),
   alt% Core.LoadedValue.unspecified ctype]
  (by codec_nodup) (by codec_enc [encodeLoadedValue]) (by codec_cover)

def objectValueLayer : Layer (ObjectValue M) encodeObjectValue where
  build c h := ofAlts encodeObjectValue
    [alt% Core.ObjectValue.integer integerValue,
     alt% Core.ObjectValue.floating floatingValue,
     alt% Core.ObjectValue.pointer pointerValue,
     alt% Core.ObjectValue.array (list (loadedValue_ c h)),
     alt% Core.ObjectValue.struct (sym ⊗ list (tuple (identifier ⊗ ctype ⊗ empty))),
     alt% Core.ObjectValue.union (sym ⊗ identifier ⊗ empty)]
    (by codec_nodup) (by codec_enc [encodeObjectValue]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [loadedValue_, hk]; omega

def objectValue : Codec (ObjectValue M) := fix encodeObjectValue objectValueLayer

def loadedValue : Codec (LoadedValue M) :=
  (loadedValue_ objectValue rfl).weaken none fun _ _ => by
    simp [loadedValue_, objectValue]

def encodeValue : Value M → Tree
  | .object v => node (tag% Core.Value.object) [objectValue.enc v]
  | .loaded v => node (tag% Core.Value.loaded) [loadedValue.enc v]
  | .unit => node (tag% Core.Value.unit) []
  | .true => node (tag% Core.Value.true) []
  | .false => node (tag% Core.Value.false) []
  | .ctype t => node (tag% Core.Value.ctype) [ctype.enc t]
  | .list t vs => node (tag% Core.Value.list) [baseType.enc t, node "$list" (vs.map encodeValue)]
  | .tuple vs => node (tag% Core.Value.tuple) [node "$list" (vs.map encodeValue)]
decreasing_by codec_decreasing

def valueLayer : Layer (Value M) encodeValue where
  build c h :=
    let t := slot c encodeValue h
    ofAlts encodeValue
    [alt% Core.Value.object objectValue,
     alt% Core.Value.loaded loadedValue,
     leaf% Core.Value.unit,
     leaf% Core.Value.true,
     leaf% Core.Value.false,
     alt% Core.Value.ctype ctype,
     alt% Core.Value.list (baseType ⊗ list t),
     alt% Core.Value.tuple (list t)]
    (by codec_nodup) (by codec_enc [encodeValue]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [hk, objectValue, loadedValue, baseType]; omega

def value : Codec (Value M) := fix encodeValue valueLayer

/-! ## Patterns -/

mutual

def encodePattern : Core.Pattern Sym → Tree
  | .mk as p => node (tag% Core.Pattern.mk) [(list annot).enc as, encodePatternNode p]

def encodePatternNode : Core.PatternNode Sym → Tree
  | .base (s, t) => node (tag% Core.PatternNode.base) [node "$tuple" [(option sym).enc s, baseType.enc t]]
  | .ctor c ps => node (tag% Core.PatternNode.ctor) [ctor.enc c, node "$list" (ps.map encodePattern)]
decreasing_by codec_decreasing

end

def patternNode (c : Codec (Core.Pattern Sym)) (h : c.enc = encodePattern) :
    Codec (Core.PatternNode Sym) := ofAlts encodePatternNode
  [alt% Core.PatternNode.base (tuple (option sym ⊗ baseType)),
   alt% Core.PatternNode.ctor (ctor ⊗ list (slot c encodePattern h))]
  (by codec_nodup) (by codec_enc [encodePatternNode]) (by codec_cover)

def patternLayer : Layer (Core.Pattern Sym) encodePattern where
  build c h := ofAlts encodePattern
    [alt% Core.Pattern.mk (list annot ⊗ patternNode c h)]
    (by codec_nodup) (by codec_enc [encodePattern]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [patternNode, hk, baseType, ctor]; omega

def pattern : Codec (Core.Pattern Sym) := fix encodePattern patternLayer

@[simp] theorem baseType_budget : baseType.budget = none := rfl
@[simp] theorem value_budget : value.budget = none := rfl
@[simp] theorem pattern_budget : pattern.budget = none := rfl
@[simp] theorem binOp_budget : binOp.budget = none := by simp [binOp]
@[simp] theorem intOp_budget : intOp.budget = none := by simp [intOp]
@[simp] theorem ctor_budget : ctor.budget = none := by simp [ctor]
@[simp] theorem name_budget : name.budget = none := by simp [name]
@[simp] theorem pureMemOp_budget : pureMemOp.budget = none := rfl

/-! ## Pure expressions -/

abbrev Pexpr := Core.Pexpr M Unit Sym
abbrev PexprNode := Core.PexprNode M Unit Sym

/-- Memory constraints over integer values. -/
def memIvConstraint : Codec (MemConstraint Int) := memConstraint integerValue rfl

@[simp] theorem memIvConstraint_budget : memIvConstraint.budget = none := rfl

/-- Inside the generic `Core.PexprNode`, `M.IntegerValue` is abstract and sized
by `instSizeOfDefault`; termination proofs must use the same size for `Int`. -/
local instance : SizeOf Int := instSizeOfDefault Int

mutual

def encodePexpr : Pexpr → Tree
  | .mk as u e => node (tag% Core.Pexpr.mk) [(list annot).enc as, unit.enc u, encodePexprNode e]

def encodePexprNode : PexprNode → Tree
  | .sym s => node (tag% Core.PexprNode.sym) [sym.enc s]
  | .impl i => node (tag% Core.PexprNode.impl) [implementationConstant.enc i]
  | .val v => node (tag% Core.PexprNode.val) [value.enc v]
  | .constrained cs => node (tag% Core.PexprNode.constrained) [node "$list" (cs.map fun p =>
      node "$tuple" [memIvConstraint.enc p.1, encodePexpr p.2])]
  | .undef l u => node (tag% Core.PexprNode.undef) [loc.enc l, undefinedBehaviour.enc u]
  | .error s e => node (tag% Core.PexprNode.error) [str.enc s, encodePexpr e]
  | .ctor c es => node (tag% Core.PexprNode.ctor) [ctor.enc c, node "$list" (es.map encodePexpr)]
  | .case_ e cs => node (tag% Core.PexprNode.case_) [encodePexpr e, node "$list" (cs.map fun p =>
      node "$tuple" [pattern.enc p.1, encodePexpr p.2])]
  | .arrayShift e t e' => node (tag% Core.PexprNode.arrayShift) [encodePexpr e, ctype.enc t, encodePexpr e']
  | .memberShift e s i => node (tag% Core.PexprNode.memberShift) [encodePexpr e, sym.enc s, identifier.enc i]
  | .memop o es => node (tag% Core.PexprNode.memop) [pureMemOp.enc o, node "$list" (es.map encodePexpr)]
  | .not e => node (tag% Core.PexprNode.not) [encodePexpr e]
  | .op o e e' => node (tag% Core.PexprNode.op) [binOp.enc o, encodePexpr e, encodePexpr e']
  | .convInt t e => node (tag% Core.PexprNode.convInt) [integerType.enc t, encodePexpr e]
  | .wrapI t o e e' => node (tag% Core.PexprNode.wrapI) [integerType.enc t, intOp.enc o, encodePexpr e, encodePexpr e']
  | .catchExceptionalCondition t o e e' =>
    node (tag% Core.PexprNode.catchExceptionalCondition) [integerType.enc t, intOp.enc o, encodePexpr e, encodePexpr e']
  | .struct s fs => node (tag% Core.PexprNode.struct) [sym.enc s, node "$list" (fs.map fun p =>
      node "$tuple" [identifier.enc p.1, encodePexpr p.2])]
  | .union s i e => node (tag% Core.PexprNode.union) [sym.enc s, identifier.enc i, encodePexpr e]
  | .cfunction e => node (tag% Core.PexprNode.cfunction) [encodePexpr e]
  | .memberof s i e => node (tag% Core.PexprNode.memberof) [sym.enc s, identifier.enc i, encodePexpr e]
  | .call n es => node (tag% Core.PexprNode.call) [name.enc n, node "$list" (es.map encodePexpr)]
  | .let_ p e e' => node (tag% Core.PexprNode.let_) [pattern.enc p, encodePexpr e, encodePexpr e']
  | .if_ e e' e'' => node (tag% Core.PexprNode.if_) [encodePexpr e, encodePexpr e', encodePexpr e'']
  | .isScalar e => node (tag% Core.PexprNode.isScalar) [encodePexpr e]
  | .isInteger e => node (tag% Core.PexprNode.isInteger) [encodePexpr e]
  | .isSigned e => node (tag% Core.PexprNode.isSigned) [encodePexpr e]
  | .isUnsigned e => node (tag% Core.PexprNode.isUnsigned) [encodePexpr e]
  | .bmcAssume e => node (tag% Core.PexprNode.bmcAssume) [encodePexpr e]
  | .areCompatible e e' => node (tag% Core.PexprNode.areCompatible) [encodePexpr e, encodePexpr e']
decreasing_by codec_decreasing

end

def pexprNode (c : Codec Pexpr) (h : c.enc = encodePexpr) : Codec PexprNode :=
  let e := slot c encodePexpr h
  ofAlts encodePexprNode
  [alt% Core.PexprNode.sym sym,
   alt% Core.PexprNode.impl implementationConstant,
   alt% Core.PexprNode.val value,
   alt% Core.PexprNode.constrained (list (tuple (memIvConstraint ⊗ e))),
   alt% Core.PexprNode.undef (loc ⊗ undefinedBehaviour),
   alt% Core.PexprNode.error (str ⊗ e),
   alt% Core.PexprNode.ctor (ctor ⊗ list e),
   alt% Core.PexprNode.case_ (e ⊗ list (tuple (pattern ⊗ e))),
   alt% Core.PexprNode.arrayShift (e ⊗ ctype ⊗ e),
   alt% Core.PexprNode.memberShift (e ⊗ sym ⊗ identifier),
   alt% Core.PexprNode.memop (pureMemOp ⊗ list e),
   alt% Core.PexprNode.not e,
   alt% Core.PexprNode.op (binOp ⊗ e ⊗ e),
   alt% Core.PexprNode.convInt (integerType ⊗ e),
   alt% Core.PexprNode.wrapI (integerType ⊗ intOp ⊗ e ⊗ e),
   alt% Core.PexprNode.catchExceptionalCondition (integerType ⊗ intOp ⊗ e ⊗ e),
   alt% Core.PexprNode.struct (sym ⊗ list (tuple (identifier ⊗ e))),
   alt% Core.PexprNode.union (sym ⊗ identifier ⊗ e),
   alt% Core.PexprNode.cfunction e,
   alt% Core.PexprNode.memberof (sym ⊗ identifier ⊗ e),
   alt% Core.PexprNode.call (name ⊗ list e),
   alt% Core.PexprNode.let_ (pattern ⊗ e ⊗ e),
   alt% Core.PexprNode.if_ (e ⊗ e ⊗ e),
   alt% Core.PexprNode.isScalar e,
   alt% Core.PexprNode.isInteger e,
   alt% Core.PexprNode.isSigned e,
   alt% Core.PexprNode.isUnsigned e,
   alt% Core.PexprNode.bmcAssume e,
   alt% Core.PexprNode.areCompatible (e ⊗ e)]
  (by codec_nodup) (by codec_enc [encodePexprNode]) (by codec_cover)

def pexprLayer : Layer Pexpr encodePexpr where
  build c h := ofAlts encodePexpr
    [alt% Core.Pexpr.mk (list annot ⊗ unit ⊗ pexprNode c h)]
    (by codec_nodup) (by codec_enc [encodePexpr]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [pexprNode, hk]; omega

def pexpr : Codec Pexpr := fix encodePexpr pexprLayer

@[simp] theorem pexpr_budget : pexpr.budget = none := rfl

-- Literal tags test semantic identity independently of encoder/decoder agreement.
example : binOp.dec (node "OpAdd" []) = some Core.BinOp.add := rfl
example : binOp.dec (node "OpSub" []) = some Core.BinOp.sub := rfl
example : pexpr.dec
    (node "Pexpr" [node "$list" [], node "$unit" [], node "PEval" [node "Vtrue" []]]) =
    some (.mk [] () (.val .true)) := rfl
example : pexpr.dec
    (node "Pexpr" [node "$list" [], node "$unit" [], node "PEnot"
      [node "Pexpr" [node "$list" [], node "$unit" [], node "PEval" [node "Vtrue" []]]]]) =
    some (.mk [] () (.not (.mk [] () (.val .true)))) := rfl

end Silmaril.Cerberus.Codec
