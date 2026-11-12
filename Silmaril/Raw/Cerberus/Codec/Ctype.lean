module

public import Silmaril.Cerberus.Ctype.Defs
public import Silmaril.Cerberus.Codec.Symbol.Defs

/-! # Wire codecs for integer types, annotations and C types

`Ctype` and `CtypeNode` are mutually nested through products and lists, so their
encoders are defined by well-founded recursion and the decoder is the fixed
point of `ctypeLayer`. The layer decodes one `Ctype` node given an
approximant for the nested positions.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec


def encodeIntegerBaseType : IntegerBaseType → Tree
  | .ichar => node (tag% IntegerBaseType.ichar) []
  | .short => node (tag% IntegerBaseType.short) []
  | .int => node (tag% IntegerBaseType.int) []
  | .long => node (tag% IntegerBaseType.long) []
  | .longLong => node (tag% IntegerBaseType.longLong) []
  | .intN n => node (tag% IntegerBaseType.intN) [nat.enc n]
  | .intLeastN n => node (tag% IntegerBaseType.intLeastN) [nat.enc n]
  | .intFastN n => node (tag% IntegerBaseType.intFastN) [nat.enc n]
  | .intmax => node (tag% IntegerBaseType.intmax) []
  | .intptr => node (tag% IntegerBaseType.intptr) []

def integerBaseType : Codec IntegerBaseType := ofAlts encodeIntegerBaseType
  [leaf% IntegerBaseType.ichar,
   leaf% IntegerBaseType.short,
   leaf% IntegerBaseType.int,
   leaf% IntegerBaseType.long,
   leaf% IntegerBaseType.longLong,
   alt% IntegerBaseType.intN nat,
   alt% IntegerBaseType.intLeastN nat,
   alt% IntegerBaseType.intFastN nat,
   leaf% IntegerBaseType.intmax,
   leaf% IntegerBaseType.intptr]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeIntegerType : IntegerType → Tree
  | .char => node (tag% IntegerType.char) []
  | .bool => node (tag% IntegerType.bool) []
  | .signed b => node (tag% IntegerType.signed) [integerBaseType.enc b]
  | .unsigned b => node (tag% IntegerType.unsigned) [integerBaseType.enc b]
  | .enum s => node (tag% IntegerType.enum) [sym.enc s]
  | .wchar => node (tag% IntegerType.wchar) []
  | .wint => node (tag% IntegerType.wint) []
  | .size => node (tag% IntegerType.size) []
  | .ptrdiff => node (tag% IntegerType.ptrdiff) []
  | .ptraddr => node (tag% IntegerType.ptraddr) []

def integerType : Codec IntegerType := ofAlts encodeIntegerType
  [leaf% IntegerType.char,
   leaf% IntegerType.bool,
   alt% IntegerType.signed integerBaseType,
   alt% IntegerType.unsigned integerBaseType,
   alt% IntegerType.enum sym,
   leaf% IntegerType.wchar,
   leaf% IntegerType.wint,
   leaf% IntegerType.size,
   leaf% IntegerType.ptrdiff,
   leaf% IntegerType.ptraddr]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeBmcAnnot : BmcAnnot → Tree
  | .id n => node (tag% BmcAnnot.id) [nat.enc n]

def bmcAnnot : Codec BmcAnnot := ofAlts encodeBmcAnnot
  [alt% BmcAnnot.id nat]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-- `list (Loc.t * string * list (Loc.t * string))`. -/
def attrArgs : Codec (List (Loc × String × List (Loc × String))) :=
  list (tuple (loc ⊗ str ⊗ list (tuple (loc ⊗ str))))

def encodeAttribute : Attribute → Tree
  | ⟨ns, id, args⟩ =>
    node (recordTag% Attribute) [(option identifier).enc ns, identifier.enc id, attrArgs.enc args]

def attribute_ : Codec Attribute := ofAlts encodeAttribute
  [recordAlt% Attribute.mk (option identifier ⊗ identifier ⊗ attrArgs)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeAttributes : Attributes → Tree
  | .mk as => node (tag% Attributes.mk) [(list attribute_).enc as]

def attributes : Codec Attributes := ofAlts encodeAttributes
  [alt% Attributes.mk (list attribute_)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeLabelAnnot : LabelAnnot → Tree
  | .loop n => node (tag% LabelAnnot.loop) [nat.enc n]
  | .loopContinue n => node (tag% LabelAnnot.loopContinue) [nat.enc n]
  | .loopBreak n => node (tag% LabelAnnot.loopBreak) [nat.enc n]
  | .return_ => node (tag% LabelAnnot.return_) []
  | .switch => node (tag% LabelAnnot.switch) []
  | .case_ => node (tag% LabelAnnot.case_) []
  | .default => node (tag% LabelAnnot.default) []
  | .actualLabel => node (tag% LabelAnnot.actualLabel) []

def labelAnnot : Codec LabelAnnot := ofAlts encodeLabelAnnot
  [alt% LabelAnnot.loop nat,
   alt% LabelAnnot.loopContinue nat,
   alt% LabelAnnot.loopBreak nat,
   leaf% LabelAnnot.return_,
   leaf% LabelAnnot.switch,
   leaf% LabelAnnot.case_,
   leaf% LabelAnnot.default,
   leaf% LabelAnnot.actualLabel]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeCerbAttribute : CerbAttribute → Tree
  | .withAddress n => node (tag% CerbAttribute.withAddress) [int.enc n]
  | .hidden => node (tag% CerbAttribute.hidden) []

def cerbAttribute : Codec CerbAttribute := ofAlts encodeCerbAttribute
  [alt% CerbAttribute.withAddress int,
   leaf% CerbAttribute.hidden]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeValueAnnot : ValueAnnot → Tree
  | .integer t => node (tag% ValueAnnot.integer) [integerType.enc t]

def valueAnnot : Codec ValueAnnot := ofAlts encodeValueAnnot
  [alt% ValueAnnot.integer integerType]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeAnnot : Annot → Tree
  | .std s => node (tag% Annot.std) [str.enc s]
  | .loc l => node (tag% Annot.loc) [loc.enc l]
  | .uid s => node (tag% Annot.uid) [str.enc s]
  | .marker n => node (tag% Annot.marker) [nat.enc n]
  | .markerObjectTypes n => node (tag% Annot.markerObjectTypes) [nat.enc n]
  | .bmc a => node (tag% Annot.bmc) [bmcAnnot.enc a]
  | .attrs a => node (tag% Annot.attrs) [attributes.enc a]
  | .typedef s => node (tag% Annot.typedef) [sym.enc s]
  | .label a => node (tag% Annot.label) [labelAnnot.enc a]
  | .cerb a => node (tag% Annot.cerb) [cerbAttribute.enc a]
  | .value a => node (tag% Annot.value) [valueAnnot.enc a]
  | .inlinedLabel (l, s, a) =>
    node (tag% Annot.inlinedLabel) [node "$tuple" [loc.enc l, sym.enc s, labelAnnot.enc a]]
  | .stmt => node (tag% Annot.stmt) []
  | .expr => node (tag% Annot.expr) []

def annot : Codec Annot := ofAlts encodeAnnot
  [alt% Annot.std str,
   alt% Annot.loc loc,
   alt% Annot.uid str,
   alt% Annot.marker nat,
   alt% Annot.markerObjectTypes nat,
   alt% Annot.bmc bmcAnnot,
   alt% Annot.attrs attributes,
   alt% Annot.typedef sym,
   alt% Annot.label labelAnnot,
   alt% Annot.cerb cerbAttribute,
   alt% Annot.value valueAnnot,
   alt% Annot.inlinedLabel (tuple (loc ⊗ sym ⊗ labelAnnot)),
   leaf% Annot.stmt,
   leaf% Annot.expr]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeRealFloatingType : RealFloatingType → Tree
  | .float => node (tag% RealFloatingType.float) []
  | .double => node (tag% RealFloatingType.double) []
  | .longDouble => node (tag% RealFloatingType.longDouble) []

def realFloatingType : Codec RealFloatingType := ofAlts encodeRealFloatingType
  [leaf% RealFloatingType.float,
   leaf% RealFloatingType.double,
   leaf% RealFloatingType.longDouble]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeFloatingType : FloatingType → Tree
  | .realFloating t => node (tag% FloatingType.realFloating) [realFloatingType.enc t]

def floatingType : Codec FloatingType := ofAlts encodeFloatingType
  [alt% FloatingType.realFloating realFloatingType]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeBasicType : BasicType → Tree
  | .integer t => node (tag% BasicType.integer) [integerType.enc t]
  | .floating t => node (tag% BasicType.floating) [floatingType.enc t]

def basicType : Codec BasicType := ofAlts encodeBasicType
  [alt% BasicType.integer integerType,
   alt% BasicType.floating floatingType]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeQualifiers : Qualifiers → Tree
  | ⟨c, r, v⟩ => node (recordTag% Qualifiers) [boolean.enc c, boolean.enc r, boolean.enc v]

def qualifiers : Codec Qualifiers := ofAlts encodeQualifiers
  [recordAlt% Qualifiers.mk (boolean ⊗ boolean ⊗ boolean)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeLoopAttribute : LoopAttribute → Tree
  | ⟨m, a, c, l⟩ =>
    node (recordTag% LoopAttribute) [nat.enc m, attributes.enc a, loc.enc c, loc.enc l]

def loopAttribute : Codec LoopAttribute := ofAlts encodeLoopAttribute
  [recordAlt% LoopAttribute.mk (nat ⊗ attributes ⊗ loc ⊗ loc)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

@[simp] theorem integerBaseType_budget : integerBaseType.budget = none := rfl
@[simp] theorem integerType_budget : integerType.budget = none := rfl
@[simp] theorem annot_budget : annot.budget = none := rfl
@[simp] theorem basicType_budget : basicType.budget = none := rfl
@[simp] theorem qualifiers_budget : qualifiers.budget = none := rfl
@[simp] theorem attributes_budget : attributes.budget = none := rfl

mutual

def encodeCtype : Ctype → Tree
  | .mk as t => node (tag% Ctype.mk) [(list annot).enc as, encodeCtypeNode t]

def encodeCtypeNode : CtypeNode → Tree
  | .void => node (tag% CtypeNode.void) []
  | .basic b => node (tag% CtypeNode.basic) [basicType.enc b]
  | .array t n => node (tag% CtypeNode.array) [encodeCtype t, (option int).enc n]
  | .function (q, r) ps v =>
    node (tag% CtypeNode.function) [node "$tuple" [qualifiers.enc q, encodeCtype r],
      node "$list" (ps.map fun p =>
        node "$tuple" [qualifiers.enc p.1, encodeCtype p.2.1, boolean.enc p.2.2]),
      boolean.enc v]
  | .functionNoParams (q, r) =>
    node (tag% CtypeNode.functionNoParams) [node "$tuple" [qualifiers.enc q, encodeCtype r]]
  | .pointer q t => node (tag% CtypeNode.pointer) [qualifiers.enc q, encodeCtype t]
  | .atomic t => node (tag% CtypeNode.atomic) [encodeCtype t]
  | .struct s => node (tag% CtypeNode.struct) [sym.enc s]
  | .union s => node (tag% CtypeNode.union) [sym.enc s]
  | .byte => node (tag% CtypeNode.byte) []
decreasing_by codec_decreasing

end

/-- `CtypeNode` given an approximant `c` for its nested `Ctype`s. -/
def ctypeNode (c : Codec Ctype) (h : c.enc = encodeCtype) : Codec CtypeNode :=
  let t := slot c encodeCtype h
  ofAlts encodeCtypeNode
    [leaf% CtypeNode.void,
     alt% CtypeNode.basic basicType,
     alt% CtypeNode.array (t ⊗ option int),
     alt% CtypeNode.function (tuple (qualifiers ⊗ t) ⊗ list (tuple (qualifiers ⊗ t ⊗ boolean)) ⊗ boolean),
     alt% CtypeNode.functionNoParams (tuple (qualifiers ⊗ t)),
     alt% CtypeNode.pointer (qualifiers ⊗ t),
     alt% CtypeNode.atomic t,
     alt% CtypeNode.struct sym,
     alt% CtypeNode.union sym,
     leaf% CtypeNode.byte]
    (by codec_nodup) (by codec_enc [encodeCtypeNode]) (by codec_cover)

def ctypeLayer : Layer Ctype encodeCtype where
  build c h := ofAlts encodeCtype
    [alt% Ctype.mk (list annot ⊗ ctypeNode c h)]
    (by codec_nodup) (by codec_enc [encodeCtype]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [ctypeNode, hk]; omega

def ctype : Codec Ctype := fix encodeCtype ctypeLayer

@[simp] theorem ctype_budget : ctype.budget = none := rfl

def encodeFlexibleArrayMember : FlexibleArrayMember → Tree
  | .mk a i q t =>
    node (tag% FlexibleArrayMember.mk) [attributes.enc a, identifier.enc i, qualifiers.enc q, ctype.enc t]

def flexibleArrayMember : Codec FlexibleArrayMember := ofAlts encodeFlexibleArrayMember
  [alt% FlexibleArrayMember.mk (attributes ⊗ identifier ⊗ qualifiers ⊗ ctype)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeAlignment : Alignment → Tree
  | .integer n => node (tag% Alignment.integer) [int.enc n]
  | .ctype t => node (tag% Alignment.ctype) [ctype.enc t]

def alignment : Codec Alignment := ofAlts encodeAlignment
  [alt% Alignment.integer int, alt% Alignment.ctype ctype]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-- `list (identifier * (attributes * maybe alignment * qualifiers * ctype))`. -/
def members : Codec (List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) :=
  list (tuple (identifier ⊗ tuple (attributes ⊗ option alignment ⊗ qualifiers ⊗ ctype)))

def encodeTagDefinition : TagDefinition → Tree
  | .struct ms f => node (tag% TagDefinition.struct) [members.enc ms, (option flexibleArrayMember).enc f]
  | .union ms => node (tag% TagDefinition.union) [members.enc ms]

def tagDefinition : Codec TagDefinition := ofAlts encodeTagDefinition
  [alt% TagDefinition.struct (members ⊗ option flexibleArrayMember),
   alt% TagDefinition.union members]
  (by codec_nodup) (by codec_enc) (by codec_cover)

example : ctype.dec (node "Ctype" [node "$list" [], node "Void" []]) =
    some (.mk [] .void) := rfl
example : ctype.dec (node "Ctype" [node "$list" [], node "Byte" []]) =
    some (.mk [] .byte) := rfl

end Silmaril.Cerberus.Codec
