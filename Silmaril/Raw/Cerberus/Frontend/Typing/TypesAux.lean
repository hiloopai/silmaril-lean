module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.Cerberus.Frontend.Typing.Ctype.Defs

/-! # Predicates and constructions on C types: `AilTypesAux`

A port of the functions of `frontend/model/ail/ailTypesAux.lem` at `b3e11ea3` that the
desugaring uses: the shape predicates, completeness (against the tag definitions of a
sigma), compatibility (STD §6.2.7) and composite types, and the adjustment of parameter
types (STD §6.7.6.3#7-8). These helpers are shared by desugaring and typing;
lookups and completeness are generic over the sigma annotation.

Lem's `error` cases (completeness of a function type, a tag resolved to the wrong kind) are
unreachable from well-formed desugaring states; they return the answer that lets the
desugaring go on, since Cerberus crashes there and the oracle scores no such file.

`Implementation.normalise_integerType` reads the implementation's global enum registry;
the port passes it as `typeofEnum`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- `AilTypesAux.is_unqualified` (`ailTypesAux.lem:6`). -/
def isUnqualified (qs : Qualifiers) : Bool := !qs.const && !qs.restrict && !qs.volatile

/-- `AilTypesAux.is_integer` (`ailTypesAux.lem:36`). -/
def isInteger : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

/-- `AilTypesAux.is_void` (`ailTypesAux.lem:52`). -/
def isVoid : Ctype → Bool
  | .mk _ .void => true
  | _ => false

/-- `AilTypesAux.is_pointer` (`ailTypesAux.lem:60`). -/
def isPointer : Ctype → Bool
  | .mk _ (.pointer ..) => true
  | _ => false

/-- `AilTypesAux.is_atomic` (`ailTypesAux.lem:76`), STD §6.2.5#20, bullet 6. -/
def isAtomic : Ctype → Bool
  | .mk _ (.atomic _) => true
  | _ => false

/-- `AilTypesAux.is_array` (`ailTypesAux.lem:115`). -/
def isArray : Ctype → Bool
  | .mk _ (.array ..) => true
  | _ => false

/-- `AilTypesAux.is_function` (`ailTypesAux.lem:140`), STD §6.2.5#1, sentence 3. -/
def isFunction : Ctype → Bool
  | .mk _ (.function ..) | .mk _ (.functionNoParams _) => true
  | _ => false

/-- `AilTypesAux.is_object` (`ailTypesAux.lem:197`), STD §6.2.5#1, sentence 3. -/
def isObject (ty : Ctype) : Bool := !isFunction ty

/-- `symbol.lem:133`: symbol equality ignores descriptions. Check the number first
so failed linear lookups do not repeatedly traverse identical digest bytes. -/
@[inline] def symbolEqual (a b : Sym) : Bool := a.number == b.number && a.digest == b.digest

/-- The reordered pure checks implement exactly Lem's symbol key equality. -/
theorem symbolEqual_eq_true (a b : Sym) : symbolEqual a b = true ↔ a.key = b.key := by
  simp [symbolEqual, Sym.key, and_comm]

/-- `List.lookup sym sigm.tag_definitions`, comparing symbols as Lem does. -/
def lookupTagDefinition {α : Type} (sigm : Ail.Sigma α) (sym : Sym) : Option TagDefinition :=
  (sigm.tagDefinitions.find? (fun p => symbolEqual p.1 sym)).map (·.2.2.2)

/-- `AilTypesAux.is_complete` (`ailTypesAux.lem:220-272`), STD §6.2.5#1, sentence 4: atomic
types look at their argument, an array needs a size and a complete element, a struct or
union needs its definition. -/
def isComplete {α : Type} (sigm : Ail.Sigma α) : Ctype → Bool
  | .mk _ (.atomic ty) => isComplete sigm ty
  | .mk _ .void => false
  | .mk _ (.basic _) => true
  | .mk _ (.array elemTy nOpt) => isComplete sigm elemTy && nOpt.isSome
  | .mk _ (.function ..) | .mk _ (.functionNoParams _) => false
  | .mk _ (.pointer ..) => true
  | .mk _ (.struct sym) | .mk _ (.union sym) => (lookupTagDefinition sigm sym).isSome
  | .mk _ .byte => true

/-- `AilTypesAux.is_incomplete` (`ailTypesAux.lem:276`). -/
def isIncomplete {α : Type} (sigm : Ail.Sigma α) (ty : Ctype) : Bool := !isComplete sigm ty

/-- `AilTypesAux.is_complete_object` (`ailTypesAux.lem:1195`). -/
def isCompleteObject {α : Type} (sigm : Ail.Sigma α) (ty : Ctype) : Bool :=
  isObject ty && isComplete sigm ty

/-- The basic types `are_compatible` compares, integer types normalised
(`ailTypesAux.lem:788-804`). -/
def normaliseBasicType (typeofEnum : Sym → Option IntegerType) : BasicType → BasicType
  | .integer ity => .integer ((normaliseIntegerType typeofEnum ity).getD ity)
  | bty => bty

mutual

/-- `AilTypesAux.are_compatible` on unqualified types: the compatibility of the shapes. -/
def areCompatibleCtype (typeofEnum : Sym → Option IntegerType) : Ctype → Ctype → Bool
  | .mk _ ty₁, .mk _ ty₂ => areCompatibleNodes typeofEnum ty₁ ty₂

/-- The match of `are_compatible` on the shapes (`ailTypesAux.lem:784-843`). -/
def areCompatibleNodes (typeofEnum : Sym → Option IntegerType) : CtypeNode → CtypeNode → Bool
  | .void, .void => true
  | .basic b₁, .basic b₂ =>
    basicTypeEqual (normaliseBasicType typeofEnum b₁) (normaliseBasicType typeofEnum b₂)
  | .array e₁ n₁, .array e₂ n₂ =>
    -- STD §6.7.6.2#6
    areCompatibleCtype typeofEnum e₁ e₂ &&
      match n₁, n₂ with
      | some a, some b => a == b
      | _, _ => true
  | .function (rq₁, rt₁) ps₁ v₁, .function (rq₂, rt₂) ps₂ v₂ =>
    -- STD §6.7.6.3#15
    rq₁ == rq₂ && areCompatibleCtype typeofEnum rt₁ rt₂ && areCompatibleParams typeofEnum ps₁ ps₂ &&
      v₁ == v₂
  | .functionNoParams (rq₁, rt₁), .functionNoParams (rq₂, rt₂) =>
    rq₁ == rq₂ && areCompatibleCtype typeofEnum rt₁ rt₂
  | .function (rq₁, rt₁) _ v₁, .functionNoParams (rq₂, rt₂) =>
    rq₁ == rq₂ && areCompatibleCtype typeofEnum rt₁ rt₂ && !v₁
  | .functionNoParams (rq₁, rt₁), .function (rq₂, rt₂) _ v₂ =>
    rq₁ == rq₂ && areCompatibleCtype typeofEnum rt₁ rt₂ && !v₂
  | .pointer q₁ r₁, .pointer q₂ r₂ =>
    -- STD §6.7.6.1#2
    q₁ == q₂ && areCompatibleCtype typeofEnum r₁ r₂
  | .struct t₁, .struct t₂ | .union t₁, .union t₂ => t₁.key == t₂.key
  | .atomic a₁, .atomic a₂ => areCompatibleCtype typeofEnum a₁ a₂
  | .byte, .byte => true
  | _, _ => false

/-- `AilTypesAux.are_compatible_params` (`ailTypesAux.lem:846-860`): the same length, and the
unqualified parameter types compatible (STD §6.7.6.3#15). -/
def areCompatibleParams (typeofEnum : Sym → Option IntegerType) :
    List (Qualifiers × Ctype × Bool) → List (Qualifiers × Ctype × Bool) → Bool
  | [], [] => true
  | (_, t₁, _) :: ps₁, (_, t₂, _) :: ps₂ =>
    areCompatibleCtype typeofEnum t₁ t₂ && areCompatibleParams typeofEnum ps₁ ps₂
  | _, _ => false

end

/-- `AilTypesAux.are_compatible` (`ailTypesAux.lem:782-844`), STD §6.2.7: equal qualifiers
(STD §6.7.3#10) and compatible shapes. -/
def areCompatible (typeofEnum : Sym → Option IntegerType) (p₁ p₂ : Qualifiers × Ctype) : Bool :=
  p₁.1 == p₂.1 && areCompatibleCtype typeofEnum p₁.2 p₂.2

mutual

/-- `AilTypesAux.make_composite` (`ailTypesAux.lem:886-975`), STD §6.2.7#3: the composite of
two compatible types, annotations concatenated. `none` where Lem fails. -/
def makeComposite (typeofEnum : Sym → Option IntegerType) : Ctype → Ctype → Option Ctype
  | cty₁@(.mk a₁ ty₁), cty₂@(.mk a₂ ty₂) =>
    if !areCompatible typeofEnum (noQualifiers, cty₁) (noQualifiers, cty₂) then none
    else makeCompositeNodes typeofEnum cty₁ a₁ a₂ ty₁ ty₂

/-- The match of `make_composite` on the shapes; `cty₁` is the first type. -/
def makeCompositeNodes (typeofEnum : Sym → Option IntegerType) (cty₁ : Ctype)
    (a₁ a₂ : List Annot) : CtypeNode → CtypeNode → Option Ctype
  | .void, .void => some (.mk (a₁ ++ a₂) .void)
  | .basic b₁, .basic _ => some (.mk (a₁ ++ a₂) (.basic b₁))
  | .array e₁ n₁, .array e₂ n₂ =>
    -- STD §6.2.7#3, first bullet
    let n := match n₁, n₂ with
      | some n, _ => some n
      | none, n => n
    (fun ty => .mk (a₁ ++ a₂) (.array ty n)) <$> makeComposite typeofEnum e₁ e₂
  | .function (rq₁, rt₁) ps₁ v₁, .function (_, rt₂) ps₂ v₂ =>
    if v₁ != v₂ then none
    else match makeComposite typeofEnum rt₁ rt₂, makeCompositeParamsAux typeofEnum ps₁ ps₂ with
      | some rt, some ps => some (.mk (a₁ ++ a₂) (.function (rq₁, rt) ps v₁))
      | _, _ => none
  | .functionNoParams (rq₁, rt₁), .functionNoParams (_, rt₂) =>
    (fun rt => .mk (a₁ ++ a₂) (.functionNoParams (rq₁, rt))) <$> makeComposite typeofEnum rt₁ rt₂
  | .function (rq₁, rt₁) ps₁ v₁, .functionNoParams (_, rt₂) =>
    if v₁ then none
    else (fun rt => .mk (a₁ ++ a₂) (.function (rq₁, rt) ps₁ v₁)) <$> makeComposite typeofEnum rt₁ rt₂
  | .functionNoParams (rq₁, rt₁), .function (_, rt₂) ps₂ v₂ =>
    if v₂ then none
    else (fun rt => .mk (a₁ ++ a₂) (.function (rq₁, rt) ps₂ v₂)) <$> makeComposite typeofEnum rt₁ rt₂
  | .pointer q₁ r₁, .pointer _ r₂ =>
    (fun r => .mk (a₁ ++ a₂) (.pointer q₁ r)) <$> makeComposite typeofEnum r₁ r₂
  | .atomic t₁, .atomic t₂ =>
    (fun t => .mk (a₁ ++ a₂) (.atomic t)) <$> makeComposite typeofEnum t₁ t₂
  | .struct t₁, .struct t₂ | .union t₁, .union t₂ => if t₁.key == t₂.key then some cty₁ else none
  | _, _ => none

/-- `AilTypesAux.make_composite_params_aux` (`ailTypesAux.lem:867-882`): pairwise composites,
unqualified and not `register`. -/
def makeCompositeParamsAux (typeofEnum : Sym → Option IntegerType) :
    List (Qualifiers × Ctype × Bool) → List (Qualifiers × Ctype × Bool) →
      Option (List (Qualifiers × Ctype × Bool))
  | [], [] => some []
  | (_, t₁, _) :: ps₁, (_, t₂, _) :: ps₂ =>
    match makeComposite typeofEnum t₁ t₂, makeCompositeParamsAux typeofEnum ps₁ ps₂ with
    | some t, some p => some ((noQualifiers, t, false) :: p)
    | _, _ => none
  | _, _ => none

end

/-- `AilTypesAux.make_composite_params` (`ailTypesAux.lem:978`). -/
def makeCompositeParams (typeofEnum : Sym → Option IntegerType)
    (ps₁ ps₂ : List (Qualifiers × Ctype × Bool)) : Option (List (Qualifiers × Ctype × Bool)) :=
  makeCompositeParamsAux typeofEnum ps₁ ps₂

/-- `AilTypesAux.variably_modified` (`ailTypesAux.lem:1170`): Cerberus's stub, always false
(VLAs are rejected before). -/
def variablyModified (_ : Ctype) : Bool := false

/-- `AilTypesAux.adjust` (`ailTypesAux.lem:1201-1219`): an array parameter becomes a pointer
to its element (STD §6.7.6.3#7), a function parameter a pointer to the function (STD
§6.7.6.3#8). -/
def adjust (qs : Qualifiers) : Ctype → Qualifiers × Ctype
  | .mk a (.array elemTy _) => (noQualifiers, .mk a (.pointer qs elemTy))
  | .mk a (.function rqt ps v) => (noQualifiers, .mk a (.pointer qs (.mk [] (.function rqt ps v))))
  | ty => (qs, ty)

/-- `AilTypesAux.is_floating` (`ailTypesAux.lem:44`). -/
def isFloating : Ctype → Bool
  | .mk _ (.basic (.floating _)) => true
  | _ => false

/-- `AilTypesAux.is_character` (`ailTypesAux.lem:95`). -/
def isCharacter : Ctype → Bool
  | .mk _ (.basic (.integer .char)) | .mk _ (.basic (.integer (.signed .ichar)))
  | .mk _ (.basic (.integer (.unsigned .ichar))) => true
  | _ => false

/-- `AilTypesAux.is_array_unknown_size` (`ailTypesAux.lem:123`). -/
def isArrayUnknownSize : Ctype → Bool
  | .mk _ (.array _ none) => true
  | _ => false

/-- `AilTypesAux.is_array_of_character` (`ailTypesAux.lem:131`). -/
def isArrayOfCharacter : Ctype → Bool
  | .mk _ (.array elemTy _) => isCharacter elemTy
  | _ => false

/-- `AilTypesAux.is_byte` (non-standard). -/
def isByte : Ctype → Bool
  | .mk _ .byte => true
  | _ => false

/-- `AilTypesAux.is_arithmetic` (`ailTypesAux.lem:202`), STD §6.2.5#18. -/
def isArithmetic (ty : Ctype) : Bool := isInteger ty || isFloating ty

/-- `AilTypesAux.is_scalar` (`ailTypesAux.lem:207`), STD §6.2.5#21, and bytes (non-standard). -/
def isScalar (ty : Ctype) : Bool := isPointer ty || isArithmetic ty || isByte ty

/-- `AilTypesAux.is_vla` (`ailTypesAux.lem:1188`): Cerberus's stub, always false. -/
def isVla (_ : Ctype) : Bool := false

/-- `ailTypesAux.lem:170`: flexible member reachability through unions (§6.7.2.1#3). -/
partial def hasFlexibleArrayMember {α : Type} (s : Ail.Sigma α) (t : Ctype) : Bool :=
  match projCtype_ t with
  | .struct tag => match lookupTagDefinition s tag with
    | some (.struct _ f) => f.isSome
    | _ => false
  | .union tag => match lookupTagDefinition s tag with
    | some (.union ms) => ms.any fun p => hasFlexibleArrayMember s p.2.2.2.2
    | _ => false
  | _ => false

/-- `ailTypesAux.lem:762`, ISO C11 §6.3.2.1#1. -/
def modifiable {α : Type} (s : Ail.Sigma α) (q : Qualifiers) (t : Ctype) : Bool :=
  !isArray t && !q.const && !isFunction t && isComplete s t

/-- `ailTypesAux.lem:981`, ISO C11 §6.3.2.1#3. -/
def arrayCoercion (t : Ctype) : Ctype := match t with
  | .mk a (.array e _) => .mk a (.pointer noQualifiers e)
  | _ => t
/-- `ailTypesAux.lem:1024`, ISO C11 §6.3.2.1#3-4. -/
def rvalueCoercion (t : Ctype) : Ctype := match t with
  | .mk a (.array e _) => .mk a (.pointer noQualifiers e)
  | .mk a (.function r ps v) => .mk a (.pointer noQualifiers (.mk [] (.function r ps v)))
  | _ => t

end Silmaril.Cerberus.Frontend
