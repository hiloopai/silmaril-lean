module

public import Silmaril.Compiler.Native.Types.Registered.Defs
public import Silmaril.Compiler.Native.Abi.Defs
public import Silmaril.Machine.SystemV.Abi.Ctypes.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Types.Registered
open Silmaril.Cerberus
open Silmaril.Cerberus.Mem.Concrete (Tags)
open Silmaril.Machine.SystemV.Abi

/-- Explicit implementation resolution commutes with the independently defined
source integer classifier, including missing and recursive registration errors. -/
theorem resolve_object (tags : Tags) (integer : IntegerType) :
    integerObject tags integer = (implementation tags integer).bind (integerObject ∅) := by
  cases integer with
  | enum tag =>
    cases found : tags.enums.lookup tag with
    | none => simp only [implementation, integerObject, found]; rfl
    | some underlying => cases underlying <;> simp only [implementation, integerObject, found] <;> rfl
  | char | bool | signed _ | unsigned _ | wchar | wint | size | ptrdiff | ptraddr => rfl

private def NonEnum : IntegerType → Prop
  | .enum _ => False
  | _ => True

private theorem implementation_non_enum (tags : Tags) (integer resolved : IntegerType)
    (resolution : implementation tags integer = .ok resolved) : NonEnum resolved := by
  cases integer with
  | enum tag =>
    cases found : tags.enums.lookup tag with
    | none => simp [implementation, found] at resolution
    | some underlying => cases underlying <;> simp_all [implementation, NonEnum, pure, Except.pure] <;> subst resolved <;> trivial
  | char | bool | signed _ | unsigned _ | wchar | wint | size | ptrdiff | ptraddr =>
    simp_all [implementation, NonEnum]; subst resolved; trivial

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem converted_integer (tags : Tags) (annotations : List Annot)
    (integer : IntegerType) (object : Object) (supported : annotationsSupported annotations = true)
    (classified : objectOfCtype tags (.mk annotations (.basic (.integer integer))) = .ok object)
    (source : integerObject tags integer = .ok object) :
    Silmaril.Compiler.Native.Abi.objectOfCodeType tags
      (ofCtype tags (.mk annotations (.basic (.integer integer)))) = .ok object := by
  cases resolution : implementation tags integer with
  | error why =>
    rw [resolve_object, resolution] at source
    cases source
  | ok resolved =>
    have empty : integerObject ∅ resolved = .ok object := by
      rw [resolve_object, resolution] at source
      exact source
    have nonenum := implementation_non_enum tags integer resolved resolution
    have ordinary : ∀ tag, resolved ≠ .enum tag := by
      cases resolved <;> simp_all [NonEnum]
    obtain ⟨bytes, same, width⟩ := integerObject_ordinary_shape ∅ resolved object ordinary empty
    subst object
    rcases width with rfl | rfl | rfl | rfl | rfl
    all_goals cases resolved <;>
      simp_all [NonEnum, ofCtype, integerType, Silmaril.Compiler.Native.Types.integerType,
        Silmaril.Compiler.Native.Abi.objectOfCodeType, Object.integer, integerObject,
        pure, Except.pure]

/-- Actual registered conversion preserves every successfully classified source
object. Ordinary enum parameters use their registered scalar implementation. -/
theorem classify (tags : Tags) (type : Ctype) (object : Object)
    (classified : objectOfCtype tags type = .ok object) :
    Silmaril.Compiler.Native.Abi.objectOfCodeType tags (ofCtype tags type) = .ok object := by
  obtain ⟨annotations, node⟩ := type
  have supported : annotationsSupported annotations = true :=
    objectOfCtype_annotations_supported tags annotations node object classified
  cases node with
  | basic basic =>
    show Silmaril.Compiler.Native.Abi.objectOfCodeType tags
      (ofCtype tags (.mk annotations (.basic basic))) = .ok object
    cases basic with
    | integer integer =>
      exact converted_integer tags annotations integer object supported classified
        (objectOfCtype_integer tags annotations integer object supported classified)
    | floating format =>
      cases format with
      | realFloating format =>
        cases format <;>
          simpa [ofCtype, Silmaril.Compiler.Native.Types.ofCtype, Silmaril.Compile.C.ofCtype,
            Silmaril.Compile.C.ofFloatingType, Silmaril.Compiler.Native.Abi.objectOfCodeType,
            objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, scalarObject,
            supported, Except.map] using classified
  | pointer qualifiers pointee | byte =>
    simpa [ofCtype, Silmaril.Compiler.Native.Types.ofCtype, Silmaril.Compile.C.ofCtype,
      Silmaril.Compiler.Native.Abi.objectOfCodeType, objectOfCtype, layoutOfCtype,
      layoutOfCtypeWithFuel, scalarObject, supported, Except.map] using classified
  | array element length | struct tag | union tag =>
    simpa [ofCtype, Silmaril.Compiler.Native.Types.ofCtype, Silmaril.Compile.C.ofCtype,
      Silmaril.Compiler.Native.Abi.objectOfCodeType, supported] using classified
  | void | function result parameters variadic | functionNoParams result | atomic underlying =>
    simp [objectOfCtype, layoutOfCtype, layoutOfCtypeWithFuel, supported, Except.map] at classified

/-- An empty enum registry preserves the original converter exactly, including
its explicit unknown-enum rejection. Record definitions may still be present. -/
theorem integerType_without_enums (tags : Tags) (whole : Ctype) (integer : IntegerType)
    (empty : tags.enums = ∅) :
    integerType tags whole integer = Silmaril.Compiler.Native.Types.integerType whole integer := by
  cases integer <;>
    simp [integerType, implementation, Silmaril.Compiler.Native.Types.integerType, integerObject, empty, Map.lookup]
  rfl

theorem ofCtype_without_enums (tags : Tags) (type : Ctype) (empty : tags.enums = ∅) :
    ofCtype tags type = Silmaril.Compiler.Native.Types.ofCtype type := by
  obtain ⟨annotations, node⟩ := type
  cases node <;> simp only [ofCtype, ite_self]
  rename_i basic
  cases basic <;> simp only [ite_self]
  simp only [Silmaril.Compiler.Native.Types.ofCtype]
  split
  · rfl
  · exact integerType_without_enums tags _ _ empty

theorem ordinaryIntegerLayout_without_enums (tags : Tags) (integer : IntegerType)
    (empty : tags.enums = ∅) :
    ordinaryIntegerLayout tags integer = Silmaril.Compiler.Native.Types.ordinaryIntegerLayout integer := by
  simp only [ordinaryIntegerLayout, integerType_without_enums tags _ _ empty,
    Silmaril.Compiler.Native.Types.ordinaryIntegerLayout]
  rfl

theorem constantIntegerLayout_without_enums (tags : Tags) (constant : Ail.IntegerConstant)
    (empty : tags.enums = ∅) :
    constantIntegerLayout tags constant = Silmaril.Compiler.Native.Types.constantIntegerLayout constant := by
  cases constant <;> simp only [constantIntegerLayout,
    ordinaryIntegerLayout_without_enums tags _ empty, Silmaril.Compiler.Native.Types.constantIntegerLayout]

/-- Enum-free literal values, including min/max bounds, keep the exact previous
errors and integers used by constant lowering. -/
theorem integerBounds_without_enums (tags : Tags) (integer : IntegerType)
    (empty : tags.enums = ∅) :
    integerBounds tags integer = Silmaril.Compiler.Native.Types.integerBounds integer := by
  cases integer <;> simp only [integerBounds, implementation]
  all_goals try rfl
  rw [empty]
  rfl

theorem integerConstantValue_without_enums (tags : Tags) (constant : Ail.IntegerConstant)
    (empty : tags.enums = ∅) :
    integerConstantValue tags constant = Silmaril.Compiler.Native.Types.integerConstantValue constant := by
  cases constant <;> simp only [integerConstantValue,
    integerBounds_without_enums tags _ empty, Silmaril.Compiler.Native.Types.integerConstantValue]

theorem resolveInteger_without_enums (tags : Tags) (integer : Ail.GenIntegerType)
    (empty : tags.enums = ∅) :
    resolveInteger tags integer = Silmaril.Compiler.Native.Types.resolveInteger integer := by
  induction integer <;> simp_all only [resolveInteger,
    Silmaril.Compiler.Native.Types.resolveInteger, ordinaryIntegerLayout_without_enums tags _ empty,
    constantIntegerLayout_without_enums tags _ empty]

theorem ofGenType_without_enums (tags : Tags) (type : Ail.GenType) (empty : tags.enums = ∅) :
    ofGenType tags type = Silmaril.Compiler.Native.Types.ofGenType type := by
  cases type <;> try rfl
  rename_i basic
  cases basic <;> try rfl
  rename_i integer
  cases integer <;> simp only [ofGenType, Silmaril.Compiler.Native.Types.ofGenType,
    integerType_without_enums tags _ _ empty, resolveInteger_without_enums tags _ empty] <;> rfl

theorem typeOf_without_enums (tags : Tags) (expression : Ail.TypedExpression)
    (empty : tags.enums = ∅) :
    typeOf tags expression = Silmaril.Compiler.Native.Types.typeOf expression := by
  cases expression.annotation <;> simp only [typeOf, Silmaril.Compiler.Native.Types.typeOf,
    ofCtype_without_enums tags _ empty, ofGenType_without_enums tags _ empty] <;> rfl

/-- Successful original code-type conversion already excludes missing top-level
enum metadata. Any explicit registry preserves such a converted source type. -/
theorem ofCtype_of_supported (tags : Tags) (type : Ctype)
    (supported : ∀ why, Silmaril.Compiler.Native.Types.ofCtype type ≠ .unsupported why) :
    ofCtype tags type = Silmaril.Compiler.Native.Types.ofCtype type := by
  obtain ⟨annotations, node⟩ := type
  simp only [ofCtype]
  split
  · rfl
  · rename_i admissible
    cases node <;> try rfl
    rename_i basic
    cases basic <;> try rfl
    rename_i integer
    simp only [Silmaril.Compiler.Native.Types.ofCtype, admissible] at supported ⊢
    cases integer <;> try rfl
    exact False.elim (supported "native enum ABI needs an explicit underlying type registration" rfl)

/-- A successfully decoded original bound or literal contains no unresolved
enum implementation. Its value is preserved for every explicit registry. -/
theorem integerConstantValue_of_resolved (tags : Tags) (constant : Ail.IntegerConstant) (value : Int)
    (resolved : Silmaril.Compiler.Native.Types.integerConstantValue constant = .ok value) :
    integerConstantValue tags constant = .ok value := by
  cases constant with
  | iconstant number base suffix => exact resolved
  | max integer | min integer =>
    cases integer <;> first
      | exact resolved
      | change (Except.error "native enum ABI needs an explicit underlying type registration" :
          Except String Int) = .ok value at resolved
        cases resolved

end Silmaril.Compiler.Native.Types.Registered
