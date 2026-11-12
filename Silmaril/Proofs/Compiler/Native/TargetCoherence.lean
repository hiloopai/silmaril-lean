module

public import Silmaril.Compiler.Native.TargetCoherence.Defs
/-! These equalities compare actual target/helper/layout/code-type APIs.
They do not assert that agreeing layout implies source-to-machine refinement. -/
@[expose] public section
namespace Silmaril.Compiler.Native.TargetCoherence
open Silmaril.Cerberus
open Silmaril.Cerberus.Target
open Silmaril.Machine.SystemV.Abi
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- All28 explicitly listed integer names have the stated storage/signedness,
actual native code view and ABI object layout. -/
theorem ordinary_agrees (entry : Ordinary) (member : entry ∈ ordinary) : Agrees entry := by
  simp only [ordinary, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cbv

/-- Only the stated range-helper API is compared, with Bool excluded. -/
theorem helper_bounds_agree (entry : Ordinary) (member : entry ∈ ordinary)
    (notBool : entry.type ≠ .bool) : HelperBoundsAgree entry := by
  simp only [ordinary, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (notBool rfl) | cbv

/-- Concrete extrema agree on the stated subset; Bool and wchar retain
separate source helper behavior and are excluded explicitly. -/
theorem constant_bounds_agree (entry : Ordinary) (member : entry ∈ ordinary)
    (notBool : entry.type ≠ .bool) (notWchar : entry.type ≠ .wchar) :
    ConstantBoundsAgree entry := by
  simp only [ordinary, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact False.elim (notBool rfl) | exact False.elim (notWchar rfl) | cbv

/-- All pointer pointees/qualifiers share actual native64 storage. No claim
connects allocation/provenance values with concrete addresses. -/
theorem pointer_agrees (qualifiers : Qualifiers) (pointee : Ctype) :
    linuxLP64.pointerLayout = some ⟨8, 8⟩ ∧
    Types.ofCtype (.mk [] (.pointer qualifiers pointee)) = .ptr pointee ∧
    Layout.sizeAlign ∅ (.mk [] (.pointer qualifiers pointee)) = .ok (8, 8) ∧
    Abi.objectOfCodeType ∅ (.ptr pointee) = .ok .pointer := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Native128 is stored and classified as two INTEGER eightbytes, but the
ordinary integer lowering API deliberately rejects its address-backed view. -/
theorem extended128 (signed : Bool) :
    let type := if signed then IntegerType.signed (.intN 128) else .unsigned (.intN 128)
    integerLayout linuxLP64 emptyEnvironment type = .ok ⟨16, 16⟩ ∧
    Types.ofCtype (integerCtype type) = .agg (integerCtype type) ∧
    Layout.sizeAlign ∅ (integerCtype type) = .ok (16, 16) ∧
    Abi.objectOfCodeType ∅ (Types.ofCtype (integerCtype type)) = .ok (.integer 16 16) ∧
    Types.ordinaryIntegerLayout type = .error "native promoted integer needs retained extended metadata" := by
  cases signed <;> cbv

/-- Normalizing Linux wint selects unsigned int. The raw upstream helper
continues to call wint signed; the actual native adapter uses unsigned int. -/
theorem raw_wint_mismatch :
    normalize linuxLP64 emptyEnvironment .wint = .ok (.unsigned .int) ∧
    signedness linuxLP64 emptyEnvironment .wint = .ok true ∧
    Types.ordinaryIntegerLayout .wint = .ok (4, false) ∧
    Silmaril.Cerberus.Elaboration.Constants.concreteMaximum linuxLP64 emptyEnvironment .wint = .ok 2147483647 ∧
    Types.integerConstantValue (.max .wint) = .ok 4294967295 := by
  cbv

/-- Concrete typed-Ail interpretation preserves the raw name, so the signedness
issue cannot be dismissed as an unreachable constructor at this API boundary. -/
theorem wint_interpretation :
    Silmaril.Cerberus.GeneralizedTypes.interpretInteger linuxLP64 emptyEnvironment .unknown
      (.concrete .wint) = .ok .wint ∧
    Types.ofGenType (.basic (.integer (.concrete .wint))) = .int 4 false := by
  exact ⟨rfl, rfl⟩

/-- Raw arithmetic result types consult the actual target helper before any
normalization. This is a function equation, not an operational divergence claim. -/
theorem wint_arithmetic (operator : Silmaril.Cerberus.Core.IntOp)
    (left right fallback : Silmaril.Cerberus.Elaboration.Construction.Pure) :
    Silmaril.Cerberus.Elaboration.Arithmetic.withIntegerBehavior linuxLP64 emptyEnvironment
      (integerCtype .wint) operator left right fallback =
      .ok (Silmaril.Cerberus.Elaboration.Construction.catchExceptionalCondition .wint operator left right) := by
  rfl

/-- The generic source helper bounds are not Cerberus Bool value semantics.
The source runtime conversion/load checks still enforce0/1 separately. -/
theorem bool_helper_mismatch :
    integerRange linuxLP64 emptyEnvironment .bool = .ok ⟨0, 255⟩ ∧
    Types.integerBounds .bool = .ok (0, 1) ∧
    Silmaril.Cerberus.Elaboration.Constants.concreteMaximum linuxLP64 emptyEnvironment .bool = .ok 255 := by
  cbv

/-- Source concrete wchar extrema are a separate preserved upstream quirk;
these values disagree with the native signed32 bound constants. -/
theorem wchar_constants_mismatch :
    Silmaril.Cerberus.Elaboration.Constants.concreteMaximum linuxLP64 emptyEnvironment .wchar = .ok 4294967295 ∧
    Silmaril.Cerberus.Elaboration.Constants.concreteMinimum linuxLP64 emptyEnvironment .wchar = .ok 0 ∧
    Types.integerConstantValue (.max .wchar) = .ok 2147483647 ∧
    Types.integerConstantValue (.min .wchar) = .ok (-2147483648) := by
  cbv

/-- Selecting a new partial layout profile leaves the pinned Apple definition
and its recorded floating shortcut available unchanged. -/
theorem pinnedApple_float_unchanged :
    floatingLayout pinnedApple (.realFloating .float) = .ok ⟨8, 8⟩ := rfl

end Silmaril.Compiler.Native.TargetCoherence
