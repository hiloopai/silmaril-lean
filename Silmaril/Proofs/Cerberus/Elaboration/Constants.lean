module

public import Silmaril.Cerberus.Elaboration.Constants.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Constants
open Silmaril.Cerberus
open Construction

/-- A literal's loaded value is not replaced by a raw object integer or by a
specified constructor application. Its spelling does not alter that value. -/
theorem translate_integer (config : Target.Config) (env : Target.Environment)
    (value : Int) (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) :
    translateConstant config env (.integer (.iconstant value basis suffix)) =
      .ok (valuePure (.loaded (.specified (.integer value)))) := by
  simp only [translateConstant]
  rfl

theorem marker_duplicate (first second : Nat) :
    marker [.marker first, .marker second] = .error "found more than one marker" := rfl

theorem integer_expression_annotations (annotations : List Annot) (location : Loc)
    (type : IntegerType) (expression : Pure) :
    addLocation location (addExpression
      (annotateIntegerEffect (.mk annotations (.basic (.integer type))) (pureEffect expression))) =
    .mk [.loc location, .expr, .value (.integer type)] (.pure expression) := rfl

/-- The concrete backend's bound differs from frontend signed wchar ranges. -/
theorem pinned_wchar_maximum :
    concreteMaximum Target.pinnedApple Target.emptyEnvironment .wchar = .ok 4294967295 := rfl

theorem pinned_wint_minimum :
    concreteMinimum Target.pinnedApple Target.emptyEnvironment .wint = .ok 0 := rfl

/-- Numeric escape wrapping follows plain-char signedness at a fixed eight bits. -/
theorem pinned_hex_ff_character (raw : Cabs.RawString)
    (bytes : rawBytes raw = [92, 120, 70, 70]) :
    decodeCharacter Target.pinnedApple raw = .ok (-1) := by
  simp only [decodeCharacter, bytes]
  rfl

end Silmaril.Cerberus.Elaboration.Constants
