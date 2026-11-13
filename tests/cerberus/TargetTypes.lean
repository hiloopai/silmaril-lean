import Silmaril.Cerberus.Target.Thms
import Silmaril.Cerberus.GeneralizedTypes.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Target
open Silmaril.Cerberus.GeneralizedTypes

-- Decimal overflow chooses signed long; hexadecimal first tries unsigned int.
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 2147483648 .decimal none) = .ok (.signed .long) := by rfl
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 2147483648 .hexadecimal none) = .ok (.unsigned .int) := by rfl
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 4294967296 .binary none) = .ok (.signed .long) := by rfl
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 9223372036854775808 .decimal none) =
      .error (.untypableIntegerConstant .unknown 9223372036854775808) := by rfl
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 18446744073709551615 .hexadecimal (some .ull)) =
      .ok (.unsigned .longLong) := by rfl
example : typeOfConstant pinnedApple emptyEnvironment .unknown
    (.iconstant 18446744073709551616 .hexadecimal (some .ull)) =
      .error (.untypableIntegerConstant .unknown 18446744073709551616) := by rfl

-- Target aliases are one-step, and unsupported exact widths fail explicitly.
example : normalize pinnedApple emptyEnvironment (.signed (.intN 64)) = .ok (.signed .long) := by rfl
example : normalize pinnedApple emptyEnvironment (.signed (.intLeastN 32)) = .ok (.signed .int) := by rfl
example : normalize pinnedApple emptyEnvironment (.unsigned (.intFastN 16)) = .ok (.unsigned .short) := by rfl
example : normalize pinnedApple emptyEnvironment (.signed (.intN 24)) = .error (.unsupportedWidth 24) := by rfl
example : normalize pinnedApple emptyEnvironment .size = .ok (.unsigned .long) := by rfl
example : normalize pinnedApple emptyEnvironment .ptraddr = .ok .ptraddr := by rfl

-- Preserve source behavior, including the eight-bit Bool precision shortcut.
example : precision pinnedApple emptyEnvironment .bool = .ok 8 := by rfl
example : integerRange pinnedApple emptyEnvironment .bool = .ok ⟨0, 255⟩ := by rfl
example : promote pinnedApple emptyEnvironment .bool = .ok (.signed .int) := by rfl
example : promote pinnedApple emptyEnvironment (.unsigned .short) = .ok (.signed .int) := by rfl
example : usualInteger pinnedApple emptyEnvironment (.unsigned .int) (.signed .long) = .ok (.signed .long) := by rfl
example : usualInteger pinnedApple emptyEnvironment (.unsigned .long) (.signed .longLong) =
    .ok (.unsigned .longLong) := by rfl
example : usualInteger pinnedApple emptyEnvironment .size (.signed .intptr) = .ok .size := by rfl
example : usualInteger pinnedApple emptyEnvironment (.signed .intptr) (.unsigned .longLong) =
    .ok (.signed .intptr) := by rfl
example : leIntegerRange pinnedApple emptyEnvironment (.signed .longLong) (.signed .long) = .ok true := by rfl
example : leIntegerRange pinnedApple emptyEnvironment .ptraddr (.unsigned .long) =
    .error (.unsupportedRangeComparison .ptraddr (.unsigned .long)) := by rfl
example : promote {pinnedApple with cheri := true} emptyEnvironment (.signed .int) =
    .error .unsupportedCheri := by rfl

private def tag : Sym := ⟨⟨[]⟩, 17, .id "enum"⟩
private def renamedTag : Sym := {tag with description := .id "different diagnostic"}
private def unsignedEnum : Environment := ⟨Map.ofList [(tag, .unsigned .int)]⟩
private def signedEnum : Environment := ⟨Map.ofList [(tag, .signed .int)]⟩

-- Enum identity ignores diagnostic descriptions; unknown/duplicate tags reject.
example : normalize pinnedApple unsignedEnum (.enum renamedTag) = .ok (.unsigned .int) := by rfl
example : signedness pinnedApple signedEnum (.enum renamedTag) = .ok true := by rfl
example : normalize pinnedApple emptyEnvironment (.enum tag) = .error (.unregisteredEnum tag) := by rfl
example : registerEnum unsignedEnum renamedTag [-1, 1] = .error (.duplicateEnum renamedTag) := by
  apply registerEnum_rejects_existing _ _ _ (.unsigned .int)
  rfl
example : (registerEnum emptyEnvironment tag [-1, 1]).map
    (fun env => Map.lookup tag env.enums) = .ok (some (.signed .int)) := by rfl
example : (registerEnum emptyEnvironment tag [0, 1]).map
    (fun env => Map.lookup renamedTag env.enums) = .ok (some (.unsigned .int)) := by rfl

-- Exercise actual generalized syntax and actual annotated Ctype results.
example : interpretInteger pinnedApple emptyEnvironment .unknown
    (.usual (.promote (.concrete (.unsigned .short))) (.concrete (.signed .long))) =
      .ok (.signed .long) := by rfl
example : interpretType pinnedApple emptyEnvironment (.point "example.c" 3 7)
    (.atomic (.basic (.integer (.unknown (.iconstant 2147483648 .decimal none))))) =
      .ok (.mk [.loc (.point "example.c" 3 7)]
        (.atomic (.mk [.loc (.point "example.c" 3 7)] (.basic (.integer (.signed .long)))))) := by rfl
example (type : Ctype) (qs : Qualifiers) :
    interpretType pinnedApple emptyEnvironment .unknown (.pointer qs type) =
      .ok (.mk [.loc .unknown] (.pointer qs type)) := rfl
example (type : Ctype) (qs : Qualifiers) :
    interpretCategory pinnedApple emptyEnvironment .unknown (.lvalue qs type true) =
      .ok (.lvalue qs type true) := rfl

#print axioms firstRepresentable_sound
#print axioms typeOfConstant_representable
#print axioms registerEnum_lookup
#print axioms enum_lookup_of_key_eq
