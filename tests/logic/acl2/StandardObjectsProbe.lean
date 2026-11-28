module

import Silmaril.Logic.ACL2.Standard.Objects.Defs
meta import Silmaril.Logic.ACL2.Standard.Objects.Defs

open Silmaril.Logic.ACL2.Standard

private def symbol (pkg spelling : String) (h : (Symbol.ofName? ⟨pkg, spelling⟩).isSome) : Object :=
  .symbol ((Symbol.ofName? ⟨pkg, spelling⟩).get h)

private def truthBit (x : Object) : Int := if x = .nil then 0 else 1

private def asInt (x : Object) : IO Int :=
  match x.integerValue? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected integer observation, got {repr x}")

private def stringLength (x : Object) : IO Int :=
  match x with
  | .string s => pure s.length
  | _ => throw (IO.userError s!"Expected string observation, got {repr x}")

public def main : IO Unit := do
  let nil := Object.nil
  let t := Object.truth
  let pA := symbol "SILMARIL-P" "A" (by decide)
  let qA := symbol "SILMARIL-Q" "A" (by decide)
  -- The native reader resolves SILMARIL-P::NIL through the import. Lean gets that identity.
  let importedNil := symbol "COMMON-LISP" "NIL" (by decide)
  let otherNil := symbol "SILMARIL-Q" "NIL" (by decide)
  let list := Object.symbol Symbol.list
  let dotted := Object.cons pA (.integer 5)
  let chars := Object.cons (.character 65) (.cons (.integer 7) (.integer 5))
  let half := Object.rational (Rat.divInt 1 2)
  let c := Object.ofParts 4 1
  let observations : List (String × Int) := [
    ("nil-home", if Symbol.nil.toName.package = "COMMON-LISP" then 1 else 0),
    ("t-home", if Symbol.truth.toName.package = "COMMON-LISP" then 1 else 0),
    ("imported-nil", truthBit (importedNil.equal nil)),
    ("other-nil", truthBit otherNil),
    ("same-spelling", truthBit (pA.equal qA)),
    ("symbol-completion", ← stringLength (Object.integer 3).symbolName),
    ("atom-car", truthBit (Object.integer 3).car),
    ("dotted-cdr", ← asInt dotted.cdr),
    ("dotted-append", ← asInt (dotted.append (.integer 6)).cdr),
    ("true-listp", if dotted.trueListp then 1 else 0),
    ("byte-255", ← asInt (Object.integer 255).codeChar.charCode),
    ("byte-negative", ← asInt (Object.integer (-1)).codeChar.charCode),
    ("byte-overflow", ← asInt (Object.integer 256).codeChar.charCode),
    ("char-completion", ← asInt (Object.string [97]).charCode),
    ("coerce-dotted", ← asInt ((chars.coerce t).coerce list).cdr.car.charCode),
    ("coerce-atom", truthBit ((Object.integer 7).coerce list)),
    ("reduced-denominator", ← asInt (Object.rational (Rat.divInt (-6) 8)).denominator),
    ("complex-zero", if (half.complex (.integer 0)).rationalp then 1 else 0),
    ("complex-completion", ← asInt (pA.complex half).imagpart.numerator),
    ("complex-inverse", ← asInt (Object.ofParts 1 2).reciprocal.imagpart.denominator),
    ("divide-zero", ← asInt (Object.integer 0).reciprocal),
    ("divide-atom", ← asInt pA.reciprocal),
    ("ordering-complex", truthBit (pA.less (Object.ofParts 0 1))),
    ("add-atom", ← asInt (pA.binaryAdd (.integer 8))),
    ("mul-atom", ← asInt ((Object.ofParts 0 1).binaryMul pA)),
    ("negate-atom", ← asInt pA.unaryMinus),
    ("numerator-complex", ← asInt c.numerator),
    ("denominator-complex", ← asInt c.denominator),
    ("zp-negative", truthBit (Object.integer (-3)).zp),
    ("zp-ratio", truthBit half.zp),
    ("zp-positive", truthBit (Object.integer 1).zp),
    ("nfix-decrement", ← asInt (Object.integer 1).decrement.nfix),
    ("acl2-count", (Object.cons (.string [97, 98, 99])
      (.cons (Object.ofParts (Rat.divInt (-1) 2) 2) (.integer 3))).acl2Count)]
  for (name, value) in observations do
    IO.println s!"SILMARIL {name} {value}"
