module

public import Silmaril.Wasm.Wit.Syntax.Defs

/-!
# WAC: extern names

The two operations on extern names that WAC's name inference uses
(wac `5a7480c`, `crates/wac-parser/src/resolution.rs` and
`crates/wac-types/src/names.rs`):

* `tail n`: the last segment of an interface path, without its version: the
  `baz` of `foo:bar/baz@1.0.0`. `find_matching_interface_name` compares it with
  a local identifier. A name without `/` has no tail.
* `altKey n`: the *semver track* of a versioned name (`alternate_lookup_key`):
  `a:b/c@1.2.3` is on the track `a:b/c@1`, `a:b/c@0.2.3` on `a:b/c@0.2`;
  `0.0.z` versions and pre-releases are on no track. `compat a b` is
  `are_semver_compatible`: equal names, or names on the same track.

Versions are read as the `semver` crate (1.x, `Version::parse`) reads them:
`major.minor.patch`, each a numeric identifier (`0` or digits without a leading zero,
below `2^64`), followed by nothing or `+build`, where `build` is a non-empty list of
non-empty dot-separated identifiers over `[0-9A-Za-z-]` (leading zeros allowed there).
A `-pre` suffix (valid or not) and everything else is on no track: `semver` rejects
invalid strings, and wac puts pre-releases on no track. So `a:b/c@01.0.0` and
`a:b/c@1.0.0+` have no track (`readVersion_noLeadingZero`, `Wac.Names.Thms`).

`verOf n` is the numeric version `(major, minor, patch)` of a name with a version;
`verGt a b` compares it lexicographically. The `semver` crate also orders build
metadata; two versions differing only in build metadata are *not* `verGt` here (a
documented approximation, used only by the merging of implicit imports).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

/-- The characters after the last `/`, or `none` without `/`. -/
def afterLastSlash : List Char → Option (List Char)
  | [] => none
  | c :: cs =>
    match afterLastSlash cs with
    | some t => some t
    | none => if c = '/' then some cs else none

/-- The characters before the first `@`. -/
def beforeAt : List Char → List Char
  | [] => []
  | c :: cs => if c = '@' then [] else c :: beforeAt cs

/-- The last path segment of an extern name, without its version. -/
def tail (n : String) : Option String :=
  (afterLastSlash n.toList).map fun t => String.ofList (beforeAt t)

/-- Split at the first occurrence of `d`: the prefix and, if `d` occurs, the rest. -/
def splitAt (d : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = d then ([], some cs)
    else let (a, b) := splitAt d cs; (c :: a, b)

/-- The leading decimal digits and the rest. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if c.isDigit then let (a, b) := spanDigits cs; (c :: a, b) else ([], c :: cs)

/-- The value of a list of decimal digits. -/
def digitsVal (ds : List Char) : Nat :=
  ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A numeric identifier of `semver`: `0`, or digits without a leading zero, below `2^64`. -/
def numOk (ds : List Char) : Bool :=
  match ds with
  | [] => false
  | ['0'] => true
  | '0' :: _ => false
  | _ => decide (digitsVal ds < 2 ^ 64)

/-- Split at every `.`. -/
def splitDots : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '.' then [] :: splitDots cs
    else match splitDots cs with
      | [] => [[c]]
      | s :: ss => (c :: s) :: ss

/-- A build-metadata identifier: non-empty, over `[0-9A-Za-z-]`. -/
def buildIdOk (s : List Char) : Bool := !s.isEmpty && s.all fun c => c.isAlphanum || c = '-'

/-- Build metadata: non-empty dot-separated identifiers. -/
def buildOk (b : List Char) : Bool := (splitDots b).all buildIdOk

/-- A version `major.minor.patch(+build)?` as its three numerals; `none` for
anything else (a pre-release, a leading zero, an empty build identifier included). -/
def readVersion (v : List Char) : Option (List Char × List Char × List Char) :=
  let (ma, r1) := spanDigits v
  match r1 with
  | '.' :: r1' =>
    let (mi, r2) := spanDigits r1'
    match r2 with
    | '.' :: r2' =>
      let (pa, r3) := spanDigits r2'
      if !(numOk ma && numOk mi && numOk pa) then none
      else match r3 with
        | [] => some (ma, mi, pa)
        | '+' :: b => if buildOk b then some (ma, mi, pa) else none
        | _ => none
    | _ => none
  | _ => none

/-- The semver track of a name (wac's `alternate_lookup_key`). -/
def altKey (n : String) : Option String :=
  match splitAt '@' n.toList with
  | (_, none) => none
  | (pre, some v) =>
    match readVersion v with
    | none => none
    | some (ma, mi, _) =>
      if digitsVal ma ≠ 0 then some (String.ofList (pre ++ '@' :: ma))
      else if digitsVal mi ≠ 0 then some (String.ofList (pre ++ '@' :: ma ++ '.' :: mi))
      else none

/-- The numeric version `(major, minor, patch)` of a name `…@version`. -/
def verOf (n : String) : Option (Nat × Nat × Nat) :=
  match splitAt '@' n.toList with
  | (_, none) => none
  | (_, some v) => (readVersion v).map fun (ma, mi, pa) => (digitsVal ma, digitsVal mi, digitsVal pa)

/-- Lexicographic order of numeric versions. -/
def verLt : Nat × Nat × Nat → Nat × Nat × Nat → Bool
  | (a, b, c), (a', b', c') => decide (a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c'))))

/-- The version of `a` is greater than the version of `b` (both have one). -/
def verGt (a b : String) : Bool :=
  match verOf a, verOf b with
  | some x, some y => verLt y x
  | _, _ => false

/-- wac's `are_semver_compatible`. -/
def compat (a b : String) : Bool :=
  a == b || match altKey a, altKey b with
    | some x, some y => x == y
    | _, _ => false

end Silmaril.Wasm.Wac
