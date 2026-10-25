module

public import Silmaril.Formats.SExp.Proper
public import Silmaril.Formats.Cbor.Bytes

/-!
# Rivest/Eastlake S-expressions

The data model in draft-rivest-sexp-04 is just octet strings and finite lists.
This module begins with the mandatory canonical representation. Its parser
takes `Bytes`, since a verbatim atom is not necessarily UTF-8 text.
-/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats

/-- The semantic data model of draft-rivest-sexp-04. -/
abbrev RivestSExp := SExp Bytes

namespace RivestSExp

def digit? (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (byte.toNat - 48) else none

def decimal : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | fuel + 1, bytes =>
      match bytes with
      | [] => none
      | first :: rest => do
          let first ← digit? first
          if first = 0 then
            match rest with
            | 58 :: rest => some (0, rest)
            | _ => none
          else go fuel first rest
where
  go : Nat → Nat → List UInt8 → Option (Nat × List UInt8)
    | 0, _, _ => none
    | fuel + 1, value, bytes =>
        match bytes with
        | 58 :: rest => some (value, rest)
        | byte :: rest => do
            let digit ← digit? byte
            go fuel (value * 10 + digit) rest
        | [] => none

def splitExact (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

mutual
  def canonicalExpr : Nat → List UInt8 → Option (RivestSExp × List UInt8)
    | 0, _ => none
    | fuel + 1, bytes =>
        match bytes with
        | 40 :: rest => do
            let (children, rest) ← canonicalList fuel [] rest
            some (SExp.ofList children, rest)
        | _ => do
            let (length, rest) ← decimal fuel bytes
            let (payload, rest) ← splitExact length rest
            some (.atom ⟨payload.toByteArray⟩, rest)

  def canonicalList : Nat → List RivestSExp → List UInt8 →
      Option (List RivestSExp × List UInt8)
    | 0, _, _ => none
    | fuel + 1, acc, bytes =>
        match bytes with
        | 41 :: rest => some (acc, rest)
        | [] => none
        | _ => do
            let (head, rest) ← canonicalExpr fuel bytes
            canonicalList fuel (acc ++ [head]) rest
end

/-- Parse one complete canonical representation from arbitrary octets. Leading
zeros in lengths, whitespace, trailing bytes, and short payloads are rejected. -/
def parseCanonical? (bytes : Bytes) : Option RivestSExp := do
  let input := bytes.toList
  let (value, rest) ← canonicalExpr (input.length + 1) input
  if rest.isEmpty then some value else none

example : (parseCanonical? (Bytes.ofList [40, 51, 58, 97, 98, 99, 40, 48, 58, 41, 41])).isSome = true := by cbv

example : (parseCanonical? (Bytes.ofList [48, 49, 58, 97])).isNone = true := by cbv

end RivestSExp
end Silmaril.Formats
