module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.ObjectOrder

open scoped Prod.Lex

/-- STRING<-L along the character-list and natural-offset path reached by STRING<. -/
def stringLessIndex : ByteString → ByteString → Nat → Option Nat
  | [], [], _ => none
  | [], _ :: _, i => some i
  | _ :: _, [], _ => none
  | a :: as, b :: bs, i =>
    if a = b then stringLessIndex as bs (i + 1) else if a < b then some i else none

def stringLeIndex (x y : ByteString) : Option Nat :=
  if x = y then some x.length else stringLessIndex x y 0

/-- Non-NIL result of SYMBOL< on symbols, comparing name before home package. -/
def symbolLess (x y : Symbol) : Bool :=
  (stringLessIndex x.spelling y.spelling 0).isSome ||
    (decide (x.spelling = y.spelling) && (stringLessIndex x.package y.package 0).isSome)

/-- The ALPHORDER branches reachable from LEXORDER on standard atoms.
The final case is unreachable for two standard atoms. -/
def alphorder : Object → Object → Bool
  | .rational x, .rational y => decide (x ≤ y)
  | .rational _, _ => true
  | _, .rational _ => false
  | .complexRational r i _, .complexRational s j _ => decide (r < s ∨ r = s ∧ i ≤ j)
  | .complexRational .., _ => true
  | _, .complexRational .. => false
  | .character x, .character y => decide (x ≤ y)
  | .character _, _ => true
  | _, .character _ => false
  | .string x, .string y => (stringLeIndex x y).isSome
  | .string _, _ => true
  | _, .string _ => false
  | .symbol x, .symbol y => !symbolLess y x
  | .symbol _, _ => true
  | _, .symbol _ => false
  | .cons .., .cons .. => false

/-- Represent the atom cases of ACL2 ALPHORDER and a final, larger cons marker.
Empty components are padding for categories that never consult them. -/
abbrev Key := Nat ×ₗ (Rat ×ₗ (Rat ×ₗ (ByteString ×ₗ ByteString)))

def key : Object → Key
  | .rational a => make 0 a 0 [] []
  | .complexRational a b _ => make 1 a b [] []
  | .character c => make 2 0 0 [c] []
  | .string s => make 3 0 0 s []
  | .symbol s => make 4 0 0 s.spelling s.package
  | .cons .. => make 5 0 0 [] []
where
  make (tag : Nat) (real imag : Rat) (spelling package : ByteString) : Key :=
    toLex (tag, toLex (real, toLex (imag, toLex (spelling, package))))

/-- Preorder traversal. The first token distinguishes a cons from every atom.
The tail parameter permits rewriting the head comparison under any continuation. -/
def encode : Object → List Key → List Key
  | x@(.cons a b), tail => key x :: encode a (encode b tail)
  | x, tail => key x :: tail

scoped instance : DecidableLT ByteString := fun x y =>
  inferInstanceAs (Decidable (List.Lex (· < ·) x y))

scoped instance : DecidableEq Key :=
  inferInstanceAs (DecidableEq (Nat × (Rat × (Rat × (ByteString × ByteString)))))

scoped instance {α β : Type} [LT α] [LT β] [DecidableEq α] [DecidableLT α] [DecidableLT β] :
    DecidableLT (α ×ₗ β) := Prod.Lex.decidable _ _

scoped instance : DecidableLT (List Key) := fun x y =>
  inferInstanceAs (Decidable (List.Lex (· < ·) x y))

/-- The strict ACL2 order ACL2::<<, observed using the non-NIL convention. -/
def before (x y : Object) : Bool := decide (encode x [] < encode y [])

/-- The non-NIL projection of stock ACL2 LEXORDER. -/
def lexorder (x y : Object) : Bool := !before y x

end Silmaril.Logic.ACL2.Standard.ObjectOrder
