module

public import Silmaril.Logic.Metamath.Syntax

@[expose] public section

/-!
# Raw Metamath statements

The statement-level abstract syntax of a `.mm` file, before scoping and
checking. It follows the Metamath specification (Megill and Wheeler,
*Metamath*, 2nd ed., §4.1): math symbols and labels are strings of printable
ASCII without whitespace or `$`; keywords are the two-character `$` tokens.
Comments are kept so that the text round-trips. A `$[ file $]` inclusion is
recorded rather than resolved; resolution is a separate, explicit step.

Proofs are kept in their textual form. A normal proof is a list of labels,
where `?` marks an unknown step. A compressed proof lists the labels in its
parenthesized header and the concatenated letter block.
-/

namespace Silmaril.Logic.Metamath.Text

/-- The body of a `$p` statement's proof. -/
inductive ProofText where
  /-- A normal proof: labels in reverse Polish order, `?` for unknown steps. -/
  | normal (steps : List String)
  /-- A compressed proof: `( labels ) letters`, with the letter block's
  whitespace removed. -/
  | compressed (labels : List String) (letters : String)
  deriving DecidableEq, Repr, Inhabited

/-- One statement of a Metamath source file. -/
inductive Stmt where
  /-- `$( text $)`. -/
  | comment (text : String)
  /-- `$c c₁ … cₙ $.` -/
  | constants (symbols : List String)
  /-- `$v v₁ … vₙ $.` -/
  | variables (symbols : List String)
  /-- `$d v₁ … vₙ $.` -/
  | disjoint (symbols : List String)
  /-- `label $f typecode variable $.` -/
  | floating (label typecode var : String)
  /-- `label $e typecode s₁ … sₙ $.` -/
  | essential (label typecode : String) (body : List String)
  /-- `label $a typecode s₁ … sₙ $.` -/
  | axiom (label typecode : String) (body : List String)
  /-- `label $p typecode s₁ … sₙ $= proof $.` -/
  | provable (label typecode : String) (body : List String) (proof : ProofText)
  /-- `${` -/
  | openScope
  /-- `$}` -/
  | closeScope
  /-- `$[ file $]` -/
  | include (file : String)
  deriving DecidableEq, Repr, Inhabited

/-- A Metamath source file as a statement sequence. -/
abbrev Source := List Stmt

end Silmaril.Logic.Metamath.Text
