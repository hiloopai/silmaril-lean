module

public import Silmaril.Logic.Metamath.SecondOrder.Data
public import Silmaril.Logic.Metamath.Grammar.Unambiguous

@[expose] public section

/-!
# The language of second-order arithmetic

The grammar of `data/metamath/z2.mm` (`SecondOrder.grammar`): number variables
(`nvar`), set variables (`svar`), terms built from number variables, `0`,
`S`, `+` and `x.`, and formulas built from `t = u`, `t < u`, `t e. X` and
`X = Y` with `-.`, `->`, `<->`, `/\` and quantifiers over numbers and over
sets. Terms are bracketed with `[ ]` and formulas with `( )`, and the grammar
has an LL certificate, so it is unambiguous (`SecondOrder.unambiguous`).

Formula classes are provable typecodes read as `wff`: `bnd` (bounded),
`sig1` (Σ⁰₁), `pi1` (Π⁰₁) and `arith` (arithmetical), next to `|-`. A class
typecode could not be a syntax typecode with its own constructors: a
coercion `wff ::= ph0` from a class `bwff` that reuses the connectives makes
`( ph0 -> ps0 )` a formula in two ways, as the coercion of a bounded
implication and as an implication of coerced formulas
(`SecondOrder.Coercion.not_unambiguous`). The class of a formula is instead a
judgment derived by the formation rules of the database (for instance
`bnd-i : bnd ph, bnd ps ⊢ bnd ( ph -> ps )`), and coercions between classes
are the rules `sig1-bnd`, `pi1-bnd`, `arith-sig1` and `arith-pi1`.
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Silmaril.Logic.Metamath Grammar

/-- The grammar of `z2.mm`: `|-`, `bnd`, `sig1`, `pi1` and `arith` are read as
`wff`. -/
def grammar : Grammar L C V where
  sorts := {c | isSort c}
  prov := provOf
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h <;> rfl
  prov_not_sort {c s} h := by cases c <;> cases h <;> decide

instance : DecidablePred (· ∈ grammar.sorts) := fun c => inferInstanceAs (Decidable (isSort c))

open C in
/-- The symbol classes that can begin a string of each sort. -/
def first : C → List (C ⊕ C)
  | .term => [.inr term, .inr nvar, .inl zero, .inl succ, .inl lb]
  | .wff => [.inr wff, .inl not, .inl lp, .inl all, .inl ex, .inr svar, .inr term, .inr nvar,
      .inl zero, .inl succ, .inl lb]
  | c => [.inr c]

/-- The LL certificate of the grammar. -/
theorem llCert : LLCert grammar first := by decide

/-- The grammar of second-order arithmetic is unambiguous. -/
theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

theorem mem_sorts_iff {c : C} : c ∈ grammar.sorts ↔ c = .wff ∨ c = .term ∨ c = .nvar ∨ c = .svar :=
  by cases c <;> decide

end Silmaril.Logic.Metamath.SecondOrder
