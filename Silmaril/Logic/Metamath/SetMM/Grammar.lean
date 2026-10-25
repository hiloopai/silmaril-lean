module

public import Silmaril.Logic.Metamath.Grammar.Examples
public import Silmaril.Logic.Metamath.Model.Check
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The primitive grammar of set.mm over string symbols

The syntax axioms of set.mm used by its ZFC axioms (`wn`, `wi`, `wb`, `wa`,
`wo`, `wal`, `wex`, `cv`, `wceq`, `wcel`), as a grammar whose constants and
variables are the strings of the source file (`SetMM.grammar`). This is the
grammar of `Grammar.Examples.SetMM` without class abstraction, but with the
file's own symbols: flattening a tree assertion gives exactly the assertion the
checker (`Silmaril.Logic.Metamath.Verify.check`) builds from
`data/metamath/set-axioms.mm`, as tested in
`Silmaril.Logic.Metamath.SetMM.Regression`. Variables are strings, so there are
infinitely many of them, as cut admissibility and the lattice of theories
require.

The grammar is unambiguous by an LL certificate (`SetMM.unambiguous`), so
string theorems of the flattened axioms are tree theorems.

The tree notation `wi`, `wal`, `weq`, ... builds formulas, and the floating
hypotheses `fw` and `fs` declare formula and set variables.
-/

namespace Silmaril.Logic.Metamath.SetMM

open Silmaril.Logic.Metamath Grammar

/-- Labels of the syntax axioms. -/
inductive L
  | wn | wi | wb | wa | wo | wal | wex | cv | wceq | wcel
  deriving DecidableEq, Repr

/-- All labels. -/
def L.all : List L := [.wn, .wi, .wb, .wa, .wo, .wal, .wex, .cv, .wceq, .wcel]

instance : Fintype L := .ofList L.all (by intro l; cases l <;> simp [L.all])

/-- The source label of a syntax axiom. -/
def L.label : L → String
  | .wn => "wn" | .wi => "wi" | .wb => "wb" | .wa => "wa" | .wo => "wo" | .wal => "wal"
  | .wex => "wex" | .cv => "cv" | .wceq => "wceq" | .wcel => "wcel"

/-- A constant. -/
abbrev c (s : String) : Sym String String := .const s

/-- A variable. -/
abbrev v (s : String) : Sym String String := .var s

/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule String String
  | .wn => Examples.rule "wff" [("wff", "ph")] [c "-.", v "ph"]
  | .wi => Examples.rule "wff" [("wff", "ph"), ("wff", "ps")]
      [c "(", v "ph", c "->", v "ps", c ")"]
  | .wb => Examples.rule "wff" [("wff", "ph"), ("wff", "ps")]
      [c "(", v "ph", c "<->", v "ps", c ")"]
  | .wa => Examples.rule "wff" [("wff", "ph"), ("wff", "ps")]
      [c "(", v "ph", c "/\\", v "ps", c ")"]
  | .wo => Examples.rule "wff" [("wff", "ph"), ("wff", "ps")]
      [c "(", v "ph", c "\\/", v "ps", c ")"]
  | .wal => Examples.rule "wff" [("wff", "ph"), ("setvar", "x")] [c "A.", v "x", v "ph"]
  | .wex => Examples.rule "wff" [("wff", "ph"), ("setvar", "x")] [c "E.", v "x", v "ph"]
  | .cv => Examples.rule "class" [("setvar", "x")] [v "x"]
  | .wceq => Examples.rule "wff" [("class", "A"), ("class", "B")] [v "A", c "=", v "B"]
  | .wcel => Examples.rule "wff" [("class", "A"), ("class", "B")] [v "A", c "e.", v "B"]

/-- The syntax typecodes `wff`, `setvar` and `class`. -/
def IsSort (s : String) : Bool := s == "wff" || s == "setvar" || s == "class"

/-- The grammar; `|-` is read as `wff`. -/
def grammar : Grammar L String String where
  sorts := {s | IsSort s}
  prov s := if s = "|-" then some "wff" else none
  rule := rules
  rule_tc l := by cases l <;> decide
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by
    by_cases hc : c = "|-"
    · simp only [hc, ↓reduceIte] at h
      cases h
      exact rfl
    · simp only [hc, ↓reduceIte] at h
      cases h
  prov_not_sort {c s} h := by
    by_cases hc : c = "|-"
    · subst hc
      exact fun h => absurd h (by decide)
    · simp only [hc, ↓reduceIte] at h
      cases h

instance : DecidablePred (· ∈ grammar.sorts) := fun s => inferInstanceAs (Decidable (IsSort s))

@[simp] theorem prov_turnstile : grammar.prov "|-" = some "wff" := rfl

/-- The first-symbol classes of each sort. -/
def first (s : String) : List (String ⊕ String) :=
  if s = "wff" then
    [.inr "wff", .inl "-.", .inl "(", .inl "A.", .inl "E.", .inr "class", .inr "setvar"]
  else if s = "class" then [.inr "class", .inr "setvar"]
  else [.inr s]

theorem llCert : LLCert grammar first := by
  refine (llCert_iff grammar first).2 ⟨fun s => ?_, by decide, by decide, by decide⟩
  unfold first
  split_ifs with h₁ h₂
  · subst h₁; decide
  · subst h₂; decide
  · exact List.mem_singleton_self _

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

/-! ## Tree notation -/

/-- `-. t`. -/
abbrev wn (t : Tree L String) : Tree L String := .node .wn [t]
/-- `( t -> u )`. -/
abbrev wi (t u : Tree L String) : Tree L String := .node .wi [t, u]
/-- `( t <-> u )`. -/
abbrev wb (t u : Tree L String) : Tree L String := .node .wb [t, u]
/-- `( t /\ u )`. -/
abbrev wa (t u : Tree L String) : Tree L String := .node .wa [t, u]
/-- `( t \/ u )`. -/
abbrev wo (t u : Tree L String) : Tree L String := .node .wo [t, u]
/-- `A. x t`. -/
abbrev wal (x : String) (t : Tree L String) : Tree L String := .node .wal [t, .var x]
/-- `E. x t`. -/
abbrev wex (x : String) (t : Tree L String) : Tree L String := .node .wex [t, .var x]
/-- The set variable `x` as a class. -/
abbrev cv (x : String) : Tree L String := .node .cv [.var x]
/-- `x = y` for set variables. -/
abbrev weq (x y : String) : Tree L String := .node .wceq [cv x, cv y]
/-- `x e. y` for set variables. -/
abbrev wel (x y : String) : Tree L String := .node .wcel [cv x, cv y]
/-- A formula variable. -/
abbrev wv (ph : String) : Tree L String := .var ph
/-- The floating hypothesis `wff ph`. -/
abbrev fw (ph : String) : THyp L String String := .float "wff" ph
/-- The floating hypothesis `setvar x`. -/
abbrev fs (x : String) : THyp L String String := .float "setvar" x
/-- `|- t`. -/
abbrev pf (t : Tree L String) : TExpr L String String := ⟨"|-", t⟩

end Silmaril.Logic.Metamath.SetMM
