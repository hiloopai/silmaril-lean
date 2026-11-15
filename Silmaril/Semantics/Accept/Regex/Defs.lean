module

public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Fintype.Basic

/-!
# Regular-expression presentations of acceptor sets

A language over an alphabet `α` is Mathlib's `Language α` (`Set (List α)`, no wrapper). Its
regular operations are Mathlib's: `0` (empty), `1` (only the empty word), `+` (union), `*`
(concatenation), `∗` (Kleene star) and `^` (powers); `Language α` is a Mathlib
`KleeneAlgebra`. This file adds the usual derived operations and an expression syntax whose
leaves are *arbitrary* acceptor sets.

## Derived operations on languages (`Silmaril.Accept.Regex`)

* `letter a = {[a]}`, `letters p` (one-letter words whose letter satisfies `p`, a character
  class), `anyLetter`, `word w = {w}`;
* `opt L = 1 + L` (`L?`), `oneOrMore L = L * L∗` (`L+`), `rep L m n` (`L{m,n}`) and
  `repAtLeast L m = L ^ m * L∗` (`L{m,}`).

## Expressions with abstract leaves (`Regex.Expr ι α`)

`Expr ι α` is the syntax of regular expressions over letters `α` (with character classes)
extended by *leaves* `leaf i`, `i : ι`. An environment `ρ : ι → Language α` interprets each
leaf by any acceptor set, and `Expr.eval ρ` interprets the operators by Mathlib's. Leaves are
not assumed regular: `eval ρ (leaf i) = ρ i` is whatever language `ρ` supplies. Only
expressions without leaves (`Expr Empty α`, or with every used leaf regular) present regular
languages (`Thms`: `isRegular_eval`); `Expr.toRegex` turns a leaf-free expression into a
Mathlib `RegularExpression` over a finite alphabet.

* `Expr.leaves e`: the leaves that occur in `e` (evaluation depends only on them);
* `Expr.bind σ e`: substitute the expression `σ i` for each leaf `i` (evaluates
  compositionally, `Thms`: `eval_bind`), and `Expr.mapLeaves f` (renaming);
* `Expr.ofRegex r`: a Mathlib `RegularExpression` as a leaf-free expression;
* `Expr.matchB check e`: a Bool matcher from Bool checkers for the leaves. It decides
  `eval (fun i => Accept.ofBool (check i)) e` (`Thms`: `decides_matchB`); it tries every split
  and is meant for specification and small tests, not for performance.

## Bytes (`Silmaril.Accept.Regex.Bytes`)

Byte languages are `Language UInt8`. `Bytes.range lo hi` is the class of bytes in
`[lo, hi]`, `Bytes.lit s` the UTF-8 encoding of a string, and `Expr.byteRange`/`Expr.byteLit`
the corresponding leaf-free expressions.
-/

@[expose] public section

namespace Silmaril.Accept.Regex

open scoped Computability

universe u v w

variable {α : Type u}

/-! ## Derived operations on languages -/

/-- The one-letter word `[a]`. -/
def letter (a : α) : Language α := {[a]}

/-- A character class: the one-letter words whose letter satisfies `p`. -/
def letters (p : α → Prop) : Language α := {w | ∃ a, p a ∧ w = [a]}

/-- Every one-letter word (`.` in regex notation). -/
def anyLetter : Language α := letters fun _ => True

/-- The language of the single word `w`. -/
def word (w : List α) : Language α := {w}

/-- Optional: `L?`, the empty word or a word of `L`. -/
def opt (L : Language α) : Language α := 1 + L

/-- One or more: `L+`. -/
def oneOrMore (L : Language α) : Language α := L * L∗

/-- Bounded repetition `L{m,n}`: concatenations of between `m` and `n` words of `L`. -/
def rep (L : Language α) (m n : ℕ) : Language α := {w | ∃ k, m ≤ k ∧ k ≤ n ∧ w ∈ L ^ k}

/-- At least `m` repetitions: `L{m,}`. -/
def repAtLeast (L : Language α) (m : ℕ) : Language α := L ^ m * L∗

/-! ## Expressions with abstract leaves -/

/-- Regular-expression syntax over letters `α`, with character classes `cls p` and leaves
`leaf i` that an environment interprets by arbitrary languages. -/
inductive Expr (ι : Type v) (α : Type u) : Type (max u v)
  /-- The empty language. -/
  | zero : Expr ι α
  /-- The language of the empty word. -/
  | one : Expr ι α
  /-- A single letter. -/
  | char (a : α) : Expr ι α
  /-- A character class given by a Bool predicate. -/
  | cls (p : α → Bool) : Expr ι α
  /-- An abstract leaf. -/
  | leaf (i : ι) : Expr ι α
  /-- Union. -/
  | plus (e f : Expr ι α) : Expr ι α
  /-- Concatenation. -/
  | comp (e f : Expr ι α) : Expr ι α
  /-- Kleene star. -/
  | star (e : Expr ι α) : Expr ι α

namespace Expr

variable {ι : Type v} {κ : Type w}

/-- The language of an expression, given languages `ρ i` for its leaves. -/
def eval (ρ : ι → Language α) : Expr ι α → Language α
  | zero => 0
  | one => 1
  | char a => {[a]}
  | cls p => letters fun a => p a = true
  | leaf i => ρ i
  | plus e f => eval ρ e + eval ρ f
  | comp e f => eval ρ e * eval ρ f
  | star e => (eval ρ e)∗

/-- The leaves occurring in an expression. -/
def leaves : Expr ι α → Set ι
  | zero | one | char _ | cls _ => ∅
  | leaf i => {i}
  | plus e f | comp e f => leaves e ∪ leaves f
  | star e => leaves e

/-- Substitution: replace each leaf `i` by the expression `σ i`. -/
def bind (σ : ι → Expr κ α) : Expr ι α → Expr κ α
  | zero => zero
  | one => one
  | char a => char a
  | cls p => cls p
  | leaf i => σ i
  | plus e f => plus (bind σ e) (bind σ f)
  | comp e f => comp (bind σ e) (bind σ f)
  | star e => star (bind σ e)

/-- Rename the leaves. -/
def mapLeaves (f : ι → κ) (e : Expr ι α) : Expr κ α := bind (fun i => leaf (f i)) e

/-- A Mathlib regular expression as a leaf-free expression. -/
def ofRegex : RegularExpression α → Expr ι α
  | .zero => zero
  | .epsilon => one
  | .char a => char a
  | .plus r s => plus (ofRegex r) (ofRegex s)
  | .comp r s => comp (ofRegex r) (ofRegex s)
  | .star r => star (ofRegex r)

/-- The union of a list of expressions (`zero` for the empty list). -/
def sum : List (Expr ι α) → Expr ι α
  | [] => zero
  | [e] => e
  | e :: es => plus e (sum es)

/-- The word `w`, letter by letter. -/
def word : List α → Expr ι α
  | [] => one
  | a :: w => comp (char a) (word w)

/-- `e ^ n`: `n` concatenated copies of `e`. -/
def pow (e : Expr ι α) : ℕ → Expr ι α
  | 0 => one
  | n + 1 => comp e (pow e n)

/-- `e?`. -/
def opt (e : Expr ι α) : Expr ι α := plus one e

/-- `e+`. -/
def oneOrMore (e : Expr ι α) : Expr ι α := comp e (star e)

/-- `e{m,n}`: the union of the powers `e ^ k` for `m ≤ k ≤ n`. -/
def rep (e : Expr ι α) (m n : ℕ) : Expr ι α :=
  sum ((List.range (n + 1 - m)).map fun j => pow e (m + j))

/-- `e{m,}`. -/
def repAtLeast (e : Expr ι α) (m : ℕ) : Expr ι α := comp (pow e m) (star e)

/-- A leaf-free expression over a finite alphabet as a Mathlib regular expression. A class
becomes the union of its letters, enumerated by `Finset.toList` (hence noncomputable). -/
noncomputable def toRegex [Fintype α] : Expr Empty α → RegularExpression α
  | zero => 0
  | one => 1
  | char a => .char a
  | cls p => ((Finset.univ.filter fun a => p a = true).toList.map RegularExpression.char).sum
  | leaf i => i.elim
  | plus e f => toRegex e + toRegex f
  | comp e f => toRegex e * toRegex f
  | star e => (toRegex e).star

/-! ## A Bool matcher with Bool leaf checkers -/

/-- All ways to split `w` as `u ++ v`. -/
def splits (w : List α) : List (List α × List α) :=
  (List.range (w.length + 1)).map fun n => (w.take n, w.drop n)

/-- Star matching with fuel `k`: `w` is empty, or a nonempty prefix matches `m` and the rest
matches the star with one unit less fuel. Fuel `w.length` suffices (`Thms`). -/
def starB (m : List α → Bool) : ℕ → List α → Bool
  | 0, w => w.isEmpty
  | k + 1, w => w.isEmpty ||
      (List.range w.length).any fun n => m (w.take (n + 1)) && starB m k (w.drop (n + 1))

/-- A Bool matcher, given Bool checkers `check i` for the leaves. -/
def matchB [DecidableEq α] (check : ι → List α → Bool) : Expr ι α → List α → Bool
  | zero, _ => false
  | one, w => w.isEmpty
  | char a, w => w == [a]
  | cls p, w => match w with
    | [a] => p a
    | _ => false
  | leaf i, w => check i w
  | plus e f, w => matchB check e w || matchB check f w
  | comp e f, w => (splits w).any fun s => matchB check e s.1 && matchB check f s.2
  | star e, w => starB (matchB check e) w.length w

end Expr

/-! ## Bytes -/

namespace Bytes

/-- A single byte. -/
def byte (b : UInt8) : Language UInt8 := letter b

/-- The bytes in the closed range `[lo, hi]`. -/
def range (lo hi : UInt8) : Language UInt8 := letters fun b => lo ≤ b ∧ b ≤ hi

/-- The UTF-8 encoding of a string, as a one-word byte language. -/
def lit (s : String) : Language UInt8 := word s.toUTF8.toList

end Bytes

namespace Expr

variable {ι : Type v}

/-- The byte class `[lo-hi]`. -/
def byteRange (lo hi : UInt8) : Expr ι UInt8 := cls fun b => decide (lo ≤ b ∧ b ≤ hi)

/-- The UTF-8 bytes of a string, as a leaf-free expression. -/
def byteLit (s : String) : Expr ι UInt8 := word s.toUTF8.toList

end Expr

end Silmaril.Accept.Regex
