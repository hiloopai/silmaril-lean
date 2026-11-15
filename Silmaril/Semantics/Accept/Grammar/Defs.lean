module

public import Mathlib.Computability.ContextFreeGrammar
public import Silmaril.Semantics.Accept.Defs

/-!
# Context-free grammars as presentations of acceptor sets

A context-free grammar is Mathlib's `ContextFreeGrammar T` (terminals `T`, nonterminals
`g.NT : Type`, a finite set of rules); its language `g.language : Language T` is the set of
terminal words derivable from the initial nonterminal, and `Language T` is `Set (List T)`.
Nothing here redefines grammars, derivations or languages. This file only fixes the vocabulary
that connects a grammar to the acceptor vocabulary of `Silmaril.Semantics.Accept.Defs`.

## Grammars as presentations

* `Grammar.lang g : Set (List T)`: `g.language` read as an acceptor set (`Language T` is a
  type synonym of `Set (List T)` that does not carry the `Set` instances such as `⊆`).

For a grammar `g` and an acceptor set `L : Set (List T)`:

* `Grammar.Sound g L`: `lang g ⊆ L` (every derivable word is in `L`);
* `Grammar.Complete g L`: `L ⊆ lang g` (every word of `L` is derivable);
* `Grammar.Presents g L`: `lang g = L` (both).

Bool checkers are related to grammars with the existing `Accept.Sound`, `Accept.Complete`
and `Accept.Decides` applied to `lang g` (`Thms`).

* `Grammar.sentential g`: the sentential forms `{s | g.Generates s}`; the language is its
  preimage under `List.map Symbol.terminal` (`Thms`), i.e. existential acceptance of the
  deterministic runner that embeds a word as a string of terminals.

## Small grammars

* `Grammar.empty`: no rules; its language is empty.
* `Grammar.word w`: the single rule `S → w`; its language is `{w}`.
* `Grammar.rename g f`: the nonterminals renamed along `f`; for injective `f` the language
  is unchanged.
* `Grammar.union g₁ g₂`: a fresh start symbol with one rule into each grammar; its language
  is `lang g₁ ∪ lang g₂`.
* `Grammar.nested x y`: the rules `S → x S y` and `S → ε`; its language is
  `{xⁿ yⁿ | n ∈ ℕ}` (`Grammar.nestedLang x y`). With `x` an opening and `y` a closing
  bracket this is the language of properly nested (not arbitrary balanced) brackets.
* `Grammar.nestedCheck x y`: a Bool checker for `nestedLang x y` (`Thms` proves it decides
  the grammar's language).
-/

@[expose] public section

namespace Silmaril.Accept.Grammar

universe u

variable {T : Type u}

/-! ## Grammars as presentations -/

/-- The language of `g` as an acceptor set: Mathlib's `g.language`, read as a `Set (List T)`
(`Language T` is a type synonym of `Set (List T)` without its set instances). -/
def lang (g : ContextFreeGrammar T) : Set (List T) := g.language

/-- The sentential forms of `g`: the strings derivable from its initial nonterminal. -/
def sentential (g : ContextFreeGrammar T) : Set (List (Symbol T g.NT)) := {s | g.Generates s}

/-- `g` is sound for `L`: every word `g` derives lies in `L`. -/
def Sound (g : ContextFreeGrammar T) (L : Set (List T)) : Prop := lang g ⊆ L

/-- `g` is complete for `L`: `g` derives every word of `L`. -/
def Complete (g : ContextFreeGrammar T) (L : Set (List T)) : Prop := L ⊆ lang g

/-- `g` presents `L`: its language is exactly `L`. -/
def Presents (g : ContextFreeGrammar T) (L : Set (List T)) : Prop := lang g = L

/-! ## Small grammars -/

/-- The grammar with one nonterminal and no rules. -/
@[reducible] def empty : ContextFreeGrammar T where
  NT := Unit
  initial := ()
  rules := ∅

/-- The grammar with one nonterminal `S` and the single rule `S → w`. -/
@[reducible] def word (w : List T) : ContextFreeGrammar T where
  NT := Unit
  initial := ()
  rules := {⟨(), w.map Symbol.terminal⟩}

/-! ## Renaming nonterminals and union -/

/-- Rename the nonterminal of a symbol; terminals are unchanged. -/
def mapSym {N N' : Type} (f : N → N') : Symbol T N → Symbol T N'
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (f n)

/-- Rename the nonterminals of a rule. -/
def mapRule {N N' : Type} (f : N → N') (r : ContextFreeRule T N) : ContextFreeRule T N' :=
  ⟨f r.input, r.output.map (mapSym f)⟩

open Classical in
/-- Rename the nonterminals of `g` along `f`. For injective `f` the language is unchanged
(`Thms.lang_rename`). Noncomputable: the rule set is a classical `Finset.image`. -/
@[reducible] noncomputable def rename (g : ContextFreeGrammar T) {N : Type} (f : g.NT → N) :
    ContextFreeGrammar T where
  NT := N
  initial := f g.initial
  rules := g.rules.image (mapRule f)

open Classical in
/-- The union grammar: a fresh initial nonterminal `none` with the rules `none → S₁` and
`none → S₂`, and the rules of `g₁` and `g₂` on disjoint copies of their nonterminals.
Noncomputable: the rule set is a classical `Finset` union. -/
@[reducible] noncomputable def union (g₁ g₂ : ContextFreeGrammar T) : ContextFreeGrammar T where
  NT := Option (g₁.NT ⊕ g₂.NT)
  initial := none
  rules :=
    insert ⟨none, [.nonterminal (some (.inl g₁.initial))]⟩
      (insert ⟨none, [.nonterminal (some (.inr g₂.initial))]⟩
        (g₁.rules.image (mapRule (some ∘ Sum.inl)) ∪ g₂.rules.image (mapRule (some ∘ Sum.inr))))

/-- The rule `S → x S y`. -/
def nestedStep (x y : T) : ContextFreeRule T Unit :=
  ⟨(), [.terminal x, .nonterminal (), .terminal y]⟩

/-- The rule `S → ε`. -/
def nestedStop : ContextFreeRule T Unit := ⟨(), []⟩

/-- The grammar `S → x S y | ε`. -/
@[reducible] def nested (x y : T) : ContextFreeGrammar T where
  NT := Unit
  initial := ()
  rules := Finset.cons (nestedStep x y) {nestedStop} (by simp [nestedStep, nestedStop])

/-- The words `xⁿ yⁿ`. -/
def nestedLang (x y : T) : Set (List T) :=
  {w | ∃ n, w = List.replicate n x ++ List.replicate n y}

/-- A Bool checker for `xⁿ yⁿ`: a word of length `m` must be `x^(m/2) y^(m/2)`. -/
def nestedCheck [DecidableEq T] (x y : T) (w : List T) : Bool :=
  decide (w = List.replicate (w.length / 2) x ++ List.replicate (w.length / 2) y)

end Silmaril.Accept.Grammar
