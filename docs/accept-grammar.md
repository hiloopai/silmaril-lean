# Acceptance: context-free grammars as presentations

`Silmaril.Semantics.Accept.Grammar` (namespace `Silmaril.Accept.Grammar`, region `Semantics`,
Mathlib only) connects Mathlib's context-free grammars to the generic acceptor vocabulary of
[acceptance](accept.md). It does not define grammars, derivations or languages: a grammar is
Mathlib's `ContextFreeGrammar T` (`Mathlib/Computability/ContextFreeGrammar.lean`), with
`Produces`, `Derives`, `Generates`, `language` and `Language.IsContextFree`.

`Language T` is a type synonym of `Set (List T)` that does not carry the `Set` instances
(`⊆`, `∪`, …), so `lang g` reads `g.language` as a `Set (List T)`, the carrier of
`Accept.Sound`/`Complete`/`Decides`. Statements about context-freeness take `L : Set (List T)`
and pass it to Mathlib's `Language.IsContextFree (T := T) L`.

## Stable API

### `Silmaril.Semantics.Accept.Grammar.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `lang g` | `g.language` as `Set (List T)`; `mem_lang : w ∈ lang g ↔ g.Generates (w.map Symbol.terminal)` |
| `sentential g` | `{s \| g.Generates s}`; `lang_eq_preimage`, `lang_eq_acceptsSome` (existential acceptance of `detRun (List.map Symbol.terminal)`) |
| `Grammar.Sound g L` | `lang g ⊆ L`: every derivable word is in `L`; `sound_iff` |
| `Grammar.Complete g L` | `L ⊆ lang g`: every word of `L` is derivable; `complete_iff` |
| `Grammar.Presents g L` | `lang g = L`; `presents_iff` (sound ∧ complete), `Presents.unique`, `Presents.congr`, `isContextFree_iff_exists_presents` |
| `empty` | no rules; `lang_empty : lang empty = ∅` |
| `word w` | `S → w`; `lang_word : lang (word w) = {w}` |
| `rename g f` | nonterminals renamed along `f`; `lang_rename : Injective f → lang (rename g f) = lang g` |
| `union g₁ g₂` | fresh start symbol with `S → S₁ \| S₂`; `lang_union : lang (union g₁ g₂) = lang g₁ ∪ lang g₂` |
| `nested x y` | `S → x S y \| ε`; `lang_nested : lang (nested x y) = nestedLang x y` |
| `nestedLang x y` | `{w \| ∃ n, w = replicate n x ++ replicate n y}` |
| `nestedCheck x y` | Bool checker (`DecidableEq T`); `decides_nestedCheck : Decides (nestedCheck x y) (lang (nested x y))` |
| `mapSym f`, `mapRule f` | renaming of symbols and rules (used by `rename` and `union`) |

Checkers against a grammar, with the existing `Accept` predicates:

| Name | Statement |
| --- | --- |
| `sound_lang_iff` | `Accept.Sound check (lang g) ↔ ∀ w, check w = true → g.Generates (w.map .terminal)` |
| `complete_lang_iff` | `Accept.Complete check (lang g) ↔ ∀ w, g.Generates (w.map .terminal) → check w = true` |
| `decides_lang_iff` / `decides_lang_iff_ofBool_eq` | pointwise iff / `ofBool check = lang g` |
| `decides_lang_congr` | deciding transports along `lang g = lang g'` |
| `Accept.Decides.of_presents` | `Decides check L → Presents g L → Decides check (lang g)` |
| `Accept.Decides.presents_iff` | given `Decides check (lang g)`: `Presents g L ↔ ofBool check = L` |
| `Accept.Sound.trans_grammar` | checker sound for `lang g`, `g` sound for `L` ⇒ checker sound for `L` |
| `Accept.Complete.trans_grammar` | checker complete for `lang g`, `g` complete for `L` ⇒ checker complete for `L` |
| `Accept.Decides.union_grammar` | checkers `c`, `c'` for `g`, `g'` ⇒ `fun w => c w \|\| c' w` decides `lang (union g g')` |
| `Accept.Decides.reverse_grammar` | `Decides check (lang g) → Decides (check ∘ List.reverse) (lang g.reverse)` (Mathlib's reversal) |

Context-freeness: `isContextFree_empty`, `isContextFree_singleton`, `isContextFree_union`
(not in Mathlib at the pinned version, which has only reversal), `isContextFree_nestedLang`,
`Presents.isContextFree`.

The proofs of `lang_empty`, `lang_word` and `lang_nested` are in
`Silmaril/Proofs/Semantics/Accept/Grammar/Basic.lean`; renaming and union go through one
embedding lemma in `…/Grammar/Embed.lean` (`derives_map_terminal_iff`: along an injective
renaming such that the target contains the renamed rules and has no other rules for renamed
nonterminals, a renamed string derives a terminal word exactly when the original does).

## Worked example

`Silmaril/Semantics/Accept/Grammar/Examples.lean` instantiates `nested` over bytes with
`(` = `40` and `)` = `41`:

* `lang_parens : lang parens = {w | ∃ n, w = replicate n 40 ++ replicate n 41}`: the grammar is
  both sound and complete for `(ⁿ )ⁿ`. Soundness is an invariant on sentential forms (every
  form is `xⁿ S yⁿ` or `xⁿ yⁿ`); completeness builds the derivation `S ⇒ⁿ xⁿ S yⁿ ⇒ xⁿ yⁿ`.
* `decides_parens : Decides parensCheck (lang parens)`, where `parensCheck w` tests
  `w = replicate (|w|/2) 40 ++ replicate (|w|/2) 41`.
* `decide` regression tests of the checker (accepting `[]`, `()`, `((()))`; rejecting `()()`,
  `)(`, `(()`), membership and non-membership in `lang parens` through the checker, a
  hand-written two-step derivation, a union with `word [0]` and its `||` checker, the reversed
  grammar and its checker, and context-freeness of `(ⁿ )ⁿ ∪ {0}`.

## Limitations

* `nested x y` presents properly *nested* brackets `(ⁿ )ⁿ`, not the Dyck language of all
  balanced bracket words (`()()` is rejected). No Dyck grammar is proved here.
* There is no general parser or membership decision procedure for grammars (no CYK, Earley or
  Chomsky normal form): `Decides` results are per grammar, through a hand-written checker and a
  proved language equality.
* Only empty, singleton, union and (from Mathlib) reversal closures are proved. Concatenation,
  Kleene star, homomorphic images and intersection with regular languages are not; closure
  under intersection and complement is false for context-free languages in general and is not
  stated.
* `rename` and `union` are `noncomputable` (their rule sets use classical `Finset` operations).
  They are presentations for proofs, not executable grammars; `nested`, `word` and `empty` are
  computable.
* Nonterminals live in `Type` (Mathlib's restriction); terminals may live in any universe.
* No relation to the regular-expression or automata developments of `Accept` is stated here
  (for example, that every regular language is context-free).
