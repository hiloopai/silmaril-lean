# Regular-expression presentations of acceptor sets

`Silmaril.Semantics.Accept.Regex` (namespace `Silmaril.Accept.Regex`, region `Semantics`,
Mathlib and CSLib only) presents languages by regular expressions. A language over an alphabet
`α` is Mathlib's `Language α` (`Set (List α)`), a Kleene algebra whose `0`, `1`, `+`, `*`,
`∗` and `^` are the regular operations; nothing here re-defines them.

## Stable API

### Derived language operations (`Defs`, laws in `Thms`)

| Name | Meaning |
| --- | --- |
| `letter a` | `{[a]}` |
| `letters p` | one-letter words whose letter satisfies `p` (a character class); `kstar_letters : (letters p)∗ = {w \| ∀ a ∈ w, p a}`, `isRegular_letters` (any alphabet) |
| `anyLetter` | every one-letter word (`.`) |
| `word w` | `{w}` |
| `opt L` | `1 + L` (`L?`) |
| `oneOrMore L` | `L * L∗` (`L+`); `one_add_oneOrMore`, `oneOrMore_eq_kstar_mul` |
| `rep L m n` | `{w \| ∃ k, m ≤ k ≤ n ∧ w ∈ L ^ k}` (`L{m,n}`); `rep_self`, `rep_le_kstar` |
| `repAtLeast L m` | `L ^ m * L∗` (`L{m,}`) |
| `Bytes.byte b`, `Bytes.range lo hi`, `Bytes.lit s` | byte languages (`Language UInt8`): one byte, the class `[lo-hi]`, the UTF-8 bytes of `s`; `Bytes.isRegular_range`, `Bytes.isRegular_lit` |

### Expressions with abstract leaves

`Expr ι α` has constructors `zero`, `one`, `char a`, `cls p` (Bool class), `leaf i`,
`plus`, `comp`, `star`. An environment `ρ : ι → Language α` gives each leaf an arbitrary
acceptor set.

| Name | Meaning |
| --- | --- |
| `Expr.eval ρ e` | the language of `e`; `eval_leaf : eval ρ (leaf i) = ρ i`, one `@[simp]` law per constructor |
| `Expr.leaves e` | the leaves occurring in `e` |
| `Expr.bind σ e` / `Expr.mapLeaves f e` | substitution / renaming of leaves |
| `Expr.sum`, `word`, `pow`, `opt`, `oneOrMore`, `rep`, `repAtLeast` | derived expressions; `eval_*` equate them with the language operations |
| `Expr.byteRange lo hi`, `Expr.byteLit s` | byte expressions; `eval_byteRange`, `eval_byteLit` |
| `Expr.ofRegex r` | a Mathlib `RegularExpression` as an expression; `eval_ofRegex`, `leaves_ofRegex` |
| `Expr.toRegex e` | `Expr Empty α → RegularExpression α` for `[Fintype α]` (noncomputable); `matches'_toRegex` |
| `Expr.matchB check e` | Bool matcher from leaf checkers (tries every split; for specification and tests) |

Laws:

* **Congruence:** `eval_congr` (only occurring leaves matter), `eval_of_leaves_eq_empty`,
  `eval_bind_congr` (equal leaf languages give equal languages in any context).
* **Monotonicity:** `eval_mono` (in occurring leaves), `eval_monotone`.
* **Substitution:** `eval_bind : eval ρ (bind σ e) = eval (fun i => eval ρ (σ i)) e`,
  `eval_mapLeaves`, `leaves_bind`, `bind_leaf`, `bind_bind`.
* **Checkers** (`Silmaril.Accept.Decides`): `decides_matchB` (leaf checkers that decide the
  leaf languages give a matcher that decides `eval ρ e`), `decides_matchB_ofBool`, and
  `decides_rmatch` for Mathlib's derivative matcher.

### Arbitrary leaves versus regular expressions

A leaf is *any* language: `exists_eval_leaf` shows a single leaf presents every language, so
an expression with leaves is a presentation, not a regularity certificate. Regularity
(`Language.IsRegular`, Mathlib) is only claimed under hypotheses:

* `isRegular_eval`: every leaf that occurs denotes a regular language;
* `isRegular_eval_of_leaves_eq_empty`: no leaf occurs (for instance `Expr Empty α`);
* `isRegular_iff_exists_expr` (`[Finite α]`): regular ⇔ the value of an `Expr Empty α`
  (CSLib's Kleene theorem `IsRegular.iff_regex`).

The closure proofs reuse CSLib's `IsRegular.add`/`mul`/`kstar`/`char`; a class `cls p` is
regular by an explicit three-state Mathlib `DFA`, even over an infinite alphabet.

Examples and regression tests: `Silmaril/Semantics/Accept/Regex/Examples.lean` (`[0-9]+`
over bytes with an exact characterization, a comma-separated list over an abstract item leaf,
substitution of `[0-9]+` for the leaf, monotonicity).

## Limitations

* `matchB` enumerates splits and is exponential in the worst case; it is a reference
  matcher, not an implementation. `rmatch` (Mathlib, derivatives) covers leaf-free Mathlib
  expressions without classes.
* No complement or intersection constructors; use `Set` operations on the evaluated
  languages (CSLib proves regular closure under them).
* `Expr.toRegex` needs a finite alphabet because a class becomes the union of its letters.
* No POSIX/PCRE semantics (submatches, lazy quantifiers, anchors, backreferences); these are
  formal-language expressions.
* Byte names use `Language UInt8`, the definition behind `Formats.Accept.ByteLang` (#256).
