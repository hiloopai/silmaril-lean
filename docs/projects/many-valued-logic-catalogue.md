# Many-valued logic catalogue

The inventory follows [English Wikipedia, *Many-valued logic*, revision 1387866146
(25 November 2026)](https://en.wikipedia.org/w/index.php?title=Many-valued_logic&oldid=1387866146).
The definitions use arithmetic and order formulas. The reference matrix below
covers the ordered-chain examples in this increment.

Import `Silmaril.Logic.ManyValuedCatalogue.Thms`. All names in the matrix are
relative to `Silmaril.Logic.ManyValuedCatalogue`.

| Article example | Carrier and operations | Checked relationships |
| --- | --- | --- |
| Gödel Gₖ, including G₃ and G₄ | `Grid n = Fin (n + 2)`, where `k = n + 2`. Use `Goedel.and`, `or`, `imp`, `neg`, and `designated`. For G₃ use `Grid 1` and for G₄ use `Grid 2`. | `Goedel.residuation` identifies the residual of minimum. `UnitInterval.ofGrid_le_iff`, `ofGrid_top`, `ofGrid_bot`, `ofGrid_and`, `ofGrid_or`, `ofGrid_goedelImp`, and `ofGrid_goedelNeg` verify the finite chain's inclusion in the unit interval. |
| Gödel G∞ | The same `Goedel` operations on `UnitInterval ℝ`. | `Goedel.residuation` and `Goedel.neg_eq` identify the Heyting residual and the negation that tests the bottom value. The article also discusses axiomatization and completeness. |
| Łukasiewicz Lᵥ, including L₃ | `Grid n`, where `v = n + 2`, with `Grid.lukNeg`, `lukImp`, and `lukAnd`. Use `Grid 1` for L₃. Only the top value is designated. | `UnitInterval.ofGrid_lukNeg`, `ofGrid_lukImp`, and `ofGrid_lukAnd` verify the numerical interpretation `i/(n+1)` and preservation of all three operations. |
| Rational Lℵ₀ and real L∞ | `UnitInterval ℚ` and `UnitInterval ℝ` with `UnitInterval.lukNeg`, `lukImp`, and `lukAnd`. Only the top value is designated. | `luk_residuation` and `luk_neg_eq` connect the operations. The `ofRat` map reflects order and preserves bounds, negation, implication, and strong conjunction. The article's equality of tautology sets is a separate metatheorem. |
| Product Π | `UnitInterval ℝ` with `UnitInterval.prodAnd`, `prodImp`, `prodNeg`, and `prodMeet`. The named falsity constant is bottom. | `prod_residuation` verifies the piecewise residual. `prod_neg_eq` compares residual negations. `prod_meet_eq` proves that `x · (x → y)` gives minimum, while strong conjunction multiplies the degrees. |

The unit interval reuses Mathlib's order on a closed interval. The finite grid
uses integer indices and has two endpoints even at `n = 0`. A degree such as
1/2 has Łukasiewicz strong conjunction 0 with itself, product strong
conjunction 1/4, and meet 1/2.

## Sources

SHA-256 identifies the fetched HTML artifact for each cited page.

| Source and locator | SHA-256 |
| --- | --- |
| Wikipedia contributors, [*Many-valued logic*, revision 1387866146, Examples](https://en.wikipedia.org/w/index.php?title=Many-valued_logic&oldid=1387866146#Examples), 25 November 2026 | `4672835704f69c91d551f998c0d295400571ff38cbea79aff59668017af6c4a9` |
| Petr Cintula, Christian G. Fermüller, and Carles Noguera, [*Fuzzy Logic*, §1](https://plato.stanford.edu/entries/logic-fuzzy/#FuzzConnBaseTNorm), Stanford Encyclopedia of Philosophy, 11 November 2021 revision | `dda00ba425fc31648f9553e88d53845383c496edd740d9e38f39952213c041c7` |
| João Marcos, Adam Přenosil, and Paul Égré, [*Many-Valued Logic*, §§2.1 and 3.2.2](https://plato.stanford.edu/entries/logic-manyvalued/), Stanford Encyclopedia of Philosophy, 29 September 2026 revision | `5a549597b7c78fe2d5d3252f0bc4bcf0e1e48afeff6314e1f05a9dd505773169` |

Build the public header and its proof modules with
`lake build --wfail +Silmaril.Logic.ManyValuedCatalogue.Thms`.
