# Acceptance: generic languages, checkers and verdicts

`Silmaril.Semantics.Accept` (namespace `Silmaril.Accept`, region `Semantics`, Mathlib only)
is the generic vocabulary for saying that a checker, a program or a runner *accepts* a set of
values. It contains nothing specific to WebAssembly, WIT or bytes; those developments
instantiate it.

A language over `α` is Mathlib's `Set α`: there is no wrapper type, so all of Mathlib's set
lattice, images and preimages apply directly.

## Stable API

These names are intended for downstream integration; changes go through review.

### `Silmaril.Semantics.Accept.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `ofBool check` | `{a \| check a = true}` |
| `Sound check L` | `∀ a, check a = true → a ∈ L` |
| `Complete check L` | `∀ a, a ∈ L → check a = true` |
| `Decides check L` | `∀ a, check a = true ↔ a ∈ L`; `decides_iff` (sound ∧ complete), `decides_iff_ofBool_eq` |
| `checker L` | `decide (· ∈ L)`; `decides_checker` |
| `acceptsSome run acc` | some outcome of `run a` is in `acc` (existential acceptance) |
| `acceptsAll run acc` | every outcome of `run a` is in `acc` (vacuous with no outcome) |
| `rejectsSome run rej` | some outcome of `run a` is in `rej` |
| `neverRejects run rej` | no outcome of `run a` is in `rej` (universal safety) |
| `detRun f` | the runner `fun a => {f a}` of a total function |
| `upTo size n L` | members of `L` with `size a ≤ n` |

Key laws: `compl_rejectsSome` (never-rejection is the complement of *some* rejection, not of
acceptance), `compl_acceptsSome`, `acceptsAll_subset_neverRejects` (needs disjoint verdicts),
`acceptsAll_subset_acceptsSome` (needs every input to have an outcome),
`neverRejects_not_subset_acceptsSome` (an input with no outcome separates them), the
deterministic collapse `acceptsSome_detRun`/`acceptsAll_detRun`/`neverRejects_detRun`,
`Decides.and`/`or`/`not`/`comp`/`upTo`, and `iUnion_upTo`/`eq_iff_upTo_eq` for size slices.

### `Silmaril.Semantics.Accept.Order.Defs` / `Thms`

Programs of any carrier `X`, compared by `lang : X → Set α`.

| Name | Meaning |
| --- | --- |
| `LangPre lang` | type synonym of `X`, **preorder** `x ≤ y ↔ lang x ⊆ lang y`; `LangPre.of`, `.val`, `.toLang` |
| `LangPre.map f hf` / `LangPre.embed f hinj hf` | monotone map / order embedding along a language-preserving (injective) `f` |
| `LangPre.subtypeEmb p` | sub-carrier `Subtype p` as an order embedding |
| `langSum l₁ l₂`, `inlEmb`, `inrEmb` | two shapes `X ⊕ Y` in one preorder; inclusions are order embeddings |
| `langSigma lang`, `sigmaEmb lang i` | a family of shapes `Σ i, X i` |
| `RespectsLang s lang` | class: `s x y → lang x = lang y` |
| `LangQuot s lang` | `Quotient s` with the descended language; a **preorder** (`mk_le_mk_iff`) |
| `LangQuot.toLangEq` | monotone, order-reflecting, surjective comparison with `LangEq`; injective iff `s` identifies all equal-language programs (`toLangEq_injective_iff`) |
| `LangEq lang` | `Quotient (Setoid.ker lang)`, a **partial order** (`mk_eq_mk_iff : mk x = mk y ↔ lang x = lang y`) |
| `LangEq.toSetEmb`, `LangEq.rangeIso`, `LangEq.antisymmIso` | `LangEq lang ↪o Set α`, `≃o Set.range lang`, `≃o Antisymmetrization (LangPre lang) (· ≤ ·)` |

Shapes are disjoint as programs, but not up to language: `inl_antisymmRel_inr_iff` and
`LangEq.mk_inl_eq_mk_inr_iff` show that a left and a right program are identified exactly when
their languages agree. A supplied equivalence must be proved to respect the language
(`RespectsLang`) before its quotient carries an order.

Examples: `Silmaril/Semantics/Accept/Order/Examples.lean`.

### Choosing a quantifier

* A *validator* or *parser* that must accept the value: `acceptsSome` (some run succeeds) or,
  for a deterministic checker, `Decides`.
* A *safety* property (“this input never makes the program reject/trap”): `neverRejects`.
  It holds vacuously for inputs with no outcome, so it does not imply acceptance.
* A *robust* acceptance (“every run accepts”): `acceptsAll`.

Examples and regression tests: `Silmaril/Semantics/Accept/Examples.lean`.

### `Silmaril.Semantics.Accept.Rel.Defs` / `Thms`

| Name | Meaning |
| --- | --- |
| `α -|> β` | scoped notation (`open scoped Silmaril.Accept`) for Mathlib's `SetRel α β = Set (α × β)` |
| `outcomes R` | `fun a => {b \| (a, b) ∈ R}`, the runner of a relation |
| `pullSome R L` | `R.preimage L`: some output in `L` |
| `pullAll R L` | `R.core L`: every output in `L` (vacuous with none) |
| `ofPartial f` | relation of `f : α → Option β` (`f a = some b`) |
| `ofTotal f` | `Function.graph f` |
| `partialComp f g` | Kleisli composition `fun a => (f a).bind g` |
| `pdom f` | `{a \| (f a).isSome}` |
| `IndexedLang A` | `∀ i, Set (A i)` |
| `eraseSigma L` / `fiberLang M` | to and from `Set (Σ i, A i)`; `indexedLangIso` is an order isomorphism |
| `eraseSome L` / `eraseAll L` | `⋃ i, L i` / `⋂ i, L i` over a common carrier |

Rejection quantifiers: `neverRejects (outcomes R) rej = pullAll R rejᶜ`;
`compl_pullSome : (pullSome R L)ᶜ = pullAll R Lᶜ`; for a partial function, `none` is in every
`pullAll` and no `pullSome` (`mem_pullAll_ofPartial_of_none`,
`not_mem_pullSome_ofPartial_of_none`), and `pullSome_ofPartial_eq`/`pullAll_ofPartial_eq`
relate them through `pdom`. `not_mem_eraseSome` (rejected at every index) and
`not_mem_eraseAll` (rejected at some index). Composition: `pullSome_comp`, `pullAll_comp`,
`ofPartial_partialComp`, `ofTotal_comp`, `ofPartial_some_comp`. Checkers:
`Decides.optionAny`, `Decides.optionAll`, `Decides.sigma`, `Decides.fiber`.

Examples: `Silmaril/Semantics/Accept/Rel/Examples.lean`.
