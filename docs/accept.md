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

### Choosing a quantifier

* A *validator* or *parser* that must accept the value: `acceptsSome` (some run succeeds) or,
  for a deterministic checker, `Decides`.
* A *safety* property (“this input never makes the program reject/trap”): `neverRejects`.
  It holds vacuously for inputs with no outcome, so it does not imply acceptance.
* A *robust* acceptance (“every run accepts”): `acceptsAll`.

Examples and regression tests: `Silmaril/Semantics/Accept/Examples.lean`.
