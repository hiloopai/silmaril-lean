# HOL and HOL Light

The release includes two separate HOL developments. For classical schematic
polymorphism, start with `Silmaril.Logic.HOLLight`.

| Development | What it provides | Model boundary |
| --- | --- | --- |
| `Logic.HOLLight` | Typed locally nameless terms; ten primitive inference rules and an explicit object-theory rule; term/type instantiation; derived classical reasoning; soundness and consistency | Nonempty Lean types in any `Type u`, full function spaces, actual equality and classical choice; Boolean and individual carriers are lifted `Bool` and `Nat` |
| `Logic.HOL` | Sorted signature-parametric syntax, typed proof certificates, checked-term wrappers and soundness | Small pointed carriers; subtype predicates are erased and abstraction/representation act as identities |

The HOL Light soundness theorem retains the supplied theory as an explicit
premise:

```text
Derives sig theory H p + model M satisfying theory
    -> every valuation satisfying H also satisfies p
```

`HOLLight.Derives.sound` covers every inference constructor, including both forms
of instantiation. Type instantiation can merge differently typed free-variable
names; the semantic proof accounts for these collisions. The public statement
is in `HOLLight/Soundness/Thms.lean`; its induction proof is under
`Silmaril/Proofs/Logic/HOLLight/`.

`Model.standard` constructs a model of the initial signature, and
`standard_models_classical` validates the explicit eta, selection and infinity
axioms. `classical_consistent` then proves that this object theory cannot derive
falsity, relative to Lean's classical metatheory. These object axioms are syntax;
they add no axioms to Lean.

The following examples are also recorded in `HOLLight/Examples.lean`:

```lean
import Silmaril.Logic.HOLLight.Consistency
import Silmaril.Logic.HOLLight.Classical.ExcludedMiddle

open Silmaril.Logic.HOLLight

example : ∃ M : Model.{0} initialSignature, Models M classicalTheory :=
  ⟨Model.standard, standard_models_classical⟩

example : Derives initialSignature [] ∅ Tm.truth := Derives.truth

example : ¬ Derives initialSignature classicalTheory ∅ Tm.falsity :=
  classical_consistent

example {p : Tm} (hp : HasType initialSignature [] p .bool) :
    Derives initialSignature classicalTheory ∅ (Tm.disj p (Tm.neg p)) :=
  Derives.excludedMiddle hp
```

Build the examples and key proof roots with:

```sh
lake build Silmaril.Logic.HOLLight.Examples \
  Silmaril.Logic.HOLLight.Consistency \
  Silmaril.Logic.HOLLight.Consilience.NatArithmetic \
  Silmaril.Logic.HOL.Intrinsic
```

`HOLLight.Consilience` is a second presentation of terms, typing, proof rules and
evaluation. Its types, semantic carriers and valuation interfaces are shared.
Rule-by-rule translations prove provability equivalence with the first kernel;
evaluation is related in both directions. Native derivations inhabit `Prop`, so
the reverse translation establishes existence of a proof tree, rather than an
inverse on proof objects.

`Consilience.NatArithmetic` adds zero, successor, addition and multiplication,
seven explicit Robinson arithmetic axioms, a genuine natural-number model and a
kernel proof of `1 + 1 = 2`. It proves consistency of this explicitly extended
theory. It does not yet translate arbitrary Q or PA derivations.

The CSLib adapters expose simultaneous substitution, one-hole contexts and
inference systems. Propositional natural-deduction proofs translate into HOL
proofs, including a categorical presentation of the translation. The finite
context deduction theorem relates a hypothesis set to an implication from its
conjunction.

Further steps are checked constant/type definitions, a named interchange format,
and an executable certificate checker. The current theorems concern the Lean
calculi; correspondence with HOL Light's OCaml implementation and completeness
for full-function models require separate proofs. The generic `Logic.HOL`
interpretation uses pointed carriers with predicate erasure, as the table above
records.

Reference files are HOL Light's `fusion.ml`, `class.ml` and `nums.ml`, pinned at
`d30e8239887b2348a063f82232a864de1cc2df15`. They are references for the primitive rules and initial classical axioms.
Exact file hashes are in [references.bib](../../references.bib).
