# ACL2 institutions for nonrecursive logical books

This PR is a foundational milestone toward C2/C4. The next deliverable is a concrete standard
ACL2 object and package layer with a checked package-sensitive nonrecursive admission.
[Standard ACL2 roadmap](acl2-standard-roadmap.md)

The fragment uses one logical value sort. User function symbols are package-qualified names in a
partial arity table. `Signature.resolve` checks a name at a requested arity, and `Term.app`
requires exactly that many arguments. Signature arrows include existing declarations at their
original names and arities. The fixed primitives are `nil`, `t`, `cons`, `car`, `cdr`,
`consp`, `equal` and `if`. A sentence asserts that its term evaluates to a value other than
`nil` under every assignment of its free variables. The model supplies total functions for the
declared symbols and a carrier with the stated laws for the primitives.

`ACL2.logic` pairs this semantics with an inductive derivation relation. Its rules include
equality, substitution, congruence, modus ponens, and computation laws for pairs, atoms and
conditionals. `ACL2.logic_sound` proves that each derivation preserves satisfaction. The
π-institution has named definition bodies in its signatures and treats their equations as
available hypotheses. Its arrows preserve those bodies under translation. Its semantic
comparison interprets the equations as restrictions on the models.

## Books and native admission

A checked `Event.defun` introduces a fresh name with a body scoped over the previous signature.
An `Event.defthm` introduces a fresh theorem name with a derivation from existing definitions and
theorems. It leaves the definition table intact. The raw `World` record also describes imported
snapshots. An imported theorem table needs a proof of `World.Valid` before it can be relied on
as a consequence of that snapshot's definitions.

A `Book W V` records its required input and its output world. `Book.includeBook` composes two
checked sequences at their common world. `Book.provable_include` preserves derivations and
`Book.extension` preserves named entries. `Book.checked` eliminates dependency on the named
theorem table, giving derivations from definitions alone for books started with a checked input.
`Book.valid` propagates semantic world validity.
`Book.expand` constructs model expansions by interpreting each new definition in a model of the
preceding events. Consequently `Book.entails_iff` gives semantic conservativity for input-world
statements.

`Standard.source` emits ACL2 events for already resolved names. The host supplies package setup,
native admissibility and certification. `Standard.Interface` describes those external
observations and the interpretation of logical values and calls. `Standard.Included` relates a
native include to a trace of the checked events. `Standard.Realizes` states the separate
obligations for names, definitions and recorded theorems. Given those obligations,
`Standard.Realizes.sound` and `Standard.Realizes.presentation_sound` transfer derivations to
the supplied interpretation. The interface does not infer realization from certification alone.

`Silmaril.ProofFormats.ACL2.admitSource` uses the existing Common Lisp S-expression reader to
match source to a supplied checked `Book W V`. It compares the ordered include paths, event
names, formal arities and term structure. Definition parameters are matched by position and
theorem variables by first occurrence, so renaming variables preserves a match while changing
their sharing does not. The resulting `CheckedSource` carries the Lean book and the source
match. The matcher accepts the `ACL2` package header, leading literal `include-book` forms,
simple `defun` and `defthm` events, and the optional logic-mode declaration and
`:rule-classes nil` used by the fixture.

Formal admission uses the supplied Lean derivations. ACL2 certification is a separate run:
stock ACL2 reads the authored files, admits their events and writes book certificates. The
matcher compares include paths as data. The fixture checks the dependency file separately and
composes the two Lean books at their common world; native ACL2 loads the actual dependency
during certification. Package resolution beyond this profile, recursive admission, induction,
guards, local events, encapsulation and arbitrary Community Books are outside the formal
model. [ACL2 8.7 manual](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html) ·
[ACL2 8.7 source](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204) ·
[ACL2 8.7 Community Books](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books)

## Logic graph

The [logic graph](logic-graph.md) registers the ordinary fragment institutions and their
morphisms. The ACL2 declarations in the table are relative to `Silmaril.Logic.ACL2`.

| Declaration | Record | Type and direction |
| --- | --- | --- |
| `inst` | `logic.acl2.inst` | Ordinary institution on arity signatures. |
| `presentedInst` | `logic.acl2.presented_inst` | Ordinary institution on signatures with definitions. Its models satisfy the defining equations. |
| `Equational.toEquational` | `logic.acl2.to_equational` | Institution morphism from `inst` to `logic.institution.examples.eq.inst`. Models go to their one-sort equational algebras. Equations over image signatures translate back to ACL2 `equal` statements. |
| `forgetDefinitions` | `logic.acl2.forget_definitions` | Institution morphism from `presentedInst` to `inst`. Models forget the defining constraints. Sentence translation is the identity on each underlying signature. |

The consequence records `logic.consequence.acl2.{derives,entails}` use the arity signature of
`Examples.exampleWorld`. The records `logic.consequence.acl2.presented.{derives,entails}` use
`Consequence.exampleDerives` and `Consequence.exampleEntails` over its presentation, where
`SILMARIL-FIRST` is defined as `car`. Both derivability systems have checked soundness answers.
The presented system records `Examples.firstSingleton` with an empty list of additional
premises. It uses `World.Checked.pi_derives` to discharge the named theorem table from the
book's `World.Provable` judgment, leaving just the defining equations as hypotheses.

`pi` and `piIns` are views of the syntactic π-institution in the comorphism and morphism diagram
categories. `piSound` is a diagram comorphism to `Institution.semanticPi presentedInst`. Its
component at the example presentation proves `Consequence.exampleSound`. The ordinary graph's
record types cover the entries in the table. Native ACL2 admission and inclusion cross the
`Standard.Interface` boundary described above.

## Reproduce the example

Build the public modules and check the authored definition and theorem books against their
Lean derivations. The regression also tests arity, variable sharing, formal parameters,
dependency names and rejection of read-time evaluation.
[Authored source fixtures](../../tests/acl2/books/)

```sh
lake build --wfail +Silmaril.ProofFormats.ACL2.Defs \
  +Silmaril.Logic.ACL2.Consequence.Thms +Silmaril.Logic.ACL2.Equational.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true --run tests/acl2/CheckSource.lean
```

Copy the same sources into a temporary directory and run the following with an ACL2 8.7
executable on the path. The theorem book's `include-book` loads the certified definition
book. A fresh ACL2 session then includes the certified theorem book and evaluates the projection.

```sh
acl2_example_dir=$(mktemp -d)
cp tests/acl2/books/*.lisp "$acl2_example_dir/"
cd "$acl2_example_dir"
acl2 > certify.log 2>&1 <<'EOF_ACL2'
(certify-book "acl2-definitions" 0 nil)
:u
(certify-book "acl2-theorems" 0 nil)
(good-bye)
EOF_ACL2
test -f acl2-definitions.cert && test -f acl2-theorems.cert
acl2 > include.log 2>&1 <<'EOF_ACL2'
(include-book "acl2-theorems")
(value-triple (silmaril-first (cons 'checked nil)))
(good-bye)
EOF_ACL2
! grep -E 'ACL2 Error|HARD ACL2 ERROR|\*\*\*\*\*\*\*\* FAILED' certify.log include.log
grep -q 'ACL2 !> CHECKED' include.log
```
