## Operational semantics: L1 and L2

These developments follow chapters 1–4 of Peter Sewell's *Semantics of
Programming Languages* notes for Cambridge Part IB, 2025–26. The course is a
self-contained leaf of the library: its proofs stay near the definitions and
exercise statements, and other library topics do not import it.

```sh
lake build Silmaril.Courses.Cambridge.L1.Course \
  Silmaril.Courses.Cambridge.L2.Course
```

The smaller `L1` and `L2` imports expose the language interfaces.
`L1.Course` and `L2.Course` add the metatheory and exercise developments.
All module names below start with `Silmaril.Courses.Cambridge.`.

| Language | Features | Main proved results |
| --- | --- | --- |
| `L1` | Integers, Booleans, conditionals, finite integer stores, assignment, sequencing and loops | Determinacy; decidable sound and complete type inference; type uniqueness; progress, preservation and safety over every finite reachable trace |
| `L2` | L1 plus functions, application, strict `let` and recursive functions | Capture-avoiding substitution; decidable sound and complete type inference; type uniqueness; preservation of typing, closedness and allocated locations; progress for closed well-typed expressions |

### Stores and safety assumptions

Stores are finite partial maps from location names to integers. Locations are
opaque strings, and assignment updates an already allocated location; the
languages do not allocate fresh references. Core arithmetic uses unbounded
integers. The L1 machine-integer exercise separately supplies modular
`BitVec w` arithmetic and signed comparison, with explicit overflow examples.

`StoreCovers Γ s` means that every location mentioned by the typing environment
is allocated in `s`. L1 progress and safety require this premise. L2 also
requires `Expr.Closed`: no free variable names and no dangling de Bruijn
indices. Preservation proves that steps retain the required invariants.
Safety means that a reachable configuration is a value or has a next step;
it does not assert termination of programs containing loops or recursion.

| Result | Public name |
| --- | --- |
| L1 one-step determinacy | `L1.Step.deterministic` |
| Inference exactly characterizes typing | `L1.infer_iff_hasType`, `L2.infer_iff_hasType` |
| L1 progress and preservation | `L1.progress`, `L1.preservation` |
| L1 safety after finitely many steps | `L1.safety`, `L1.safety_reachable` |
| L2 typed substitution | `L2.HasType.subst`, `L2.HasType.beta` |
| L2 progress | `L2.progress` |
| L2 typing, closedness and store coverage | `L2.type_preservation` |

L2 keeps named source syntax in `RawExpr`. Resolution maps bound occurrences
to de Bruijn indices while retaining free names. `AlphaEq` is equality of the
resolved syntax; examples distinguish harmless binder renaming from capture.

### Evaluation strategies and executable examples

L2 has call-by-value (`Step`), call-by-name (`NameStep`) and a broader full-beta
relation (`BetaStep`). Call-by-value and call-by-name steps embed in
`BetaStep`. Their agreement is not assumed: a proved store-effect example
returns `true` under call-by-value and `false` under call-by-name because an
unused effectful argument is evaluated only in the first strategy.

The executable interfaces have different proved contracts:

| Interface | What it computes | Current guarantee |
| --- | --- | --- |
| `L1.Exercises.searchConfig` | One step with a printable derivation tree | Each returned tree proves its resulting `L1.Step` via `StepTree.toStep` |
| `L2.runFuel` | Substitution-based CBV/CBN reduction, bounded by a number of transitions | Concrete exercise programs have proved results; no general reducer-to-`Step` correctness theorem yet |
| `L2.evalClosureFuel` | CBV evaluation with lexical and recursive closures, bounded by evaluation depth | Proven agreement with the substitution interpreter on lexical-scope, recursion and store-effect examples; no general simulation theorem yet |

`runFuel` returns `some c` when its reducer has no next step, which can mean a
value or a stuck configuration on untyped input. `none` records insufficient
transition fuel. A particular fuel-exhaustion equation is not an infinite-run
proof. The closure interpreter's `none` also covers invalid operations or
missing variables; `evalClosureGround` additionally rejects function results.
Its depth fuel is not directly comparable to `runFuel`'s transition budget.

For example:

```lean
import Silmaril.Courses.Cambridge.L2.Course

open Silmaril.Courses.Cambridge

example : L2.runFuel .name 10 L2.Exercises.EvaluationStrategies.start =
    some L2.Exercises.EvaluationStrategies.nameResult :=
  L2.Exercises.CallByNameInterpreter.name_matches_exercise23

example : L2.evalClosureGround 40 L2.Exercises.Closures.lexicalStart =
    some L2.Exercises.Closures.lexicalResult :=
  L2.Exercises.Closures.lexical_closure
```

The L1 exercises also prove counterexamples for nondeterministic evaluation
order and for retaining the old typing rule after changing assignment's
result. Revised assignment typing restores preservation. A factorial-shaped
program is defined and typed; its general factorial input/output correctness
is not proved in this slice. L2's first-order exercise defines saturated
multiargument calls and proves that a partial call is untypable.

The notes are cited as `sewell2026semantics` in `references.bib`; their exact
artifact hash is recorded there. The formalization uses finite maps and
de Bruijn binders rather than asserting correctness of the accompanying
OCaml, Java or SML implementations.
