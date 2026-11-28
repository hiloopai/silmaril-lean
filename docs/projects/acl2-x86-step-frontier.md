# Checked bindings for the logical x86 step frontier

`Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.machineBindings` takes a total
interpretation of 28 remaining declarations. It completes the original
33-entry interpretation before supplying it to the existing step/run
composition. The checked step body and the run's recursive admission are
reused in the same admitted model.
[Composition](acl2-x86-run-checked-step.md) · [Definitions][defs]

| Installed identity | Arity | Interpretation |
| --- | --- | --- |
| `ACL2::MV-NTH` | 2 | Standard object projection over the cons spine |
| `COMMON-LISP::EQL` | 2 | Logical object equality |
| `COMMON-LISP::NOT` | 1 | T exactly on NIL |
| `X86ISA::FAULT` | 1 | Checked logical record read |
| `X86ISA::MS` | 1 | Checked logical record read |

The resolver delegates the three pure operations to the checked
package-and-arity lookup. The two status reads use the record rules,
object order, and environment and TLB predicates already used by the run.
`fault_agrees` and `ms_agrees` identify each installed step denotation
with its named interpretation in the admitted run model for every standard
object and every remaining table. Neither theorem requires pointwise
agreement as an input.
[Pure helper equations](acl2-pure-helpers.md) ·
[Logical record model](acl2-x86-tlb.md) · [Agreement theorems][thms]

`installed_exact` checks the five pairs in the table against the pinned
step frontier. `remaining_iff` characterizes a remaining arity declaration
by membership in the original frontier with the installed pairs removed.
`remaining_count` checks that 28 entries remain, and `extend_of_remaining`
preserves their supplied interpretations. The original checked frontier is
itself tied to the step's manifest calls.
[Original frontier and source agreement](acl2-x86-step.md) ·
[Frontier theorems][thms]

The step defining equation, the original recursive run equation, and the
exported `X86-RUN-HALTED` sentence hold in the specialized model. Remaining
entries include `X86ISA::!MS`, the bit selector, and dispatcher calls. Their
semantics, execution and raw stobj correspondence are outside this slice.

## Verify

```sh
lake build --wfail +Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests
PYTHONSAFEPATH=1 make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests +Silmaril.Logic.ACL2.X86Run.WithStep.Tests +Silmaril.Logic.ACL2.Standard.Pure.Tests +Silmaril.Logic.ACL2.X86Run.Status.TlbTests'
```

The tests check the installed reader results on the native status
observations, both run early exits with arbitrary remaining bindings,
the pure bindings, and representative arity entries. The axiom audit
permits `propext`, `Classical.choice`, and `Quot.sound`.
[Regressions][tests]

[defs]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Defs.lean
[thms]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Thms.lean
[tests]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Tests.lean
