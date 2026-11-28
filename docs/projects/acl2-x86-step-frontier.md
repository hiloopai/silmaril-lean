# Checked bindings for the logical x86 step frontier

`Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.machineBindings` takes a total
interpretation of 24 remaining declarations. It completes the original
33-entry interpretation before supplying it to the existing step/run
composition. The checked step body and the run's recursive admission are
reused in the same admitted model.
[Composition](acl2-x86-run-checked-step.md) · [Definitions][defs]

| Installed identity | Arity | Interpretation |
| --- | --- | --- |
| `ACL2::MV-NTH` | 2 | Standard object projection over the cons spine |
| `BITOPS::PART-SELECT-LOW-HIGH$INLINE` | 3 | Checked logical bit selection in argument order `x`, `low`, `high` |
| `COMMON-LISP::EQL` | 2 | Logical object equality |
| `COMMON-LISP::NOT` | 1 | T exactly on NIL |
| `X86ISA::FAULT` | 1 | Checked logical record read |
| `X86ISA::MS` | 1 | Checked logical record read |
| `X86ISA::PREFIXES->ADR$INLINE` | 1 | Address-size field of the fixed-width object |
| `X86ISA::PREFIXES->NUM$INLINE` | 1 | Count field of the fixed-width object |
| `X86ISA::PREFIXES->NXT$INLINE` | 1 | Next-byte field of the fixed-width object |

The resolver delegates `MV-NTH`, `EQL`, and `NOT` to the checked
package-and-arity lookup. The two status reads use the record rules,
object order, and environment and TLB predicates already used by the run.
`fault_agrees` and `ms_agrees` identify each installed step denotation
with its named interpretation in the admitted run model for every standard
object and every remaining table. Neither theorem requires pointwise
agreement as an input.
[Pure helper equations](acl2-pure-helpers.md) ·
[Logical record model](acl2-x86-tlb.md) · [Agreement theorems][thms]

`partSelectLowHigh_agrees` identifies the arity-three binding with the
translated logical Bitops body for every standard payload and pair of bounds.
[Bit-selection correspondence](acl2-bit-selection.md) · [Agreement theorems][thms]

`prefixesAdr_agrees`, `prefixesNum_agrees`, and `prefixesNxt_agrees`
identify the unary bindings with the corresponding translated ACL2 bodies
for every standard object. `PREFIXES-FIX$INLINE`, `LOGHEAD$INLINE`, and
`PART-SELECT-WIDTH-LOW$INLINE` are internal to the checked projection terms.
[Projection correspondence](acl2-prefixes-projections.md) · [Agreement theorems][thms]

`installed_exact` checks the nine pairs in the table against the pinned
step frontier. `remaining_entries_exact` lists the precise 24 pairs left
after installing the three projections from the 27-root snapshot.
`remaining_iff` relates the remaining arity declarations to the original
manifest with the installed pairs removed. `extend_of_remaining` preserves
the supplied interpretation of each remaining entry.
[Original frontier and source agreement](acl2-x86-step.md) ·
[Historical audit](acl2-x86-frontier-audit.md) ·
[Frontier theorems][thms]

The step defining equation, the original recursive run equation, and the
exported `X86-RUN-HALTED` sentence hold for any interpretation of the 24
remaining entries in the same specialized model. Those entries include
`X86ISA::GET-PREFIXES`, `X86ISA::!MS`, and dispatcher calls. Their
semantics, execution and raw stobj correspondence are outside this slice.

## Verify

```sh
lake build --wfail +Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests \
  +Silmaril.Logic.ACL2.Standard.FixedWidth.Tests
PYTHONSAFEPATH=1 make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.WithStep.Frontier.Tests +Silmaril.Logic.ACL2.X86Run.WithStep.Tests +Silmaril.Logic.ACL2.Standard.FixedWidth.Tests'
```

The tests check the installed reader results on the native status
observations, both run early exits with arbitrary remaining bindings,
the installed projections on the pinned native object observations,
and package, suffix, and arity checks. The axiom audit
permits `propext`, `Classical.choice`, and `Quot.sound`.
[Regressions][tests]

[defs]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Defs.lean
[thms]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Thms.lean
[tests]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Frontier/Tests.lean
