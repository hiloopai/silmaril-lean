# Checked logical ACL2 x86isa step body

`Silmaril.Logic.ACL2.X86Step.definition` checks the single-argument
`X86ISA::X86-FETCH-DECODE-EXECUTE` declaration from the pinned ACL2 8.7
`X86ISA_EXEC=nil` world. The input is the translated `unnormalized-body`
after ACL2's `remove-guard-holders`, exported by the existing dependency
tool at commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. The generator
pins the bytes of both inputs, runs the dependency checker, and compares the
entire generated Lean source byte for byte. [Dependency manifest](acl2-x86-dependencies.md) ·
[Generated source][lean-source] · [Source checker][checker] · [License notice][notice]

## Checked lowering

The reusable lowering constructs `Checked S scope source`, whose indices
are the exact translated term and its ordered scope. A variable carries a
finite slot and a proof that the name at that slot is its package-qualified
identity. Calls supply an arity-indexed callee and a checked argument list.
A lambda checks its body against its own distinct formals and its actuals
against the caller's scope. The type requires the two counts to agree, and
evaluation passes the actuals in order. `QUOTE` retains the integer or
resolved symbol. `IF` retains both branches and tests only for `NIL`.
[Translation and interpretation definitions][lowering]

`checked_agreement` identifies the result of the lowerer with the body in
the definition. It covers 570 variable occurrences, 124 quotations, 58
lambda applications and 210 named call sites, including `IF`. `calls_exact`
checks membership in the 37-entry source call set against the manifest by
package, name and arity. The tests exercise bad packages, wrong arities,
duplicate formals and lexical capture, plus a reordered outer lambda whose
dependency graph still matches. Synthetic evaluation regressions check
argument order, `CONS` result order and ACL2's treatment of zero as non-NIL.
[Step theorems][theorems] · [Lean regressions][tests] · [Source mutation][mutation]

## Defining equation and external bindings

`defining_equation` extends any total `Interpretation frontier` on the
standard ACL2 `Object` carrier by interpreting the fresh step symbol as the
evaluation of the checked body. The generic extension preserves every old
binding. `frontier_exact` proves that the signature contains exactly the 33
entries in `frontierEntries`, with their full spellings and arities.
`frontier_partition` accounts for the four fixed primitives `IF`, `CONS`,
`EQUAL` and `BINARY-+`. This is the step's frontier, so the run-only `ZP`
binding is absent. [Exact external signature][frontier] · [Defining equation][theorems]

The translation preserves logical multiple-value lists built by `CONS`,
their lambda bindings and each `ACL2::MV-NTH` call. `MV-NTH` remains an
external binding, alongside the accessors, memory operations, and the
one-byte, VEX and EVEX calls. The named definition is nonrecursive and
total for **every** supplied frontier interpretation. Identifying any
particular interpretation with ACL2's frontier definitions requires
additional evidence. Guard verification, logical stobj correspondence,
dispatcher admission and source-to-world expansion correspondence remain
outside this result. The source boundary is the pinned certified ACL2
projection and the generated syntax comparison. [Certificate limits](acl2-x86-dependencies.md#checked-slice-and-limits)

## Reproduce

Use the [pinned certification commands](acl2-x86-run.md#reproduce) and set
`acl2` to the certified checkout. The following reads the logical world
properties and checks the translated bodies without invoking the machine
step or dispatchers.

```sh
work=$(mktemp -d)
python3 -IB tools/acl2-x86isa/export_dependencies.py "$acl2" "$work/one"
python3 -IB tools/acl2-x86isa/export_dependencies.py "$acl2" "$work/two"
for file in manifest.json step-body.json; do
  cmp "$work/one/$file" "$work/two/$file"
  cmp "$work/one/$file" "corpus/acl2/x86-dependencies/$file"
done
python3 -IB tools/acl2-x86isa/check_step.py "$work/one"
python3 -IB tests/acl2/check_x86_step.py
lake build --wfail +Silmaril.Logic.ACL2.X86Step.Tests
PYTHONSAFEPATH=1 make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Step.Tests'
```

The two fresh SBCL 2.5.2 sessions produced byte-identical copies of both
fixtures. The warning-strict test module audits agreement, call coverage,
frontier partition and arity, the defining equation, and preservation of
the prior interpretation. Their combined axiom dependencies are `propext`,
`Classical.choice` and `Quot.sound`.

[lean-source]: ../../Silmaril/Logic/ACL2/X86Step/Source.lean
[checker]: ../../tools/acl2-x86isa/check_step.py
[notice]: ../../NOTICES/ACL2-x86isa
[lowering]: ../../Silmaril/Logic/ACL2/Translated/Defs.lean
[theorems]: ../../Silmaril/Logic/ACL2/X86Step/Thms.lean
[tests]: ../../Silmaril/Logic/ACL2/X86Step/Tests.lean
[mutation]: ../../tests/acl2/check_x86_step.py
[frontier]: ../../Silmaril/Logic/ACL2/X86Step/Source.lean#L55
