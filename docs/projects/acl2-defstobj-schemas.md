# Schema-parameterized logical ACL2 DEFSTOBJ

Import `Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Thms` for the generic
Lean model. A layout is an ordered list of integer scalar or fixed-size
integer-array slots with integer initializers. The record is a proper ACL2
list of the same length. An array slot is a proper list of the declared
length, with integer elements. [Generic definitions][defs] · [Theorems][thms]

## Generic laws

- The empty layout accepts exactly NIL. A nonempty layout accepts a cons
  whose first value satisfies its designated slot and whose tail satisfies
  the remaining layout. These cases hold for every standard Object.
- Initialization is accepted for every layout. Reading a declared position
  returns the corresponding slot initializer. Reading an initialized array
  cell with natural-fixed index below its size returns the initial integer.
- On an accepted record, a write to a declared slot preserves recognition
  when the replacement satisfies that slot. An array cell write preserves
  recognition when the slot has the declared array kind, the natural-fixed
  index fits, and the replacement is an integer.
- Positional read-after-write and preservation at distinct outer positions
  hold on all objects. For two cells of the same array, the inequality is
  between their natural-fixed indices. The same total CAR, CDR, NTH and
  UPDATE-NTH behavior applies off guard, including NIL padding.

Read and write operations take a natural slot number and, for cells, an
ACL2 Object index. The layout hypotheses belong to the recognition
preservation theorems. [Positional lemmas](acl2-logical-defstobj.md) · [Theorems][thms]

## Checked ACL2 events

The checker reads the actual event form from ACL2's world. It accepts the
profile with a nonempty layout, standard ACL2-package names, default
generated names, explicit integer initializers, and one natural dimension
per fixed integer array. It rejects unsupported types, resizable arrays,
extra attributes, name collisions and malformed descriptors. Its
`check_expansion(event, rows)` entry point requires exactly the expected
qualified definitions, arities, lexical formals and stobj input and output
metadata. It checks component recognizers, slot order, array sizes,
initializer values, and the actual translated terms before reusing the
existing term lowering. [Checker][checker] · [ACL2 generator][generator]

| Event | Slots in declaration order | Ground observations |
| --- | --- | --- |
| `SIL-TOY` | Integer initialized to −2, array of 3 initialized to 7 | 18 |
| `SIL-SHELVES` | Array of 2 initialized to 4, integer initialized to −9, array of 1 initialized to −3 | 11 |

Lean proves agreement with both pinned constructors, recognizers, and
every generated field declaration in these two worlds. Fixed arrays also
generate a logical constant-length function and an identity resize
function. ACL2's `unnormalized-body` properties are projected with
`remove-guard-holders`. The schema export reuses the eight previously
pinned SIL-TOY bodies and adds its two auxiliary array declarations.
[Existing fixture][toy] · [Schema fixture][fixture] · [Lean agreement][agreement]

The generic laws quantify over Lean layouts. The native agreement theorems
cover the two exported declarations and depend on the ACL2 world projection,
the source checker and lowering, and the shared Object primitive
interpretations. The scope is logical. Live and raw stobj representation or
execution, guard verification, and single-threaded access enforcement
remain outside the model.

## Reproduce

Use the stock ACL2 8.7 checkout and SBCL build from the
[SIL-TOY reproduction instructions](acl2-logical-defstobj.md#reproduce).
The pin is `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. From the Silmaril
root, point `acl2_source` at that checkout.

```sh
work=$(mktemp -d)
python3 -I tests/logic/acl2/export_defstobj_schema.py "$acl2_source" "$work/first.json"
python3 -I tests/logic/acl2/export_defstobj_schema.py "$acl2_source" "$work/second.json"
cmp "$work/first.json" "$work/second.json"
python3 -I tests/logic/acl2/check_defstobj_schema.py "$work/first.json"
python3 -I tests/logic/acl2/test_defstobj_schema.py
lake build --wfail +Silmaril.Logic.ACL2.Standard.FixedLayout.Tests
```

The schema fixture SHA-256 is
`4c4b3a5d5481e5ee71c79da725d3707da89e5c0a3a38b245c4c3840214a399ec`.
The existing fixed-layout target builds the generic laws and both agreement
proofs, checks the ground results by kernel reduction, and audits transitive
dependencies against the repository's three permitted axioms. The existing
Python check hooks now also test the schema fixtures and mutations.

[defs]: ../../Silmaril/Logic/ACL2/Standard/FixedLayout/Schema/Defs.lean
[thms]: ../../Silmaril/Logic/ACL2/Standard/FixedLayout/Schema/Thms.lean
[agreement]: ../../Silmaril/Proofs/Logic/ACL2/Standard/FixedLayout/SchemaFixtures.lean
[checker]: ../../tests/logic/acl2/check_defstobj_schema.py
[toy]: ../../corpus/acl2/toy-defstobj/acl2-8.7.json
[fixture]: ../../corpus/acl2/defstobj-schema/acl2-8.7.json
[generator]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L20308-L20579
