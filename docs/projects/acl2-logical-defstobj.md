# ACL2 8.7 logical DEFSTOBJ

The authored `SIL-TOY` event has one integer scalar and one fixed array of
three integers. `Toy.encode s cells` represents it as the proper two-element
ACL2 list `(s cells)`, with the array represented by a separate proper list.
`CREATE-SIL-TOY` initializes the scalar to `-2` and the array to `(7 7 7)`.
The recognizer accepts exactly these two slots with an integer scalar and
three integer cells. The constructor, recognizer and both fields' reads and
writes agree with the translated logical bodies on the full standard object
domain. [Toy event][toy] · [Lean API][thms]

`Silmaril.Logic.ACL2.Standard.FixedLayout.Thms` reuses the standard Object
carrier, total CAR and CDR, integer projection, proper lists and MV-NTH.
The existing status record API models keyed entry lists. The fixed-layout
operations here use positional cons spines.
[Object model](acl2-standard-objects.md) · [MV-NTH](acl2-pure-helpers.md) ·
[Generic operations][defs]

## Logical reads and writes

A read after a write at the same position returns the written value. A
different natural position keeps its previous value. For Object-valued
indices, disjointness means that their natural fixes differ. Writing the
scalar preserves all cell reads, and writing a cell preserves the scalar
read. Given a recognized record, an integer scalar write preserves
recognition. An integer cell write preserves recognition when its natural
index is below three.

ACL2 fixes nonintegral and negative indices to zero through ZP. A read past
the cons spine yields NIL. A write grows the spine to include the index, and
the intervening absent positions read NIL. A write at an existing cons
preserves the tail following that position, including a dotted tail. The
recognizer can reject an off-guard result, for example after an array
extension or a write of NIL into an integer slot.
[Generic and toy theorems][thms] · [NTH][nth] · [UPDATE-NTH and UPDATE-NTH-ARRAY][update]

## Source and trust boundary

The exporter submits the toy event and 18 ground theorems to stock ACL2. It
reads eight generated declarations and eight supporting definitions from
the live world through `unnormalized-body` and `remove-guard-holders`. The
fixture preserves qualified symbols, lexical formals, arities and stobj
input and output signatures. The source checker resolves the calls and
lowers literal quotation and ACL2's NIL-only conditional. Recursive bodies
are lowered with an explicit recursive-call parameter. Lean checks those
equations against total implementations and checks the ground results
with kernel reduction. The export, lowering and shared Object primitive
interpretations form the source trust boundary.
[Fixture][fixture] · [Lean lowering][source] · [ACL2 generator][generator]

The Lean result covers the logical interpretation of this one
`DEFSTOBJ` event. ACL2's raw Lisp representation, execution on live
stobjs, guard verification and enforcement of single-threaded access
remain outside this correspondence. The ground theorems use quoted toy
data in the ACL2 logic.

## Reproduce

From the repository root, with Git, SBCL and GNU Make, build ACL2 at the
pinned commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204` and run two fresh
processes. Stock ACL2 supplies all dependencies for this event.

```sh
work=$(mktemp -d)
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$work/acl2"
test "$(git -C "$work/acl2" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$work/acl2" LISP=sbcl
python3 -I tests/logic/acl2/export_toy_defstobj.py "$work/acl2" "$work/first.json"
python3 -I tests/logic/acl2/export_toy_defstobj.py "$work/acl2" "$work/second.json"
cmp "$work/first.json" "$work/second.json"
python3 -I tests/logic/acl2/check_toy_defstobj.py "$work/first.json"
python3 -I tests/logic/acl2/test_toy_defstobj.py
lake build --wfail +Silmaril.Logic.ACL2.Standard.FixedLayout.Tests
```

The fixture SHA-256 is
`fcc10ed9d708f4c755f8e2d974e00c505cf8bbbb2e52ad82dc89414b68f82015`.
The Lean tests check the observations, two off-guard regressions, and
transitive axiom dependencies against `propext`, `Classical.choice`, and
`Quot.sound`. The Python tests mutate translated call identity, arity,
formal binding, stobj metadata, layout, initializers and a ground result.

[toy]: ../../tests/logic/acl2/toy-defstobj.lsp
[defs]: ../../Silmaril/Logic/ACL2/Standard/FixedLayout/Defs.lean
[thms]: ../../Silmaril/Logic/ACL2/Standard/FixedLayout/Thms.lean
[source]: ../../Silmaril/Logic/ACL2/Standard/FixedLayout/Source.lean
[fixture]: ../../corpus/acl2/toy-defstobj/acl2-8.7.json
[nth]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3882-L3890
[update]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L14105-L14122
[generator]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L20618-L20670
