# ACL2 object order and the x86 record recognizer

`machineBindingsWithFields` uses the native logical record path for both
`FAULT` and `MS`. It instantiates the two reader callbacks from the status
slice with `ACL2::<<` and `X86ISA::X86REC-P1` on standard `Object`. The
specialized run still satisfies the exported `X86-RUN-HALTED` formula.
[Status slice](acl2-x86-status.md) ·
[Lean interface](../../Silmaril/Logic/ACL2/X86Run/Status/RecordThms.lean)

## Source and proof

The export comes from the certified ACL2 8.7 logical `machine/x86` world
with `X86ISA_EXEC=nil`, commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`
and tree `66d80ea68f664b931f8982b607fe2305f3cec0e4`. It retains
package-qualified names, formals and arities, raw and guard-holder-free
translated bodies, guards, stobj signatures, symbol classes, and recursive
metadata. The order slice includes `<<`, `LEXORDER`, `ALPHORDER`,
`SYMBOL<`, `STRING<`, `STRING<=`, `STRING<-L`, `CHAR<`, and `ENDP`,
with live arities for primitive calls and the native statements of
the four strict order laws. The record slice includes `X86REC-P1`, the
field dispatchers and `TTY-BUFFERP`.
[World artifact](../../corpus/acl2/x86-order/acl2-8.7.json) ·
[Pinned order book][order] · [Pinned ACL2 system definitions][axioms] ·
[Pinned record generator][record] · [Pinned field declarations][state] ·
[Pinned TTY recognizer][tty]

Lean orders objects by a preorder token sequence. Atoms compare by
category, with rational, complex rational, character, string and symbol
cases in native order. Symbols compare spelling before home package.
Conses compare the car first and then the cdr when the cars are equal. The
continuation lemma shows that following tokens cannot affect an unequal
subtree comparison. Lean proves injectivity, the native equations for
`<<` and `LEXORDER`, and irreflexivity, transitivity, asymmetry and
trichotomy. The `ALPHORDER` proof covers the branches reached by
`LEXORDER` on stock atoms. ACL2's `BAD-ATOM<=` is outside the standard
carrier. The string lemmas cover the byte lists and natural offsets
reached by the order, including a zero index as a non-NIL result.
[Order interface](../../Silmaril/Logic/ACL2/Standard/ObjectOrder/Thms.lean)

`entriesP` checks the tail, the current value's field type, omission of
default values and strict order between adjacent keys. The generator
compiles the native package-qualified field tests and default literals.
ACL2 `CAR` is total, so dispatch also applies when a key is atomic.
`TTY-BUFFERP` checks a proper list of unsigned bytes. The specialization
still takes the non-NIL interpretations of `X86ISA::ENV-ALISTP` (arity 1)
and `X86ISA::TLBP` (arity 1) and a total interpretation of the logical
`X86ISA::X86-FETCH-DECODE-EXECUTE` step (arity 1). Stobj representation
alignment and mutable execution are outside this proof.

The pinned ACL2 build, certificates and world export establish provenance.
The Python checker matches translated body shapes and compiles the field
rules and observations. The checker and review of the Lean definitions
establish correspondence from those shapes to the Lean implementations.
Lean checks the equations and proofs over `Object`, including the strict
order laws derived independently of the exported ACL2 theorem formulas.
[Source checker](../../tools/acl2-x86isa/check_object_order.py) ·
[Lean regressions](../../Silmaril/Logic/ACL2/X86Run/Status/RecordTests.lean)

## Reproduce

Use the [pinned certified checkout](acl2-x86-run.md#reproduce).

```sh
python3 -B tools/acl2-x86isa/export_x86_run.py --object-order "$work/acl2" "$work/x86-order.json"
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Status.RecordTests
python3 -B tools/acl2-x86isa/check_object_order.py "$work/x86-order.json"
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.Status.RecordTests +Silmaril.Logic.ACL2.X86Run.Status.Tests +Silmaril.Logic.ACL2.X86Run.Standard.Tests'
```

The Lean regressions check 19 native order pairs in both directions, 18
entry-list results and the six native status observations. They cover
rational and complex values, bytes beyond ASCII, package and case
distinctions, string prefixes, dotted pairs, unordered and duplicate keys,
default omission and malformed entries and byte lists. The actual generated
run takes both native-derived early exits for arbitrary remaining field
predicates and step. The checker rejects mutations of translated terms,
field dispatch, observations and order theorem metadata.

Two fresh SBCL sessions on the pinned certified checkout produced the
same export bytes.

| Artifact | SHA-256 |
| --- | --- |
| World export JSON | `cb77542025f89ab900def3282353ee3a102a1192cd5a3c6bb5f04f994335eac0` |
| Generated Lean source | `73f0a39e91e9b327044139d90570bc3afe49a5758ad253e170dc8203ac64cc47` |

[order]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/misc/total-order.lisp
[axioms]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp
[record]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/defrstobj2/def-multityped-record.lisp
[state]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/state.lisp
[tty]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/tty.lisp#L83-L93
