# Logical FAULT and MS for X86-RUN

This slice binds the two status reads in the existing standard-object
`X86-RUN` model. It uses the certified logical `machine/x86` world of ACL2
8.7 at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`, with `X86ISA_EXEC=nil`.
[World artifact](../../corpus/acl2/x86-status/acl2-8.7.json) ·
[Standard X86-RUN model](acl2-x86-run-standard.md) · [Pinned state source][state]

| Export | Logical path | Foundational stobj implementation |
| --- | --- | --- |
| `X86ISA::FAULT` | `FAULT$A` calls `XR :FAULT NIL` | `FAULT$C` uses `NTH 1` |
| `X86ISA::MS` | `MS$A` calls `XR :MS NIL` | `MS$C` uses `NTH 0` |

The export retains the translated and guard-holder-free bodies, package
identities, formals, arities, guards, symbol classes, stobj signatures,
and abstract-stobj tuples. It reads the `X86-CORR` name from the generated
`DEFABSSTOBJ-EVENTS` in the completed state certificate. ACL2's own
`absstobj-correspondence-formula` reconstructs the two expected translated
obligations. Each says that `X86-CORR` on the foundational and abstract states
implies equality of its `$C` and `$A` results. The local correspondence
relation and proofs are scoped to upstream certification. The exported
obligations are evidence of their statements. The Lean run proofs make
no use of those obligations as facts. [Stobj generator][rstobj] ·
[ACL2 obligation generator][obligations]

## Checked logical representation

`XR` constructs a cons key with a keyword car and a NIL cdr. The logical
state is an ACL2 object. A recognized sparse record has a nonempty ordered
entry list in its car and a non-record tail in its cdr. `X86REC-TO-MTR`
wraps every other input with an empty entry list. Lookup tests the strict key
order before testing equality, and its default for both status keys is NIL.
The logical stobj recognizer requires a NIL bad part. Thus an atom or an
out-of-order record can read as NIL, while a record with a non-NIL bad tail
can still return its entries. The foundational reads use total ACL2 `NTH`
at the exported natural slots over the logical list. [Record generator][records] ·
[ACL2 NTH definition][nth]

The executable checker pins the complete artifact, matches the translated
wrapper and record-read terms, specializes the exported default dispatch on
the two package-qualified keywords, and generates a Lean module with those
keys, defaults and slots. Lean checks the generated module, the representation
lemmas, and the specialization of the original admitted body and halted
statement. ACL2 certification, world export, and the Python translation
establish source provenance. Lean checks the conditional model and proofs.
[Checker](../../tools/acl2-x86isa/check_status_accessors.py) ·
[Lean interface](../../Silmaril/Logic/ACL2/X86Run/Status/Thms.lean)

The remaining parameters are the non-NIL predicates for `X86ISA::X86REC-P1`
(the typed, ordered entry-list recognizer) and `ACL2::<<` (the strict key
order), and the total logical `X86ISA::X86-FETCH-DECODE-EXECUTE` step. The
export retains the `X86REC-P1` body. Closing it requires the general field
typing and default functions as well as ACL2's object order. Full machine
correspondence also requires the checked step and stobj closure and a state
relation for both machine views and the environment.

## Reproduce

Use the pinned certified checkout from the [X86-RUN reproduction](acl2-x86-run.md#reproduce).

```sh
python3 -B tools/acl2-x86isa/export_x86_run.py --status-accessors "$work/acl2" "$work/status.json"
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Status.Tests
python3 -B tools/acl2-x86isa/check_status_accessors.py "$work/status.json"
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.Status.Tests +Silmaril.Logic.ACL2.X86Run.Standard.Tests'
```

The Lean tests compare six native observations, using an interpretation of
the two open predicates restricted to status-only entries. They cover the
empty state, both initialized status fields, an MS-only state, a malformed
atom, wrong key order, and a record that still reads through a non-NIL bad
tail. The early-exit tests apply the actual generated run to native-produced
logical states with an arbitrary step. The Python mutations exercise the
wrapper, packages, indices, arity, lookup, slot, metadata, and sample ties.

Two fresh sessions using SBCL 2.5.2 and the pinned certified checkout
produced the same export bytes.

| Artifact | SHA-256 |
| --- | --- |
| Status export JSON | `481d502d3980285e97fae81c58c9841a19750490c14549219b819ad8c414ae7c` |
| Generated Lean source | `67d1e67b174acbb2c4e36b164b790885b6302df1316776824614b5652f6eed76` |
| Pinned `machine/state.lisp` | `257fa2d41f051a1d3bb4b4c74747a70472c6f4d9c82823bb83278d08d65728cd` |

[state]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/state.lisp#L662-L679
[rstobj]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/defrstobj2/defrstobj.lisp#L1144-L1192
[obligations]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/other-events.lisp#L22563-L22612
[records]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/defrstobj2/def-multityped-record.lisp#L265-L320
[nth]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3882-L3889
