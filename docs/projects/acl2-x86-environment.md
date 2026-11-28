# Logical ENV-ALISTP for the x86 record

`machineBindingsWithEnvironment` instantiates the ENV predicate of the
checked `X86REC-P1` field dispatcher. It takes `X86ISA::TLBP` and the
logical `X86ISA::X86-FETCH-DECODE-EXECUTE` as its two remaining bindings.
Lean proves the singleton ENV entry equation and satisfaction of the
exported `X86-RUN-HALTED` formula with those parameters.
[Standard-object model](acl2-x86-run-standard.md) ·
[Record order and field dispatcher](acl2-x86-object-order.md) ·
[Lean interface](../../Silmaril/Logic/ACL2/X86Run/Status/EnvironmentThms.lean)

## Source correspondence

The export comes from the certified ACL2 8.7 `machine/x86` world with
`X86ISA_EXEC=nil` at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. It retains
the translated and guard-holder-free bodies, qualified symbols, formals,
arities, guards and signatures of `ENV-ALISTP`, `RIP-RET-ALISTP`,
`I48P$INLINE`, and their alist, list, equality and signed-range helpers.
It also records source hashes and the native termination formulas for
the list recursions. [World artifact](../../corpus/acl2/x86-environment/acl2-8.7.json) ·
[Pinned ENV and oracle source][state] · [Pinned core definitions][axioms]

The checker validates the translated body shapes and emits the recognizer
with the actual three quoted keys, list length and signed oracle width.
`ENV-ALISTP` accepts NIL, or a proper three-entry association list with
the three keyword keys. Both file-related values must be alists. The
oracle must be an alist whose keys are integers in `[-2^47, 2^47)` and
whose values are proper lists of arbitrary objects. The outer key order
is immaterial. The `ASSOC-EQUAL` equation returns the first match and
uses total `CAR` even on atomic entries. `LEN` counts the cons spine
even on improper lists. These helper equations hold over all standard
objects. In `X86REC-P1`, a NIL environment entry is rejected because
NIL is the field default and must be omitted.

ACL2 certification, the exporter and the Python body check establish
provenance. The checker and Lean definitions provide the interpretation
of the supported source forms on standard objects, including the
positive-integer exponent and integer range reached through the oracle.
Lean proves the total equations and specializes the existing run. The
exported native termination formulas are retained as evidence. Lean
admits the helpers by structural recursion.
[Source checker](../../tools/acl2-x86isa/check_environment.py) ·
[Lean regressions](../../Silmaril/Logic/ACL2/X86Run/Status/EnvironmentTests.lean)

## TLB dependency boundary

The pinned logical `TLBP` accepts a list of `TLB-ENTRYP` entries with
a final `:TLB` atom. Each entry is a cons with a 40-bit unsigned value.
Its key must pass `TLB-KEY-P` (46 unsigned bits), and the generated
`TLB-KEY->R-W-X$INLINE` must return a value at most 2. The generated
accessor applies `TLB-KEY-FIX` and
`BITOPS::PART-SELECT-WIDTH-LOW$INLINE` with width 2 and offset 6.
The logical slice is `LOGHEAD 2 (LOGTAIL 6 key)` after the fix.
In the pinned ACL2 world, a probe proved that a 46-bit unsigned key
has accessor result `(mod (floor key 64) 4)`. The proof uses
`TLB-KEY-FIX-WHEN-TLB-KEY-P` and unfolds the logical bit helpers.
Closing `TLBP` in Lean requires interpreting those definitions and
linking ACL2's nonnegative quotient, rational `FLOOR`, and integer
`MOD` to Lean division and remainder on the reachable inputs. This
slice leaves `TLBP` explicit.
[Pinned TLB predicates][tlb] · [Pinned bit selection][bits] ·
[Pinned integer arithmetic helpers][ihs]

The [TLB follow-up](acl2-x86-tlb.md) checks that arithmetic path and
supplies the remaining field predicate.

## Reproduce

Use the [pinned certified checkout](acl2-x86-run.md#reproduce).

```sh
export PYTHONSAFEPATH=1
python3 -B tools/acl2-x86isa/export_x86_run.py --environment "$work/acl2" "$work/environment.json"
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Status.EnvironmentTests
python3 -B tools/acl2-x86isa/check_environment.py "$work/environment.json"
python3 -B tests/acl2/check_environment.py
```

Two fresh SBCL sessions produced identical export bytes. Lean checks 16
native environment and record observations and six helper observations
with ACL2 guard checks disabled during collection. These include signed
boundaries, a noninteger key, a wrong-package key, duplicate and
reordered keys, and improper lists. The record checks also exercise
logical state recognition and both status reads for an arbitrary TLB
predicate. The run regression takes the FAULT exit with the remaining
bindings arbitrary. The Python mutations exercise native terms, the
generated keys and widths, observations and termination metadata.

| Artifact | SHA-256 |
| --- | --- |
| World export JSON | `6fedc848bea2d78ae15de964b4848414e91fe88fc4cf938c4eafa1f6adaec48d` |
| Generated Lean source | `61290e00aee0714c28e9e54fc16e4aa1a91f36ff1ee5b2711aeba7270de98212` |

[state]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/state.lisp#L137-L175
[axioms]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp
[tlb]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/tlb.lisp#L237-L301
[bits]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/bitops/part-select.lisp#L63
[ihs]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ihs/basic-definitions.lisp#L156-L195
