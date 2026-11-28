# Logical TLBP for the x86 record

`machineBindingsWithRecord` fixes both former field predicates in the
standard-object `X86REC-P1` specialization. It uses the checked
`ENV-ALISTP` and `TLBP` interpretations and takes the logical
`X86-FETCH-DECODE-EXECUTE` step as its sole parameter. Lean proves the
singleton TLB entry equation and satisfaction of the exported
`X86-RUN-HALTED` formula with that step arbitrary.
[Environment slice](acl2-x86-environment.md) ·
[Record recognizer](acl2-x86-object-order.md) ·
[Lean interface](../../Silmaril/Logic/ACL2/X86Run/Status/TlbThms.lean)

## Certified source and arithmetic

The export uses the certified ACL2 8.7 logical machine world with
`X86ISA_EXEC=nil` at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`.
It retains the raw and guard-holder-free translated definitions,
package identities, formals, arities, guards, stobj signatures, and
the termination formulas for `TLBP` and
`NONNEGATIVE-INTEGER-QUOTIENT`. The checked bodies trace the generated
key accessor through its fix, `PART-SELECT-WIDTH-LOW`, `LOGHEAD`,
`LOGTAIL`, integer wrappers, and translated `FLOOR` and `MOD`.
Source file hashes are part of the export.
[World artifact](../../corpus/acl2/x86-tlb/acl2-8.7.json) ·
[Pinned TLB][tlb] · [Pinned bit selection][bits] ·
[Pinned IHS integer helpers][ihs] · [Pinned ACL2 arithmetic][axioms]

The native export replays the proof of the translated statement
`(implies (unsigned-byte-p 46 key)
          (equal (tlb-key->r-w-x key) (mod (floor key 64) 4)))`.
The proof uses the generated key-fix theorem. The checker matches that
theorem and the replayed statement against the translated bodies and
emits the key width, page width, bit offset and width, maximum mode and
terminator. [Native proof replay](../../tools/acl2-x86isa/tlb-samples.lisp) ·
[Source checker](../../tools/acl2-x86isa/check_tlb.py)

Lean proves that the subtraction recurrence for nonnegative quotient
computes natural division. For `FLOOR`, it follows the branches on the
reduced rational product. In the negative branch a denominator other
than one cannot divide the numerator, so the extra subtraction of one
gives the floor. Lean proves the resulting `FLOOR` and `MOD`
equalities for an integer dividend and a natural divisor, including
the logical zero-divisor results of zero and the input dividend,
respectively. These theorems justify using fast division and
remainder in the predicate. Lean also proves that the 46-bit key fix
leaves a valid key unchanged. [Quotient and remainder interface](../../Silmaril/Logic/ACL2/Standard/Quotient/Thms.lean)

`TLBP` is total over `Object`. A TLB is a cons spine ending at the
keyword `:TLB`, with each entry a cons of a 46-bit unsigned key and a
40-bit unsigned page value. The two bits at offset six in the key must
have a value of at most two. Malformed keys are rejected before bit
selection. The lone `:TLB` marker is valid for `TLBP` and is omitted
from sparse records because it is the default.

The provenance boundary is the pinned ACL2 build, certificates, native
replay, exporter, and structural source checker. Lean checks the
arithmetic interpretation and the body equations. The `FLOOR` proof
uses reduced rationals and the existing rational interpretation of the
arithmetic primitives on the indicated integer inputs. General
arithmetic on arbitrary ACL2 objects, the generated key accessor
off its valid-key path, raw stobj alignment, and the machine step are
outside the result.

## Reproduce

Use the [pinned certified checkout](acl2-x86-run.md#reproduce).

```sh
export PYTHONSAFEPATH=1
python3 -B tools/acl2-x86isa/export_x86_run.py --tlb "$work/acl2" "$work/tlb.json"
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Status.TlbTests
python3 -B tools/acl2-x86isa/check_tlb.py "$work/tlb.json"
python3 -B tests/acl2/check_tlb.py
```

Two fresh SBCL sessions produced identical bytes. Lean checks 12
arithmetic, 15 key, and 12 TLB and record observations from the native
logical world. Samples include signed floor cases, division by zero,
key and page boundaries, invalid mode bits, wrong packages, and
malformed entries and tails. The record samples exercise both fields
together and compare native state recognition and both status reads.
The existing environment suite separately checks its rejected cases.
[Lean regressions](../../Silmaril/Logic/ACL2/X86Run/Status/TlbTests.lean)

| Artifact | SHA-256 |
| --- | --- |
| World export JSON | `6f78907ac56fa95d36abc83be9402c617c29bd8c7fd6ee8aa460f72b2ca88cd9` |
| Generated Lean source | `5605546b71ded24d2eee642d5c8e8a82dbda9f58a0d3ebcfc88c627d6f756cf7` |

[tlb]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/tlb.lisp#L237-L301
[bits]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/bitops/part-select.lisp#L63
[ihs]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ihs/basic-definitions.lisp#L156
[axioms]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L6889
