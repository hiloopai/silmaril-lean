# ACL2 8.7 logical integer bit operations

Import `Silmaril.Logic.ACL2.Standard.IntegerBits.Thms` for operations on the standard
`Object` carrier. The implementation uses exact signed Lean integers and the existing
`Object.integerValue?` projection. ACL2 8.7 is pinned at
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`.
[Object model](acl2-standard-objects.md) · [Pinned ACL2 source](https://github.com/acl2/acl2/tree/bc6f4f49e81a0711214a8d91f0d06e0e084d2204)

## x86isa selection

The certified `X86-RUN` export names `X86-FETCH-DECODE-EXECUTE`, with no integer-bit
operators directly in its own translated body. To choose operators below that boundary,
the audit takes a sample of certified declarations from `machine/x86` dependencies.
For each function it inventories calls in `unnormalized-body` after ACL2
`remove-guard-holders`, and inspects measures separately. This removes `:exec` branches
from the comparison and sees macro-expanded calls and home-package symbol identities.
The table lists the operations in this PR found by the sample.
[Certified X86-RUN export](acl2-x86-run.md) ·
[Audit input](../../tests/logic/acl2/audit-x86isa-integer-bits.lsp)

| Sampled declaration in `X86ISA` | World property | Observed operators |
| --- | --- | --- |
| `GPR-AND-SPEC-1$INLINE` | Body | `ACL2::BINARY-LOGAND` |
| `GPR-XOR-SPEC-1$INLINE` | Body | `ACL2::BINARY-LOGXOR` |
| `SHLX-SPEC-32` | Body | `COMMON-LISP::ASH` |
| `VEX-VVVV-REG-INDEX` | Body | `COMMON-LISP::LOGNOT` |
| `RVM16$INLINE` | Body | `ACL2::BINARY-LOGIOR`, `COMMON-LISP::ASH` |
| `GENERAL-PF-SPEC-FN$INLINE` | Body | `COMMON-LISP::LOGBITP` |
| `BITCOUNT8$INLINE` | Measure | `COMMON-LISP::INTEGER-LENGTH` |

`BITCOUNT8$INLINE` has `LOGHEAD$INLINE` and `LOGTAIL$INLINE` calls in its logical
body. Its source `:exec` branches use `LOGAND` and `ASH`. `GENERAL-PF-SPEC-FN$INLINE`
also depends on `LOGCOUNT`. `BITOPS::PART-SELECT-WIDTH-LOW$INLINE` appears in the
AND and XOR specifications. These helpers, fixed-width recognizers and fixers, and
other operations such as `LOGAPP` and `LOGEXT` remain wider dependencies. The sample
is a direct-call audit of selected bodies and one measure. Machine-wide dependency
closure, logical state, and export bindings remain open.
[Pinned flag definitions](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/rflags-spec.lisp#L273-L389) ·
[Pinned shift definitions](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/instructions/shifts-spec.lisp#L1618-L1672)

## Definitions and equations

The ACL2 primitive registry classifies `COMMON-LISP::INTEGERP` and `ACL2::BINARY-+`
as primitives. The seven fixed-arity operations in the table are all defined functions
in the world. `COMMON-LISP::LOGAND`, `LOGIOR` and `LOGXOR` are macros with three cases.
With zero arguments they produce `-1`, `0` and `0` respectively. With one argument
all three use `THE INTEGER`, whose logical equation returns that argument even for
nonintegers. With two or more arguments they nest their binary functions to the right.
The list APIs express the value semantics of these expansions.
[Primitive registry](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/basis-b.lisp#L630) ·
[Macro and binary definitions](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L16996-L17108) ·
[`THE-CHECK`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L12105-L12112)

| Lean API on `Object` | Logical equation |
| --- | --- |
| `binaryLogand` | `ZIP` makes a zero or noninteger input yield zero. An input of `-1` returns the other integer. The recursive digit step takes the AND of the floor-halved operands, doubles it, and adds one exactly when both inputs are odd. |
| `binaryLogior`, `binaryLogxor`, `lognot` | Binary operations use sign extension. `LOGNOT` is `-ifix(x) - 1`. Lean proves the ACL2 `LOGIOR` De Morgan equation and the `LOGXOR` equation expanded through `LOGEQV` and `LOGORC1`. |
| `ash` | Both operands use their integer payload or zero. A nonnegative count multiplies by `2^count`. A negative count floor-divides by `2^(-count)`, including for negative data. |
| `logbitp` | The tested integer uses `ifix`. A negative or noninteger index selects bit zero via `nfix`. The result is `T` exactly when the floor quotient by `2^index` is odd. |
| `integerLength` | Nonintegers, zero and `-1` have length zero. On any other integer the result is one plus the length of its floor half. |

Lean proves the listed equations for the unbounded implementations in the
[theorem header](../../Silmaril/Logic/ACL2/Standard/IntegerBits/Thms.lean).
These equations capture the signed digit recurrences and source arithmetic cases.
Source translation and general native correspondence remain outside the proof.
[`ZIP`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3853-L3861) ·
[`LOGNOT`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L7354-L7356) ·
[`EXPT`, `LOGBITP`, `ASH`](https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L9073-L9137)

## Checks

```sh
lake build --wfail +Silmaril.Logic.ACL2.Standard.IntegerBits.Tests
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.Standard.IntegerBits.Tests +Silmaril.Logic.ACL2.Standard.Objects.Tests'
python3 -I tests/logic/acl2/check-integer-bits.py
```

The Lean tests audit declarations in both public integer-bit modules and their
transitive axiom dependencies against `propext`, `Classical.choice` and `Quot.sound`.
The [snapshot](../../tests/logic/acl2/integer-bits-8.7.txt) records 45 observations,
including mixed signs, shifts and indices beyond 128 bits, noninteger operands and
macro arities. Its SHA-256 is
`6ee22e5d0e72985978aa1028c535143eed6d4032101a7567a390eebec2e1f02c`.
The runner compares Lean and, with the optional pinned checkout, two fresh ACL2 sessions
against those exact observation rows. The native sample uses stock ACL2 with guard
checking set to `:none` to exercise logical completion.
[Guard checking manual](https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____SET-GUARD-CHECKING)

From the Silmaril root, with Git, SBCL and GNU Make, build pinned ACL2 for the native
comparison. The call audit loads five certified dependency books with
`X86ISA_EXEC=nil`. The [C1 inventory](acl2-x86isa.md#reproduce) gives the separate
build and book audit for `machine/x86`.

```sh
acl2_source=$(mktemp -d)/acl2
git clone --depth 1 --branch 8.7 https://github.com/acl2/acl2.git "$acl2_source"
test "$(git -C "$acl2_source" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$acl2_source" LISP=sbcl
python3 -I tests/logic/acl2/check-integer-bits.py --acl2-source "$acl2_source"
(
  cd "$acl2_source/books/projects/x86isa"
  export ACL2_CUSTOMIZATION=NONE X86ISA_EXEC=nil
  ../../build/cert.pl --acl2 "$acl2_source/saved_acl2" --acl2-books "$acl2_source/books" \
    -j 12 machine/instructions/and-spec machine/instructions/xor-spec \
    machine/instructions/shifts-spec machine/register-readers-and-writers machine/application-level-memory
)
ACL2_CUSTOMIZATION=NONE X86ISA_EXEC=nil "$acl2_source/saved_acl2" \
  < tests/logic/acl2/audit-x86isa-integer-bits.lsp
```
