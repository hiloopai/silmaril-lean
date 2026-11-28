# ACL2 8.7 X86-RUN export and Lean admission

This C3 slice binds one recursive declaration, `X86ISA::X86-RUN`, and the
statement of `X86ISA::X86-RUN-HALTED` to the certified logical
`machine/x86` world with `X86ISA_EXEC=nil`. The checkout is pinned to
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tree
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. The exporter includes the book in a
fresh SBCL ACL2 process, checks the completed root certificate, and rejects
skipped-proof, axiom and trust-tag annotations and the native syscall support
marker. [Pinned machine source][x86] · [C1 inventory](acl2-x86isa.md) ·
[Recursive admission API](acl2-recursive-admission.md)

The [world artifact](../../corpus/acl2/x86-run/acl2-8.7.json) retains the
`unnormalized-body` world property, its logical projection from ACL2's
`remove-guard-holders`, guard, stobj signatures, symbol class, recursive clique,
justification, measure, measure domain and well-founded relation, induction
machine, and the formula returned by ACL2's `termination-theorem`. The
reference table contains the live arities of the named functions in the
logical body and halted formula. A symbol is serialized as
`["symbol", package, name]` using ACL2's `symbol-package-name`. Proper lists,
dotted pairs, integers, and strings retain their structure. Both Lean terms
use the exported formal order `(ACL2::N, X86ISA::X86)` for their variable
indices. The world records `ACL2-COUNT` on `ACL2::N`, domain `O-P`, relation
`O<`, and four induction cases. The last case records the recursive call
when `FAULT`, `MS` and `ZP` all return NIL. [ACL2's reconstructed termination theorem][termination]

The [checker](../../tools/acl2-x86isa/check_x86_run.py) pins the exact bytes,
resolves applications by package, name and arity, and substitutes translated
lambda applications by their explicit formals. The outer lambda's quoted
function name drops out because its `__FUNCTION__` formal is unused. The
checker translates the logical body into `Recursive.Body` and the halted
formula into `Sentence`, compares
both with the [generated Lean module](../../Silmaril/Logic/ACL2/X86Run/Source.lean),
and asks Lean to type-check the generated source. The existing ACL2 syntax
represents quoted NIL and T directly. A reserved nullary symbol represents
the quoted integer -1 in the old signature and its interpretation is bound
by an explicit arithmetic premise.

The [Lean header](../../Silmaril/Logic/ACL2/X86Run/Thms.lean) uses an arbitrary
old `Model` over the named operations and `CountLaws` over its value carrier.
The laws give the positive-integer consequence of a NIL `ACL2::ZP` result,
identify the quoted -1, and relate `ACL2::BINARY-+` to integer addition. Lean
uses the natural projection of the count on the remaining branch to
construct a total recursive model. The two early exits use only the NIL
status of the interpreted `FAULT` and `MS` calls. The reconstructed halted
theorem proves satisfaction of the generated corpus statement in that model.

## Trust boundary and remaining closure

The pinned ACL2 build, its certificates and expansion, the Lisp exporter,
and the Python translation are the provenance and source-translation
boundary. Lean checks the resulting typed terms and the conditional
admission and theorem proofs in the single ACL2 value sort. ACL2's ordinal
termination formula and induction machine are retained evidence. The Lean
proof uses its own natural rank and the generic block admission API. The
stobj signatures and guard are retained as data.

Closing the machine result requires binding the named operations and literal
to a checked ACL2 value model, importing the declaration and constraint
closure of `FAULT`, `MS` and `X86-FETCH-DECODE-EXECUTE` including the
generated dispatcher and logical stobj operations, and proving a state
relation for both machine views and the environment. The value model can
supply the existing `Primitives` carrier, the named interpretations, and
proofs of `CountLaws`. An independent source or expansion correspondence proof
would replace the current provenance boundary.

## Reproduce

From the Silmaril root, with the pinned Lean toolchain, Git, Python 3.9+, SBCL,
Perl and GNU Make. Reuse a completed certification cache for this checkout
and profile if available.

```sh
work=$(mktemp -d)
git clone --depth 1 --single-branch --branch 8.7 https://github.com/acl2/acl2.git "$work/acl2"
test "$(git -C "$work/acl2" rev-parse HEAD)" = bc6f4f49e81a0711214a8d91f0d06e0e084d2204
make -C "$work/acl2" LISP=sbcl
(
  cd "$work/acl2/books/projects/x86isa"
  export ACL2_CUSTOMIZATION=NONE CERT_PL_NO_COLOR=1 X86ISA_EXEC=nil
  ../../build/cert.pl --acl2 "$work/acl2/saved_acl2" --acl2-books "$work/acl2/books" \
    -o "$work/certify.mk" -j 16 machine/x86
)
python3 -B tools/acl2-x86isa/export_x86_run.py "$work/acl2" "$work/x86-run.json"
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Thms
python3 -B tools/acl2-x86isa/check_x86_run.py "$work/x86-run.json"
python3 -B tests/acl2/check_x86_run.py
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.Thms +Silmaril.Logic.ACL2.Recursive.Tests'
```

Two fresh SBCL 2.5.2 sessions using the certified checkout produced identical
export bytes. SHA-256 values for the local reproduction follow.

| Artifact | SHA-256 |
| --- | --- |
| Export JSON | `ad779373d1802ecd4dcedb27d23b3ca6bdb6303acb10c2d25e572cc9268fc269` |
| Generated Lean source | `f1f905289375364f3caa84b9c1f1566212d69d818e587a44975644a94c6de9d1` |
| Upstream `machine/x86.lisp` | `e73251b5ea07fdb524d3530006ed268be9ebe1756d9e85abb29d34d08c006f85` |
| Local `machine/x86.cert` | `10f1d0ab74de7007d9fb0f7e293f83288254e94504ebf7e64192c37d0887d4f4` |

ACL2's raw certificate bytes can vary with the host, directory, and
certification options. The check pins the exported data.

The regression suite rejects 13 mutations covering the package, arities,
scope, decrement, formal order, body, halted formula and admission metadata.
The original C1 machine inventory also produced byte-identical manifest and
world sample files before and after the certificate-reader refactor.

[x86]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/x86.lisp#L653
[termination]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/history-management.lisp#L12758
