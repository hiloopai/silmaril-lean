# ACL2 logical MV-NTH, EQL and NOT

`Silmaril.Logic.ACL2.Standard.Pure.Thms` supplies total interpretations of
`ACL2::MV-NTH` (arity 2), `COMMON-LISP::EQL` (arity 2) and
`COMMON-LISP::NOT` (arity 1). The binding lookup requires the exact home
package, spelling and arity. It uses only the standard `Object` carrier.
[Definitions](../../Silmaril/Logic/ACL2/Standard/Pure/Defs.lean) ·
[Equations](../../Silmaril/Logic/ACL2/Standard/Pure/Thms.lean)

## Source and equations

The artifact retains the unnormalized and guard-holder-free translated
bodies, package identities, formals, arities, guards and stobj signatures
from the certified ACL2 8.7 machine world with `X86ISA_EXEC=nil`.
The commit is `bc6f4f49e81a0711214a8d91f0d06e0e084d2204` and the tree is
`66d80ea68f664b931f8982b607fe2305f3cec0e4`. The source declarations are
stock ACL2 definitions. `ATOM` is included as the translated list test.
The native `MV-NTH` justification and termination formula are also
retained. [World artifact](../../corpus/acl2/pure-helpers/acl2-8.7.json) ·
[Pinned MV-NTH][mv] · [Pinned EQL and ATOM][eql] · [Pinned NOT][not]

The checker pins the full export, resolves the translated formal and call
identities and arities, then emits typed Lean functions for the bodies.
Lean proves the equations for all standard objects, including the
equation substituting the total `Object.mvNth` for the recursive call.
It admits that function by structural recursion on the cons spine. The
translated decrement keeps the source operand order, `(BINARY-+ '-1 N)`.
The existing `ZP`, equality, arithmetic and projections supply the
primitive interpretations. `ZP` already has a standard binding, an
all-object characterization, and native observations.
[Source checker](../../tools/acl2-x86isa/check_pure_helpers.py) ·
[Generated bodies](../../Silmaril/Logic/ACL2/Standard/Pure/Source.lean) ·
[Standard objects](acl2-standard-objects.md)

An atomic remainder always gives NIL for `MV-NTH`. On a cons, a
nonpositive or noninteger index returns the car. Only a positive integer
consumes a cell. An improper tail therefore gives NIL when traversal
reaches it. Logical `EQL` calls structural `EQUAL` even on strings and
conses. `NOT` returns T only for NIL, including when its argument is
outside conventional Boolean inputs.

The source boundary is the pinned certified world, the Lisp exporter,
and the Python translation into the standard primitive interpretations.
Lean checks the total equations. This is a pure library slice. Machine
state operations and instruction dispatch are outside its scope.

## Reproduce

Use the [pinned certified checkout](acl2-x86-run.md#reproduce).

```sh
export PYTHONSAFEPATH=1
python3 -I tools/acl2-x86isa/export_x86_run.py --pure-helpers "$work/acl2" "$work/helpers.json"
lake build --wfail +Silmaril.Logic.ACL2.Standard.Pure.Tests
python3 -I tools/acl2-x86isa/check_pure_helpers.py "$work/helpers.json"
python3 -I tests/acl2/check_pure_helpers.py
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.Standard.Pure.Tests +Silmaril.Logic.ACL2.Standard.Objects.Tests'
```

Two fresh SBCL sessions produced identical bytes. The warning-strict Lean
tests check 36 native results collected with guard checking disabled,
including improper lists, non-natural indices, package-distinct symbols,
non-eqlable values and non-NIL zero. They audit the equations and lookup
for permitted axioms. The source mutations exercise call identities,
arities, bodies, an off-guard observation and the termination formula.
[Lean regressions](../../Silmaril/Logic/ACL2/Standard/Pure/Tests.lean)

| Artifact | SHA-256 |
| --- | --- |
| World export JSON | `22599f92ca4704e7f1ef4fa350d18a6e22b32f4303f0656977ad745f110e4fce` |
| Generated Lean source | `601e1762ecdf961f42cf29047610c760b3569ee59ba0e92b3729bd351271a2d6` |

[mv]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L6727-L6734
[eql]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L2479-L2489
[not]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L2113-L2115
