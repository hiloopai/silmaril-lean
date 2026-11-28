# Non-default ordinal relations in the pinned x86isa closure

Lean now checks ACL2 8.7's `NAT-LIST-<` and `E0-ORD-<` by transporting
selected recursive-call obligations to the [default `O<` checker][default].
The adapters use the existing model extension and defining-equation proof.
There is a Lean `WellFounded` theorem for each relation on its ACL2 domain.

The source pin is `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. The upstream
GL and RTL books below were certified on that ACL2 8.7 image with SBCL 2.5.2.
The translated bodies, formals, and justification fields were read from the
ACL2 world after inclusion. The measures in Lean are manual transcriptions.
The native certifications and world records provide provenance. The Lean
proofs establish validity and strict decrease independently. The
[x86isa certification graph][inventory] reaches the GL book through
`machine/guard-helpers` and `centaur/gl/gl`, and reaches RTL through the
floating-point instruction books and `rtl/rel11/lib/reps`.

## NAT-LIST-< and GL

`Silmaril.Logic.ACL2.NatListMeasure.Thms` implements the definition of
`NAT-LIST-MEASURE`. Its domain is all ACL2 objects. For an atom the measure
is `NFIX` of the atom. For a cons it is
`(make-ord (len x) (+ 1 (nfix (car x))) (nat-list-measure (cdr x)))`.
Here `LEN` counts the cdr spine and the final atom of an improper list
contributes its own `NFIX`. The encoding retains all distinctions used
by the definition. `valid` proves the counterpart of
`O-P-OF-NAT-LIST-MEASURE`. The `lt_cons_cons` and `lt_of_atom` laws
characterize length-first order, then lexicographic order on the NFIXed
entries and the final atom. Two different ACL2 objects may compare equal.
`Terminates.toOrdinal` transports a path-conditioned decrease without any
input-domain premise, as in the ACL2 rule `NAT-LIST-WFR`.
[Pinned definitions and rule][nat-list]

The native justifications from `centaur/gl/ctrex-utils` contain these measures
with relation `ACL2::NAT-LIST-<` and measure predicate `T`.

| Real definition | Measure before applying NAT-LIST-MEASURE |
| --- | --- |
| `GL::MAGICER-EV` | `(cons clk (cons (acl2-count x) 'nil))` |
| `GL::MAGICER-EV-LST` | `(cons (pos-fix clk) (cons (acl2-count x) 'nil))` |

The Lean regression admits a two-argument projection of the mutual block. It
checks the lambda argument-list call from `MAGICER-EV` on `(cdr x)` with the
same positive clock. It also checks the list member's `CAR` call to
`MAGICER-EV` and `CDR` call to `MAGICER-EV-LST` at the original clock. The
list fixture requires the `CDR` call to decrease even on executions where
the upstream member exits after an error in the `CAR` call. The fixture
carrier retains the source count of an atom, with the pinned cons equation
`1 + acl2-count(car x) + acl2-count(cdr x)`. It models the measures even for
nonpositive clocks. A separate theorem checks the exported fallback call with
`(1- clk)` for any resolved body, whose count can increase.
[GL mutual definitions][gl] · [Pinned ACL2-COUNT][acl2-count]

The native probe evaluated the real `MAGICER-EV` on a quoted lambda
argument and a zero-clock case, and the real list member on two quoted
arguments. The Lean executable outputs are observations of the authored projection.
The full upstream evaluator still needs state and multiple values, the
remaining paths and calls, evaluated-result tests, and source-to-model
correspondence for the translated body. The fallback theorem checks its
termination measure and leaves dynamic world lookup outside the model.

## E0-ORD-< and RTL

`Silmaril.Logic.ACL2.LegacyOrdinals.Thms` implements the full
`E0-ORDINALP` domain. A value is a natural or a cons whose car is a
nonzero ordinal exponent. Exponents along the cdr spine are nonincreasing,
so repetitions are allowed. The `E0-ORD-<` comparison uses exponent order,
structural equality of exponents, and cdr order. The proved comparison
equivalence is on recognized inputs. The `ATOC` translation adds each
omega power to the translated cdr and combines repeated exponents. Lean
proves that this yields a valid `O-P` and preserves and reflects the strict
order. The adapter requires `E0-ORDINALP` on every call state.
[Pinned legacy definitions and ATOC theorems][legacy]

In `rtl/rel11/support/definitions`, `RTL::EXPE` records
`(RTL::EXPO-MEASURE (ACL2::REALFIX X))` and `RTL::EXPO` records
`(RTL::EXPO-MEASURE X)`. Both select `ACL2::E0-ORD-<` with
`ACL2::E0-ORDINALP`. The Lean measure implements standard ACL2's rational
cases. Nonrational input yields zero. A negative rational yields
`(2 . 0)`, a nonnegative rational below one yields `(1 . floor(1/x))`
using total reciprocal, and rationals at least one yield `floor(x)`.
The regression proves `EXPE`'s three strict decreases on rationals
for negation, multiplication below one, and division at or above the radix.
The multiplication and division proofs work for every rational radix
at least two, including the upstream integer radices.
[Pinned RTL measure and functions][rtl]

The authored `SILMARIL::EXPE-DOUBLE` fixture isolates the actual
`EXPE` multiplication edge at radix two, uses the exported `REALFIX`
measure, and sends its termination proof through the adapter. It returns
the first argument outside the branch, so its value is a fixture observation.
The full RTL result semantics and `EXPO`'s executable `MBE` branch remain
outside the translation.

## Verification

```sh
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.NatListMeasure.Tests +Silmaril.Logic.ACL2.LegacyOrdinals.Tests +Silmaril.Logic.ACL2.OrdinalAdmission.Tests +Silmaril.Logic.ACL2.Recursive.Tests'
```

The test modules print the axiom dependencies of the relation theorems,
transport into the checker, and projected admissions. For native
reproduction, build the pinned ACL2 with `make LISP=sbcl`, then run from
its root.

```sh
ACL2="$PWD/saved_acl2" ACL2_CUSTOMIZATION=NONE X86ISA_EXEC=nil \
  books/build/cert.pl -j 14 books/centaur/gl/ctrex-utils books/rtl/rel11/support/definitions
```

After including `centaur/gl/ctrex-utils` and `rtl/rel11/support/definitions`
with `:dir :system`, the justification
properties are available through the raw Lisp world. For example, after
`:q` the following retrieves the exact translated measure, relation, and
predicate for `MAGICER-EV`.

```lisp
(let* ((w (acl2::w acl2::*the-live-state*))
       (j (acl2::getpropc 'gl::magicer-ev 'acl2::justification nil w)))
  (list (acl2::access acl2::justification j :measure)
        (acl2::access acl2::justification j :rel)
        (acl2::access acl2::justification j :mp)))
```

The SHA-256 of `centaur/gl/ctrex-utils.lisp` is
`df6b53a9331b2f05272ce354f928ac5fd5c330a1616da2e50a2a4ecc6f095cec`.
The SHA-256 of `rtl/rel11/support/definitions.lisp` is
`2d7c23dca2da8a3f9c8764f8030da49ce3a3453026a03ef6ea52a706e0a1fa8b`.
The SHA-256 of `std/basic/two-nats-measure.lisp` is
`d5e5f6505646b1158d6159fd23f19cd3cff9e6beee902384e81abc14d230d1da`.
The SHA-256 of `ordinals/e0-ordinal.lisp` is
`1f2c4bd82f7182db427681c499683062d18f844c4b364cb372c2072c41e42702`.
The native world and execution log has SHA-256
`74c0e8ec9a6529d444e7c206072f02fcf76833d03d641982ce48fee5a40d26a0`.

The complete x86isa logical closure still needs term and measure
translation, recognition of relation selectors from world records, and
termination proofs for the rest of the definitions. This change supplies
adapters for the two relations used in the examples above.

[default]: acl2-ordinal-admission.md
[inventory]: acl2-x86isa.md#dependency-inventory
[nat-list]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/std/basic/two-nats-measure.lisp#L128-L286
[acl2-count]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L2355-L2382
[gl]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/gl/ctrex-utils.lisp#L200-L268
[legacy]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ordinals/e0-ordinal.lisp#L36-L148
[rtl]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/rtl/rel11/support/definitions.lisp#L648-L718
