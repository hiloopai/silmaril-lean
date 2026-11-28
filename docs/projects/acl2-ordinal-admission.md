# ACL2 default ordinal admission

`Silmaril.Logic.ACL2.OrdinalAdmission.Thms` extends the typed recursive block
admission from [#4401][natural]. It covers all canonical ACL2 8.7 `O-P` values,
which represent ordinals strictly below ε₀. The measure validity obligation
ranges over every call state, including inputs outside guards and states with
no recursive calls. Every taken recursive call must strictly decrease under
`O<`. The same body evaluator gives the extended model, its defining equations,
and induction over its recursive calls. Existing natural-rank entry points use
the same evaluator and retain their signatures and certificate checker.

## Representation and correspondence

An `Encoding` is a natural atom, any other atom, or a cons. Collapsing other
atoms preserves rejection by `O-P`. A finite ordinal is its natural atom.
`MAKE-ORD(e, c, r)` constructs `((e . c) . r)`. The exponent `e` is a nonzero
ordinal, the coefficient `c` is a positive integer, and the remainder `r` is
an ordinal whose leading exponent is smaller than `e`. The leading exponent
of a finite remainder is zero. Both the exponent and remainder may themselves
be nonfinite. The comparator uses the finite case, then compares exponents,
coefficients and remainders in that order. Its correspondence contract is on
valid ordinal encodings. [Pinned ACL2 definitions][axioms] · [O-P manual][op] ·
[O< manual][olt]

`Encoding.oP_iff` identifies exactly the images of Mathlib's normal
`ONote`s. Both conversions round trip on these domains. A positive finite
ordinal in `ONote` has exponent zero and an empty remainder, so it maps to a
natural atom. `ValidOrdinal.cmp_eq_eq` establishes equality of ACL2 encodings
in the equal-exponent case, as required by ACL2's `EQUAL` test.
`Encoding.oLt_makeOrd_iff` gives the three comparison clauses for infinite
ordinals. `ValidOrdinal.lt_iff` identifies the strict comparison with the denoted order,
and `ValidOrdinal.wellFounded` pulls back Mathlib's ordinal well-foundedness.
`ValidOrdinal.ofEncoding?` returns `none` for invalid encodings. Admission
uses the raw encoding comparator and requires kernel-checked proofs of
validity and of the path-conditioned strict decreases.

The source pin is ACL2 8.7
`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`. The SHA-256 of
`axioms.lisp` is
`50247ed0609257bcf08c4c6d365ccf1695bd2cbd2dfedff0f7bc516f9ce828b1`.
The pinned manual source is also available in the release tree. The Mathlib
notation dependency comes from the repository's existing Lake pin.
[Manual source][manual-source] · [Pinned Mathlib notation][notation]

## Regression and pinned upstream validation

The Lean test transcribes the pinned `TWO-NATS-MEASURE` body, including the
input projections `NFIX`, and proves its `O-P` and lexicographic `O<` laws.
Its value is ω²·(1 + nfix(a)) + ω·(1 + nfix(b)). The authored
`ORDINAL-DRAIN` test decrements the second counter when positive. Once it
drains, the test decrements the first counter and resets the second to the
old first counter. This exercises strict decrease despite an increase in the
second component, which the single-argument CDR certificate does not express.
The test proves the admitted equation over its fixture model and executes
the reset and a non-natural input. It also checks nested exponents and rejects
invalid atoms, malformed pairs, zero coefficients or exponents, and equal or
increasing exponents in the remainder. [Pinned measure and lemmas][measure]

The upstream book `std/basic/two-nats-measure` was certified on the pinned
ACL2 8.7 image with SBCL 2.5.2. The source SHA-256 is
`d5e5f6505646b1158d6159fd23f19cd3cff9e6beee902384e81abc14d230d1da`.
The ACL2 image admitted the authored fixture using default `O<`, displayed
its measure conjecture, and passed concrete assertions about the measure,
validity checks and both fixture outputs. This independently validates the
pinned measure and fixture. The Lean proof uses a separate local carrier.

```sh
lake build --wfail +Silmaril.Logic.ACL2.OrdinalAdmission.Tests +Silmaril.Logic.ACL2.Recursive.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Logic/ACL2/OrdinalAdmission/Tests.lean
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Logic/ACL2/Recursive/Tests.lean
```

The regression modules print theorem dependencies for the axiom audit. To
reproduce the native admission, check out the pin above, build with
`make LISP=sbcl`, run `ACL2="$PWD/saved_acl2" books/build/cert.pl books/std/basic/two-nats-measure`,
and submit these events in `saved_acl2`.

```lisp
(include-book "std/basic/two-nats-measure" :dir :system)
(defun ordinal-drain (x y)
  (declare (xargs :measure (two-nats-measure x y)
                  :verify-guards nil))
  (if (posp y)
      (cons t (ordinal-drain x (nfix (1- y))))
    (if (posp x)
        (cons t (ordinal-drain (nfix (1- x)) x))
      nil)))
(assert-event (equal (ordinal-drain 2 0) '(t t t t t)))
(assert-event (equal (ordinal-drain nil 2) '(t t)))
```

## x86isa closure boundary

The follow-up [non-default relation adapters](acl2-x86isa-ordinal-relations.md)
check selected measures from the GL and RTL books described below.

The [x86isa inventory procedure](acl2-x86isa.md#reproduce), run for `machine/x86`
with `X86ISA_EXEC=nil`, returned 1,030 certificate targets and 1,163 sources.
The following are examples from a source scan of that build closure. The
scan is at book level and does not identify every translated logical admission
event. Its manifest SHA-256 is
`dd1fcef3c277b0ba32bee24966b72dc572ad52b8fce60e74864b52475e154fd3`.

- GL's `MAGICER-EV` declares `ACL2::NAT-LIST-<` with measure
  `(list clk (acl2-count x))`. The corresponding `NAT-LIST-MEASURE` mapping
  yields ordinals in the implemented domain. The follow-up checks the
  list-measure adapter and selected recursive calls.
  [GL source][gl] · [NAT-LIST-< rule][nat-list]
- RTL's `EXPE` and `EXPO` use legacy `E0-ORD-<` with `EXPO-MEASURE`.
  Its `(2 . 0)` and `(cons 1 (fl (/ x)))` forms use the old encoding.
  The follow-up checks the legacy correspondence and the RTL measure.
  [RTL source][rtl] ·
  [ACL2 legacy ordinal book][legacy]
- The ordinal-bearing `MAKE-ORD` measure in `TOOLS/FLAG` is in a
  `:program` declaration. Source event expansion and program-mode execution
  lie outside this checked logical admission. [FLAG source][flag]

The implementation consumes typed bodies and a measure on their states.
Source translation, replay of upstream termination proofs, stateful
`stobj` operations, guards, `mbe` executable branches and nested calls
inside recursive-call arguments remain separate work. This validation uses
the pinned small book, and the x86isa analysis uses the dependency inventory
and source inspection. The full x86isa definition closure has yet to be
admitted in Lean.

[natural]: https://github.com/hiloopai/silmaril-lean/pull/4401
[axioms]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L5064-L5150
[op]: https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____O-P
[olt]: https://www.cs.utexas.edu/users/moore/acl2/v8-7/combined-manual/index.html?topic=ACL2____O_C3
[manual-source]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/system/doc/acl2-doc.lisp#L110122
[notation]: https://github.com/leanprover/downstream-lean4/blob/569134c2fc750d92baa85d50cd925a7e20a93dd2/mathlib4/Mathlib/SetTheory/Ordinal/Notation.lean
[measure]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/std/basic/two-nats-measure.lisp#L103-L124
[gl]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/centaur/gl/ctrex-utils.lisp#L200-L208
[nat-list]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/std/basic/two-nats-measure.lisp#L247-L259
[rtl]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/rtl/rel11/support/definitions.lisp#L648-L714
[legacy]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/ordinals/e0-ordinal.lisp
[flag]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/tools/flag.lisp#L1472-L1476
