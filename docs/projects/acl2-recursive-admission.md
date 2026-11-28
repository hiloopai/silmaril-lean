# ACL2 recursive admission in Lean

`Silmaril.Logic.ACL2.Recursive.Thms` checks total logical definitions over an
existing ACL2 `Model`. A `Block` adds fresh package-qualified names and arities
to the old signature. Members can call each other, with a shared state space
that records the callee, arity, and arguments. A `Rank` maps these states to
`Nat`. `Block.Terminates` requires a strict decrease at each recursive call
under the tests on its path and for every assignment of the formal variables.
The tests follow ACL2's non-NIL convention. The body syntax allows old-world
terms for tests and recursive-call arguments, and old-world contexts that
combine recursive results. A context contributes all its argument obligations,
including ones it could ignore. Recursive results in tests or recursive-call
arguments, general ordinal relations, and unrestricted ACL2 events are outside
this fragment.

`Block.model` constructs the extension by well-founded recursion.
`Block.model_reduct` gives back the input model along the named inclusion, and
`Block.equation_holds` verifies each ordinary ACL2 defining equation in the
extended model. `Block.callInduction` gives the induction hypotheses for the
calls selected by the body and its branch tests. These results require neither
host admission nor any guard hypothesis. Nonrecursive dependencies come from
the supplied old model.

## Certificate and value-model interface

The first certificate rule checks a recursive call whose callee's measured
argument is the `cdr` of the caller's measured argument. The checker requires
an enclosing positive `consp` test on that same variable. Each member chooses
its argument through `MeasureArgument`; calls may change arity or argument
position. `Certificate.check` constructs the path from the body and checks the
certificate against the full body. A call certificate supplies an index into
that path, counted from the innermost test. A missing child, mismatched
certificate shape, wrong branch polarity, wrong variable, or non-decreasing
argument fails this check.

`BlockCertificate.Accepted` requires the Boolean check to succeed for every
declared member. The caller supplies the member-indexed certificates and Lean
proof of coverage by this check. `BlockCertificate.terminates` turns acceptance
and `CdrSize` into the evidence consumed by `Block.model`. A concrete value
model implementing the existing `Primitives` interface needs only to supply
`CdrSize.size : Value → Nat` and prove `cdr_lt` under a positive `consp`. The
size can be the ACL2 count, a spine measure, or any natural measure with this
law. The general admission API also accepts direct `Block.Terminates` proofs
for other ranks. New certificate rules can prove the same obligations.

The certificate trees are entered manually in Lean. This change supplies
neither a serialization format nor a certificate extractor. It does not
implement source macro expansion, package resolution, `make-event`,
`encapsulate`, stobjs, guard verification, or `:program` events. It also
does not certify an `mbe` executable branch. An adapter can feed translated
logical bodies to the typed API. Such an adapter needs separate evidence
linking its input and expansion to source.

## Pinned definitions and induction

The worked example manually transcribes `TRUE-LISTP` and `BINARY-APPEND` from
ACL2 8.7, with `axioms.lisp` SHA-256
`50247ed0609257bcf08c4c6d365ccf1695bd2cbd2dfedff0f7bc516f9ce828b1`.
It expands logical `EQ` to `EQUAL` and uses `CONSP` with swapped branches for
logical `ENDP` (which is `ATOM`). The two-argument `APPEND` in the source
statement expands to `BINARY-APPEND`. These are manual translations of the
displayed logical definitions and theorem, including on improper lists. The
fixture uses a small separate carrier with a natural right-spine measure.
[TRUE-LISTP source][list] · [BINARY-APPEND and APPEND-TO-NIL source][axioms]

The same checker admits both upstream blocks and a synthetic mutual block
with different arities and measure positions. The Lean reconstruction of
`APPEND-TO-NIL` uses the admitted equations, the generic call induction, and the
carrier law that a cons is reconstructed by its car and cdr. It proves
`Sentence.Holds` for the transcribed statement. The branch proofs are ordinary
Lean proofs supplied by hand. They do not replay ACL2 proof search or give a
general correspondence between ACL2 theorem artifacts and Lean derivations.

The regression module also checks malformed certificates and computations on
improper lists and across mutual calls. Run the targeted build with the
repository's pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Logic.ACL2.Recursive.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Logic/ACL2/Recursive/Tests.lean
```

To inspect the independent native observations on the pinned revision, build
ACL2 with `make LISP=sbcl`, then run these commands in `saved_acl2`.

```lisp
:pe binary-append
:pe true-listp
:pe append-to-nil
:q
(dolist (name '(binary-append true-listp endp eq append-to-nil))
  (let ((world (w *the-live-state*)))
    (format t "~&~s~%" name)
    (dolist (prop '(formals unnormalized-body justification induction-machine guard theorem))
      (let ((val (getpropc name prop :absent world)))
        (unless (eq val :absent) (format t "  ~s = ~s~%" prop val))))))
(lp)
```

The world records `ACL2-COUNT` of the first formal and `O<` for both recursive
definitions. For `BINARY-APPEND`, the induction machine records a base case on
`(ENDP X)` and the call `(BINARY-APPEND (CDR X) Y)` on its false branch. The
corresponding `TRUE-LISTP` call is on the positive `(CONSP X)` branch. A probe
with fresh function names can reproduce the conditions and induction scheme
independently of the Lean certificates. Trace `termination-machine`,
`guess-measure`, and `induction-machine-for-fn` around the two renamed defuns,
then use the renamed append call as the induction hint for the renamed theorem.
Admission output, world properties, traces, and native book certificates are
provenance or diagnostics.

## Next step for X86-RUN

The [C3 X86-RUN slice](acl2-x86-run.md) documents the implemented export and
conditional admission against the pinned ACL2 world.

1. Certify and include the pinned `machine/x86.lisp` and use the C1 world
   export to obtain the translated `X86ISA::X86-RUN`,
   `X86ISA::X86-FETCH-DECODE-EXECUTE`, and `X86ISA::X86-RUN-HALTED` terms.
   Extend the export for `X86-RUN` with `justification` and
   `induction-machine`. Bind the exported formals and dependencies by name and
   arity. The source is a `define` with a stobj parameter and `mbe`.
   [Pinned x86 source][x86] · [C1 world export][c1]
2. For the first Lean admission, supply an old model for the total logical
   `FAULT`, `MS`, `ZP`, decrement, and step functions. Use the exported
   logical branch of `mbe`, and represent the three exits as tests on
   `FAULT x86`, `MS x86`, and `ZP n`. The remaining path calls `X86-RUN` on
   the decremented count and the logical step result. Rank by the natural
   projection of the count. Prove that `ZP n = NIL` implies a positive
   integer count and that the translated decrement strictly lowers that rank.
   This uses ACL2's total integer laws, including the `ZP` result for
   non-integers. Supply that proof through `Block.Terminates` first, then add a
   checker rule for the negative `ZP` path and translated decrement.
3. Use `Block.equation_holds` to reconstruct the translated
   `X86-RUN-HALTED` formula from the two early exits. At this stage the result
   is relative to the supplied state and step model. A full machine result
   still needs the checked declaration closure and logical stobj operations,
   a state relation for both machine views, and source and execution
   correspondence for the exported machine.

[list]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L2155
[axioms]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/axioms.lisp#L3315
[x86]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/x86.lisp#L653
[c1]: https://github.com/hiloopai/silmaril-lean/pull/4372
