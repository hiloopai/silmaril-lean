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

For the default ACL2 ordinal relation, see [ordinal admission](acl2-ordinal-admission.md).

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

## Connecting admitted blocks to institutions and books

`Silmaril.Logic.ACL2.Recursive.Institution.Thms` puts a block in the existing
`Presentation`. It uses `Body.toTerm` for the new bodies and translates the
old ones along `Block.inclusion`. The resulting signature arrow works with
`inst`, `presentedInst`, `forgetDefinitions`, and the existing syntactic
`pi`. It preserves the resolved package, spelling, and arity of each old
symbol. The presented equations are exactly the translated old equations and
the new members' equations.

`Block.worldExtension` translates the prior theorem table and composes with
`Book.extension`. It requires the new names to be fresh for the theorem table
as well as the function table. A checked input theorem table stays checked.
The recursive block is represented by this world extension. The source-facing
`Book` events still describe nonrecursive definitions and checked theorem
events.

The new equations are hypotheses of π-derivations. Separately,
`Block.modelBy_models` proves that well-founded evaluation satisfies the whole
extended world, and `Block.modelBy_reduct` recovers the input model. Satisfaction
of translated old sentences follows by `Sentence.holds_map`. In
`Block.entails_iff`, reflecting entailment back to the input world uses expansion
for **every** input-world model. A termination proof on one carrier gives that
model's expansion.

The regression transcribes pinned `ACL2::TRUE-LISTP` over standard
`Object`. It checks the positive `CONSP`/CDR certificate and embeds
`ACL2-COUNT` as a finite ordinal for default `O<`. It uses the admitted
equation to prove that a singleton is a true list, checks both ordinary
model reducts, and includes a following theorem book. [Pinned definition][list]

```sh
lake build --wfail +Silmaril.Logic.ACL2.Recursive.Institution.Tests
```

## Checking the pinned translated TRUE-LISTP export

The stock ACL2 8.7 exporter reads the initial world's logical declarations for
`ACL2::TRUE-LISTP` and `COMMON-LISP::EQ`. It records their ordered formals,
arities and unnormalized translated bodies, plus the measure, its domain and
the well-founded relation. Both bodies must already be free of guard holders.
Symbols are serialized with their resolved home packages, including
`COMMON-LISP::NIL` in the quote. [Fixture](../../corpus/acl2/true-listp/acl2-8.7.sexp)

`Silmaril.ProofFormats.ACL2.TrueListp` reads the fixture with the existing Lisp
reader. It checks the resolved names and arities and uses `Translated.lower`
to bind formal occurrences to finite slots. The recursive block is built from
the structural projection of that checked body. The profile checks that the
exported logical `EQ` applies `EQUAL` to its original formals in order, and
that the default-order measure is `ACL2-COUNT` of the single bound formal.
A supplied CDR certificate checks decrease on the actual recursive call.

Lean proves pointwise agreement between evaluation of the checked source
and evaluation of the block body in the admitted standard-object model.
Source evaluation runs the separately checked `EQ` body. The admitted
equation then gives the translated source equation for all arguments.
The institution test uses the same block to obtain the ordinary model
reduct and the equation's syntactic π-derivation. Mutations of the recursive
argument, its governing test, the measure, qualified bindings, call arity,
and the exported equality body are rejected.

The stock ACL2 image supplies translation, package resolution and world
provenance. Lean checks the exported terms and the supplied termination
certificate. Inference of termination certificates and native theorem or
book-certification replay remain outside this case.

Build stock ACL2 8.7 at `bc6f4f49e81a0711214a8d91f0d06e0e084d2204` with
`make LISP=sbcl` in its checkout. The exporter checks that commit and tree,
the tracked checkout and the SHA-256 of `axioms.lisp`. The committed export
has SHA-256 `4dde04074aa4a1e40488121a3f326f5ec79139c03fb08d33c461dbc3e7e277a1`.
The direct Lean run reads the fixture again and prints the axiom audit.

```sh
python3 -B tools/acl2/export_true_listp.py /path/to/acl2
lake build --wfail +Silmaril.ProofFormats.ACL2.TrueListp.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/ProofFormats/ACL2/TrueListp/Tests.lean
```

## Checking the pinned translated BINARY-APPEND export

The same stock ACL2 8.7 image exports `ACL2::BINARY-APPEND` together with the
logical bodies of `COMMON-LISP::ENDP`, `COMMON-LISP::ATOM`, and
`COMMON-LISP::NOT`. The shared reader and typed lowering check qualified
names, arities and lexical slots. The exported definitions give the
complement law for `ENDP` and `CONSP` on standard objects. That law justifies
swapping the conditional branches in the recursive block. Lowering preserves
the recursive call inside `CONS` and the unchanged second argument.
[Fixture](../../corpus/acl2/binary-append/acl2-8.7.sexp) · [Pinned source][axioms]

The supplied CDR certificate checks decrease of the exported `ACL2-COUNT X`
measure under `O<`, using its natural-valued interpretation on standard objects.
Lean proves the admitted equation agrees pointwise with the checked source
body and checks the ordinary and presented model reducts. A subsequent theorem
book derives `BINARY-APPEND NIL Y = Y` from the admitted equation using the
syntactic calculus and exports it as a π-consequence with no added premises.
The handwritten admission regression proves the conditional right identity
`APPEND-TO-NIL` semantically by call induction. Its syntactic derivation remains
open in this source profile. The regression also checks rejection of a changed
helper body, recursive call arity and the nondecreasing `ACL2-COUNT Y` measure.
[Lean regression](../../Silmaril/ProofFormats/ACL2/BinaryAppend/Tests.lean)

Translation, package resolution and world provenance come from the pinned
image. Lean checks the exported terms, the supplied certificate and the
authored theorem event. This case establishes neither termination inference
nor replay of native theorem proofs or book certification.

The committed fixture has SHA-256
`d72acd889da7fdb1419ca388994851d5c59d57b1db15910d2649da594c0f266a`.

```sh
python3 -B tools/acl2/export_recursive.py /path/to/acl2 binary-append
lake build --wfail +Silmaril.ProofFormats.ACL2.BinaryAppend.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/ProofFormats/ACL2/BinaryAppend/Tests.lean
```

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
