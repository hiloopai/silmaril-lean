# Seeded execution for checked Python modules

`Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded`
consumes the checked instruction stream from the ordinary module-call
compiler. Callers opt in by passing a `Core.Module.SeededCall.Namespace`
to `Seeded.run`. Module bindings and builtin bindings remain separate
throughout execution. The ordinary module runner has its own entry point.
[Seeded entry](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Seeded/Defs.lean)
· [Closed host-free calls](python-module-seeded-call.md)

The seeded profile admits integer literals, global reads, single-name
assignments, truth assertions, and fixed-positional calls to the closed
descriptors. Calls also accept exact Boolean literals as positional operands.
A call can discard its result, bind it after success, or use
it as a direct assertion condition. An argument may itself be a named
call with literal or name operands. The runner saves the outer callee
first, evaluates arguments from left to right, and invokes the saved
value only after every argument returns. An instruction failure keeps
its incoming module bindings and skips the remaining instructions.
[Python evaluation order](https://docs.python.org/release/3.12.13/reference/expressions.html#evaluation-order)

For message-free `assert not test`, the seeded runner uses the same
operands as a positive assertion.
It evaluates the operand once, then checks for a false value. A
failed operand read keeps its defined error, and a truthy operand
raises an empty `AssertionError`. Both paths preserve earlier module
bindings.

Scalar equality evaluates its left and right operands in order and uses
the ordinary module's integer and Boolean comparison. The Boolean result
can be bound, tested, or used in a later scalar comparison. Boolean
literals are admitted inside equality. Equality on `None`, exception
classes, and helper values is unsupported. Arithmetic and standalone
Boolean literals remain outside the seeded operand profile.

The runner handles the checked stream at module instruction granularity.
A module-level function can be published as the same empty-capture
function value used by the ordinary runner. Publication checks its code
reference and layout in the compiled ordinary table. The binding shadows
builtin fallback, and publication leaves every other binding and the
ordinary heap intact. A missing key or mismatched layout reports the
exact module `publicationFault`. `run_publication` and
`run_publication_fault` give the exact continuation or residual state.

A direct named call to the typed exception-expectation helper can run a
function published earlier in the same module execution. The callback
must have zero positional parameters and receive zero arguments.
The runner uses the ordinary call and delivery path with the current
module-first namespace and shared heap. Integers, Booleans, `None`, and
ordinary functions can cross the lookup boundary. A read of a seed-only
class, helper or builtin descriptor is unsupported, including when the expectation would
have caught a genuinely missing name.

After a matching defined exception, the helper returns `None` and records
the caught error. An unmatched exception propagates. A normal callback
return raises the helper's configured missing-exception diagnostic.
An executor fault or a live prefix at the explicit fuel limit
stops module execution with its own outcome and retains the current heap.
The closed dispatcher still handles closed callbacks. Ordinary callbacks
in nested helper calls and constructing exception instances remain unsupported.

A flat zero-argument call used as a statement can invoke a checked
zero-parameter ordinary function. The resolved descriptor must occur in
the same run's successful-publication ledger. The callee comes from the
current module-first lookup, so rebinding and aliasing follow that lookup.
The call uses the same ordinary preparation, namespace projection and
heap as the callback path.

A flat factory assignment accepts the live descriptor of a function
published or bound as a factory result in this run. It binds up to three
positional integer or `None` values in declaration order. The module
adapter carries a literal `None` as the singleton tag and the ordinary
binder writes that exact value into the destination slot. A checked
factory returns a lexical closure directly or through up to two lexical
wrappers. The runner reads the live callee and evaluates arguments from
left to right before invoking it. A successful closure result writes
the module destination and records the exact descriptor and reached
heap. Its captures keep the original cell identities.
[Argument and binding theorems](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Seeded/Thms.lean)

A nested module call saves its outer callee before evaluating arguments.
A direct zero-argument argument call can use the published selector.
When the saved outer callee is the integer equality helper and its result
is discarded, an argument can also call a closure saved by a factory
assignment in this run with no arguments or one integer. The ordinary
invocation uses the live namespace and the saved closure's cells. The runner carries the
reached heap and any settled receipt to later arguments and then invokes
the saved helper through the closed dispatcher.

A settled call records one receipt with an empty caught field. Defined
errors and seed-only operand lookups retain the current bindings and skip
the tail. The latter yield unsupported. A faulted or live executor state
preserves the exact residual heap and yields `directCallFault` or
`directCallFuelExhausted` with no settled receipt. The default limit is
1000 ordinary transitions per invocation.

A module `co_varnames` assertion reads the current receiver once using
the seeded module-first resolver. A module binding masks the builtin
even when the module value cannot be inspected. The assertion shares
the ordinary checked CPython 3.13.5 tuple and exact code-point
comparison. False membership, including in an explicit empty tuple,
raises an empty `AssertionError`. A missing receiver raises
`NameError`, an unprofiled tuple or receiver is unsupported,
and an invalid code key or layout gives a metadata dispatch fault.
The step carries forward the namespace, heap and earlier receipts
without a call receipt of its own.


`Observation.calls` records evaluated argument calls in order, then the
settled outer receipt. A missing outer name emits no nested-call receipts.
Each receipt carries the result and any caught error, including typed
integer-pair and Boolean-pair payloads on closed assertions and the empty payload on an
ordinary assertion. Executor faults and exhausted prefixes emit no
settled call receipt.

`run_preserves_builtins` proves that execution preserves the supplied
builtin table. `failing_instruction` gives the exact residual and trace
on failure. `observeArguments_iff` relates the runner to ordered argument
evaluation rules with a first-failure rule. `observeNestedCall_missing`
and `observeNestedCall_failedArguments` give the exact failure outcomes
before outer dispatch. `invokeCall_published`, `callback_path`, and
`callback_delivers` connect callback admission, the ordinary labelled path,
and the existing expectation delivery rules with the precise residual heap.
`run_directDiscard` gives the exact receipt, continuation and residual
state for a direct call. `run_directDiscard_unsupported` gives the
unadmitted descriptor or parameter boundary.
`SeededCall.runObserved_result` and `Expectation.caught_iff` characterize
closed execution and the catch payload.
[Runner theorems](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Seeded/Thms.lean)


## Remaining call and closure inventory

The fixed corpus after #3147 has 360 compiler rejections among historically
compiled inputs. Of these, 176 contain a function declaration or lambda.
The ranking below uses complete ASTs and CPython 3.13.5 execution. The
ordinary reference and empty-seed reference both omit helper bindings.
The checked factory path now covers the two successive result bindings
in rank 1. Closure arithmetic and final global-call lowering close the
named-definition input. Checked nested lambda lowering uses the same
factory path for the lambda input.

| Rank | Pinned shapes | Whole-input outcome and remaining prerequisites |
| ---: | --- | --- |
| 1 | `mixed-freevars-and-cellvars.py` and `lambda4.py` each assign the result of a three-integer factory, then call that saved result with three integers to obtain a second closure. | The empty reference raises the missing-helper `NameError` after both writes. Builtin and preamble references finish normally. The named-definition row uses closure multiplication and a final call through a live global. The lambda row lowers three nested function blocks and uses a zero-argument escaped call inside the equality helper. |
| 2 | `lambda1.py`, `lambda2.py` and `lambda3.py` construct factories with lambdas. | Both supplied references finish normally. The empty reference reaches the missing helper after binding the resulting closures. The first uses a fixed nested lambda chain. The second uses a checked final call to a lexical lambda and forwards its captured cell. The third binds a literal `None` and reads the current module global from its capture-free leaf. |
| 3 | `nesting-plus-free-ref-to-global.py` assigns a declared global in an outer factory. | The two returned closures see the last write. The supplied references finish normally and the empty reference reaches the missing helper. The compiler needs declared-global writes and child lookup of that global. Executor namespace effects must survive return and failure. |
| 4 | `testfunctions8.py` compares named call results in assertions. `testscope1.py` immediately calls a returned closure inside an assertion. | Both complete normally in every reference. They need checked call results as comparison operands. The first also uses a standalone Boolean assignment in the seeded namespace. The second needs a call-result callee and the assertion-message evaluation rule. |
| 5 | `testfunctions11.py` omits two trailing literal positional defaults after six supplied values. | All references finish normally. It needs a saved-default positional binder, a conjunctive assertion, and a seeded ordinary discard with the completed argument list. Larger default and unpacking rows also require tuple, mapping or exception semantics. |

The two defaulted lambda rows need saved positional defaults and binding
of omitted suffix slots. Their full supplied runs also need tuple results
and tuple equality in the helper, variadic collection, and the
`___assertRaises(TypeError, ...)` path with positional callback
arguments. `lambda_stararg.py` additionally expands literal tuples in
argument order. With the current helper names supplied, CPython first
stops at the missing `TypeError` name. With that class also supplied,
both original inputs complete normally.

The decorator row completes normally in CPython with no helpers. Its
closures require call results as arithmetic operands and subtraction.
The module also needs inside-out decorator application with callable
arguments, publication of the final decorated binding, and a call
result as a comparison operand.

The factory ledger authorizes exact descriptors recorded by a successful
publication or factory binding in the same run. The separate argument
selector uses the escaped ledger only after resolving the live equality
helper in a discard call. Imported descriptors, broad value-return
assignments, arbitrary call-result callees, keyword expansion, and
ordinary calls through the general seeded dispatcher require their own
admission and settlement rules.

## Corpus replay handoff

Use the same raw inputs, hashes, and historical selection as the ordinary
module-call replay. Compile each input once with
`ModuleEntry.Functions.Run.compile`. Record compilation rejection before
choosing the runner. Keep the ordinary result and the explicit seed
profile in separate ledger fields. The seeded entry reports unsupported
instructions and calls separately from Python errors. Only count a
completion/output match within the admitted seeded profile.

For the hash-pinned assertion case, run the checked stream with
`Namespace.empty`, `Seeded.legacySeed .builtin`, and
`Seeded.legacySeed .preamble` independently. The two legacy seeds each
provide the `AssertionError` class. The builtin seed installs the two
helpers in the builtin table and the preamble seed installs them in the
module. The preamble seed is a projection onto the bindings used by this
call. The original CPython runner executes the full preamble separately.
Compare the completion, output, and specified residual user bindings
under each profile.

The upstream raw case at revision
`b7ff99372dd24845cf84e58c96b877f15764b276` has SHA-256
`822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79`.
The legacy SOS report records successful completion with empty output
and 21846 transitions. A compatibility rerun of the upstream runner on
CPython 3.9.25 with typed-ast 1.5.5 recorded successful completion with
empty output and 22146 transitions. The recorded transition totals are
separate from the observable completion and output comparison. The
seeded Lean runner's typed call receipts represent module call outcomes.
[Public case](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py)
· [Archived SOS result](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/reports/sospython.json#L3931)
· [Legacy CPython invocation](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/evaluation/run_cpython.py#L50)

The three nested-call cases from the same audit set match CPython under
each equivalent restricted namespace. All raise `NameError` with no
changes to user bindings.

| Pinned case | First missing name in empty namespace | First missing name in either supplied seed |
| --- | --- | --- |
| `bool-callable.py` | `___assertIs` | `___assertIs` |
| `bool-int.py` | `___assertEqual` | `int` |
| `bool-isinstance.py` | `___assertIs` | `___assertIs` |

The full preamble supplies `___assertIs` and `___assertIsNot` and runs with
stock builtins. The table uses the exception-helper projection
`legacySeed`. The separate opt-in `legacyBoolIntSeed` adds the typed
`int(bool)` builtin and the mixed integer/Boolean `___assertIsNot`
helper. The builtin uses builtin fallback in both placements, and the
helper uses the selected harness namespace.

In both Boolean-integer placements, `bool-int.py` completes normally
in Lean and CPython with no changes to user bindings. Lean records eight
calls in order, including the exact integer conversion results and
`None` from each assertion helper. The other two rows still raise
`NameError` for `___assertIs` in those projected namespaces.

`legacyBoolCallableSeed` independently extends `legacySeed` with
`___assertIs` in the selected harness namespace and stock `callable`
and `len` in builtin fallback. `bool-callable.py` completes normally
in both placements with no changes to user bindings. Its four receipts
carry `True`, `None`, `False`, and `None` in order. In this projection,
`bool-int.py` reaches the missing `int` and `bool-isinstance.py`
reaches the missing `isinstance`. The separate CPython full-preamble
run with stock builtins completes `bool-callable.py` quietly.

`legacyBoolIsinstanceSeed` independently extends `legacySeed` with
`___assertIs` in the selected harness namespace and stock `isinstance`,
`bool` and `int` in builtin fallback. The pinned `bool-isinstance.py`
completes in both placements with an empty user-binding delta. Its six
instance checks return `True` four times, then `False` twice. Each
paired identity assertion returns `None`. In this projection the
`bool-callable.py` control reaches the missing `callable` and
`bool-int.py` reaches the missing `___assertIsNot`. The full pinned
preamble on stock CPython 3.13.5 completes the instance case quietly.
[Pinned Boolean cases](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/bool)

The two pinned scalar equality rows now complete normally in the ordinary
runner and every restricted seeded namespace. `testassign1.py` retains
`x = 5`. `testintegers1.py` leaves user bindings empty and reaches its
final negated assertion. Both have empty call traces. The replay checks
these rows and the other seven admitted inputs against CPython, with the
namespace and outcome recorded for each profile.
[Pinned equality rows](https://github.com/koehlma/rigorous/tree/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/k-python/programs)

The pinned `assert-silent.py` case publishes `failing_function` under
all three restricted profiles. The empty profile then raises
`NameError("___assertRaises")` during callee lookup. In both supplied
profiles, the runner and CPython execute the callback and catch its
empty assertion error. The helper returns `None`, and the function
binding survives in every profile.
[Pinned publication row](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/lambda-py/python-reference/exceptions/assert-silent.py)

The pinned `testscope3.py` row completes in the empty, builtin and
preamble-global profiles, in agreement with CPython 3.13.5. The same
published function remains bound. Lean retains cell 0 with integer value
5 and emits one direct-call receipt with result `None` and an empty
caught field. The internal ordinary calls use the shared executor.
[Pinned direct discard row](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/tests/python/programs/original/k-python/programs/testscope3.py)

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms +Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-seeded-call/Publication.lean
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/module-seeded-call/Callback.lean
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py
python3 -I tests/languages/python/source-module-entry/check_seeded_run.py --upstream /path/to/pinned/rigorous
```

The independently authored fixtures exercise the empty control, both
seed placements, shadowing, caught and unmatched assertions, and
the two missing-exception diagnostics. Nested-call fixtures check
callee and argument error precedence, receipt order, assertion delivery,
and residual bindings. Unsupported fixtures run only in Lean. The
optional upstream check validates the revision and raw-file hashes
before emitting the same inputs under the empty, legacy and opt-in projections.
[Fixtures](../../tests/languages/python/source-module-entry/check_seeded_run.py)
