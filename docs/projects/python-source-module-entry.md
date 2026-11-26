# Python module-entry source profile

The source checker reads the actual module scope analysis and retains a
typed global reference for each read and write. Readers and assignment
targets carry their name and exact access, including an explicit
`global` declaration. An uninitialized name read still carries its key so
the runtime can give the defined lookup outcome.

The plan contains single-name assignments and assertions in source order.
Operands include signed integers, booleans, global reads, addition, floor
division and a single equality comparison. Bare `global` and `pass`
provide the corresponding scope and statement evidence. The plan supplies
operations to the module runtime, which gives the initialized store and
execution outcomes.
[Definitions and translation laws](../../Silmaril/Languages/Python/Compile/ModuleEntry/Thms.lean)

A list or tuple of signed integer literals can be indexed by a signed
integer literal. The checker adjusts a negative index once by the
sequence length and lowers a successful lookup to an integer operand.
All elements must be integer literals. Out-of-bounds indices, slices,
and dynamic receivers or indices are outside the profile.

Module `if` statements admit Boolean and signed integer literal guards.
Both arms must consist of single-name assignments, message-free assertions
and `pass`, with every operand checked by the scalar profile. Scope analysis
visits the entire statement before this check. Declarations, nested scopes,
and other statement forms in either arm prevent elision.

The translation certifies the decoded truth value and both arms, and emits
the selected actions in source order before the remaining module.
Literal Boolean assertions in an arm lower to the equivalent integer truth
tests. Both runners use their existing transitions, preserving writes before
a failing assertion or lookup and skipping later statements on failure.

Scalar conditional expressions accept the same literal guards. The checker
validates both operands in the analyzed module scope and emits only the
selected operand. A selected Boolean literal uses the existing Boolean
result of equality with `True`. The resulting value retains its Boolean
type in ordinary and seeded execution. Other operands keep their existing
value and failure semantics. The unselected operand performs no lookup.

The scalar checker folds single equality and inequality comparisons over
closed list and tuple expressions. Leaves are flat sequences of exact
Boolean or signed integer literals. A concatenation must join sequences
of the same kind and its certificate retains their element order. Both
sides of the comparison require certificates, including when their
kinds or lengths differ. Equality compares sequence kind, length and
corresponding values, including Boolean and integer equality at zero and
one. Tuple membership keeps the flat literal profile. The result is an
exact Boolean with no runtime sequence value or allocation.

A message-free assertion can compare `len(sequence)` for equality or
inequality against a checked scalar operand. The sequence uses the closed
list or tuple certificate above. Its elements and intermediate objects
have no runtime uses outside the call. The plan retains the checked global
read of `len` and the exact length. The ordinary namespace reports a missing
`len` or an unsupported function receiver, or raises a defined error for
a noncallable scalar. Seeded execution resolves the current module-first
binding and uses the certified length only with the exact stock `len`
descriptor. It records the call result before checking the right operand.
This path uses the existing explicit seed that already supplies `len`.

Run the CPython 3.13.5 controls and the fixed original inputs with
`python3.13 -I scripts/check-python-sequence-length.py --upstream /path/to/pinned/rigorous`.

The same integer-result assertion path accepts `ord` with one positional
text literal containing exactly one Unicode code point. The checker
certifies the code point, including surrogate code points, before lowering.
The independent `legacyOrdSeed` supplies the stock descriptor. The live
module-first lookup precedes comparison against the right operand. A scalar
mask raises the defined noncallable error and a different callable falls
outside the profile. The call receipt records the integer result before a
right-operand failure, and both heaps keep their incoming contents.
Text arguments of other lengths fail the source check. Run the unchanged
`testord.py` and CPython 3.13.5 controls with
`python3.13 -I scripts/check-python-ordinal.py --upstream /path/to/pinned/rigorous`.

The positional argument checker can emit exact literals for closed signed
integer bit operations and single numeric comparisons. The integer profile
accepts unary sign and complement, bitwise AND, OR and XOR, and nonnegative
shifts. Left shift counts up to 4096 bound compile-time growth. Integer
power accepts a nonnegative integer exponent when the exponent times the
base's magnitude bit length, with a minimum bit length of one, is at most
4096. It emits the exact integer, including `0**0 == 1`. Closed guards
reuse this power check. Comparisons
accept exact Boolean literals and closed integer operands and retain the
Boolean result tag. Each operand is checked in full before a result is emitted.

Both runners receive the same literal argument and use their existing
call preparation and delivery. Lookup stays live and module-first. A missing
callee stops before reading arguments, while a noncallable binding is tested
after preparing the arguments. Seeded receipts come from the reached call
path and retain the existing error and result tags. Run the unchanged
`bool-compare.py` and `bitwise_test.py` with the CPython 3.13.5 controls using
`python3.13 -I scripts/check-python-numeric-arguments.py --upstream /path/to/pinned/rigorous`.

The integer-power replay exercises the first five statements of the pinned
`test_pow.py`. The original still stops at `2**-2` on line 6, whose result
is the float `0.25` in CPython 3.13.5. Floating-point power and reached true
division stay outside this integer check. Run
`python3.13 -I scripts/check-python-integer-power.py --upstream /path/to/pinned/rigorous`.

The Python Core operation `Binary64.trueDivide` takes two integers and returns
an exact finite binary64 value or a typed `ZeroDivisionError` or `OverflowError`.
It rounds the exact quotient magnitude once to nearest, ties to even. A
separate sign preserves negative zero, including after underflow. Overflow
starts at the midpoint between maximum finite and the virtual value
`2^1024`. The rule matches the arithmetic contract of CPython 3.13.5
[`long_true_divide`](https://github.com/python/cpython/blob/v3.13.5/Objects/longobject.c#L4493-L4588).

The module call path checks closed integer operands in a positional
division argument and evaluates the quotient after resolving the live callee.
Each runner carries a finite binary64 value, preserving the exact bits in
returned bindings and seeded receipts. The seeded path enters a same-run
published function with a single finite float through the ordinary binder.
Reached arithmetic errors leave the earlier bindings, heaps and receipts
intact. An argument that raises before call entry produces no outer receipt.
Integer-only closure equality and arithmetic report a profile fault if
reached with a finite float.

The AST emitter reads decimal float tokens from the original source, keeping
the integer coefficient and power of ten. The checker evaluates their exact
rational magnitude and rounds once to nearest, ties to even. The coefficient
binary logarithm and the absolute decimal exponent are bounded by 4096
before exponentiation. A single unary sign is allowed on a positional
literal. Literal conversion preserves signed zero and admits only finite results.

The live seeded equality helper compares finite float/float and int/float
pairs by their exact numeric values. Distinct zero encodings compare equal.
Mixed comparison embeds the integer exactly in the rationals. A failed
comparison retains the two original tags and encodings in its assertion
payload and receipt. Other descriptors keep their own call rules.

Mixed addition in a positional operand accepts one checked closed integer
and one signed finite decimal literal in either order. After live callee
lookup, the runner first rounds the integer to binary64, ties to even.
Integer conversion overflow raises `OverflowError`. The exact dyadic sum
of the converted operands is then rounded once.

Float–float addition in a positional operand accepts two signed decimal
literals whose checked conversions produce finite binary64 operands. The
compiler preserves their source order. Both runners defer the exact dyadic
sum until argument preparation and round it once to nearest, ties to even.
Exact cancellation and opposite zero signs produce positive zero. The sum
of two negative zeros is negative zero, and a sum on the subnormal grid
retains its magnitude bits and sign. At the overflow midpoint or beyond,
CPython produces an infinity. Both runners explicitly stop outside the
finite profile at that operand. A decimal literal conversion that produces
infinity fails checking. Both addition paths use the existing ordered call
preparation and seeded receipt delivery.

Subtraction checks two closed integer expressions with exact unbounded
integer arithmetic. A positional subtraction with a finite decimal
literal on at least one side keeps the source operand order and defers
evaluation until argument preparation. The runner first rounds the
integer operand, if present, to binary64. It then negates the right
operand's exact dyadic value, flips its sign bit for the zero rule, and
rounds the sum once. In particular, `-0.0 - 0` yields negative zero and
`-0.0 - -0.0` yields positive zero. Integer conversion failure raises
`OverflowError`. A finite-operand difference that rounds to infinity
stops at the operand outside the runtime profile. Nonfinite literals
and nonnumeric pairs remain outside the checked source profile.

Multiplication checks closed integer products exactly. The floating path
shares the ordered operand check and integer coercion with subtraction.
It multiplies the resulting exact dyadic values and rounds the product
once to nearest, ties to even. The exclusive-or of the input signs
supplies the result sign, including exact zero and underflow to zero.
Subnormal results use the same rounding rule. Integer conversion
overflow raises `OverflowError`, including when the other operand is
zero. A finite-operand product that rounds to infinity stops outside
the runtime profile. The source profile covers numeric operands.

True division with at least one checked finite decimal literal uses the
same ordered operand witness. The runner converts the integer operand,
if present, before checking the divisor. Thus a value beyond the integer
conversion limit raises `OverflowError` even with a zero float divisor.
After conversion, either zero sign as divisor raises `ZeroDivisionError`.
For a nonzero divisor the runner rounds the exact dyadic ratio once,
ties to even, using the exclusive-or of the operand signs. That sign
also applies to exact zero and underflow to zero. A ratio that rounds to
infinity stops outside the finite runtime profile. Integer–integer true
division uses its exact integer ratio and raises its defined overflow
error when rounding reaches infinity.

Positional floor division and modulo accept two closed integer expressions
from the same integer checker. After live callee lookup, both runners
evaluate the deferred operation as they prepare arguments left to right.
A zero divisor raises `ZeroDivisionError` before call entry. For a nonzero
divisor, the quotient and remainder satisfy `numerator = divisor * quotient + remainder`.
For a positive divisor the remainder lies in `[0, divisor)`. For a negative
divisor it lies in `(divisor, 0]`. These intervals uniquely determine the
floor quotient and the remainder for either numerator sign.

Positional floor division and modulo with one or two finite decimal literals
follow [CPython 3.13.5's float arithmetic](https://github.com/python/cpython/blob/v3.13.5/Objects/floatobject.c).
The runner converts a mixed integer to binary64 before checking for a zero
divisor. Conversion overflow and a zero divisor raise their defined errors.
The finite kernel obtains the truncating remainder and checks that its
binary64 encoding decodes to the exact value. It rounds the remainder's
sign correction once or gives a zero remainder the divisor's sign.
For floor division it rounds the subtraction of the raw remainder, the
division by the divisor, and the correction by one when selected.
The quotient snap uses a binary64 subtraction and a strict half comparison.
A zero input to the snap takes the sign of the original quotient.
The snap checks exact representability of its integral floor. A nonfinite
quotient step stops outside the finite runtime profile. Modulo evaluates
its remainder independently, including when floor division would overflow.

Line 28 of `test_int_float_primitives.py`, `___assertEqual(5 / 2, 2.5)`,
completes in isolation in both helper placements. Ordinary and empty-seeded
execution report the missing helper. The closed integer checker also lowers
the exact sum in line 1, `___assertEqual(4 + 2, 6)`, to an integer call
operand. Lines 1, 3 and 5 complete in isolation in both helper placements.
All 53 unchanged lines complete with `legacyNumericIsinstanceSeed`
in both helper placements. It installs the stock `float` class in the
builtin table and the Boolean assertion helper in the selected placement.
All 24 probes record exact Boolean `True` before the outer helper's
`None` receipt. The mixed and float–float sums, differences, and products
supply finite binary64 `6.0`, `2.0`, and `8.0` respectively. The four
true-division pairs supply binary64 `2.5`. Floor division and modulo
supply integer `2` and `1` for the integer pairs and binary64 `2.0` and
`1.0` for the float-containing pairs. Each placement records 72 receipts.
Instance dispatch uses the live module-first
descriptors. A saved class alias still works after rebinding `float`, and an `int` or `bool`
mask yields exact `False` before the assertion fails. The checked pairs use
exact Boolean, integer and finite float values against stock `bool`,
`int` and `float` classes. Class tuples, arbitrary subclasses, nonclass
arguments and calling `float` as a constructor are outside this profile.

Ordinary and empty-seeded runs stop at the missing equality helper on
line 1. The fixed stock profiles reach the missing Boolean assertion
helper on line 2. Supplying that helper and only the integer and Boolean
classes leaves the `float` lookup on line 4 undefined. The compiler
admits the entire file.
Run the binary64 arithmetic differential with
`python3.13 -I scripts/check-python-mixed-finite-addition.py --upstream /path/to/pinned/rigorous`.
Run the equality and positional arithmetic differential with
`python3.13 -I scripts/check-python-finite-numeric-equality.py --upstream /path/to/pinned/rigorous`.
Run the transport differential with
`python3.13 -I scripts/check-python-division-call-transport.py --upstream /path/to/pinned/rigorous`.
Negative exponent power uses CPython's separate floating power path, which
includes platform libm behavior. Run the quotient differential with
`python3.13 -I scripts/check-python-integer-true-division.py --upstream /path/to/pinned/rigorous`.

A bound `get` on a nonescaping dictionary display can use the checked
scalar operand path. The entire display, key and positional default must
be literals in the integer, Boolean or None profile. The checker validates
all entries and the explicit default even when a key matches. Lookup uses
the last equal key, including Python's shared Boolean and integer key
equality. A miss returns the exact default or None when omitted. The
existing scalar runners deliver the selected value to assignments and
assertions. The three unchanged assertions in `testdicts2.py` complete in
ordinary and seeded execution with no call receipts. Dictionary bindings,
unpacking, and dynamic keys and defaults are outside this profile.
Run the pinned differential with
`python3.13 -I scripts/check-python-literal-dictionary-get.py --upstream /path/to/pinned/rigorous`.

The function-aware runners also bind exact dictionary displays. Entries
use literal integers, Booleans, None or text. Construction follows display
order and replaces an equal key's value while retaining the first key's
tag and position. Every display, including an empty one, allocates a fresh
handle. Aliasing copies the handle and rebinding preserves the old object
for aliases. The shared heap validates each handle and supplies the live
entries for lookup and truth.

A direct named `get` can assign its result or supply a positional argument.
The runner resolves the current receiver before preparing the key and
default from literals or live global reads. It reads the explicit default
even on a hit, then returns the stored value or the exact fallback.
A receiver outside the exact dictionary profile stops before argument
preparation. The seeded runner records the reached method operation and
uses its existing helper dispatch, including the exact `None is None`
case. The ordinary runner and empty seed stop at the missing helper on
line 2 of `dict-get.py`. Both supplied helper placements complete its
unchanged first eight lines with twelve receipts. Line 9 passes a bound
method as a callback and remains a compiler cutoff.
Run the pinned differential with
`python3.13 -I scripts/check-python-persistent-dictionary.py --upstream /path/to/pinned/rigorous`.

A direct named `clear` with zero positional arguments keeps the same
handle, replaces the live entries with an empty list, and returns None.
The ordinary runner reports completion and the seeded runner records the
method receipt. The direct call may discard or bind the result. Flat
positional arguments are looked up in order before a stock arity error.
A missing or unsupported receiver stops before argument preparation.
Failure leaves the reached heap and namespace intact. The unchanged
`dict-clear.py` prefix through line 2 completes in all four fixed runner
profiles. Its next cutoff is the dictionary equality assertion on line 3.
Escaping bound methods, keyword or expanded arguments, and `update` are
outside the checked slice.
Run the pinned differential with
`python3.13 -I scripts/check-python-dictionary-clear.py --upstream /path/to/pinned/rigorous`.

The function-aware checker can omit an `if` whose closed guard selects an
empty arm or an arm of `pass` statements. The otherwise unsupported arm
must contain only passes or syntactically checked raises. Its exception
names and calls are unreachable. A selected raise or a guard whose
evaluation falls outside the checked profile reports `statementProfile`.
The existing literal-arm lowering handles assignments and assertions.

Closed guards compose integer operations, exact singleton identity,
Boolean selection, and ordered comparisons. Finite float addition and
comparison use the library's binary64 semantics. Text comparison follows
Unicode code-point order, and truth of a literal dictionary requires a
checked text key and literal value at every entry. Boolean selection
retains the selected value's tag. The checker validates every operand and
comparison link, including skipped ones. Bitwise inversion requires an
integer because CPython 3.13.5 warns on Boolean inversion. Emission adds no
instructions, runtime allocations or receipts. Run the four pinned inputs and the
CPython 3.13.5 controls with
`python3.13 -I scripts/check-python-closed-guards.py --upstream /path/to/pinned/rigorous`.

A module `try` can be lowered to its normally reached statements when the
protected and else suites contain only `pass` and exact scalar literal
writes. The checked shape has one bare handler with the same grammar, or
a finally-only clause. The handler contributes no writes. The protected
writes precede the else writes, and the cleanup sees both. The cleanup
uses the existing scalar assignment and assertion rules. A reached
cleanup failure preserves earlier writes, stops the remaining cleanup
and module statements, and leaves both heaps and prior receipts intact.
Boolean literal assignment uses the existing tagged scalar result in
both runners.

The five unchanged no-exception `try` fixtures exercise the handler,
else, and finally combinations. Their fixed profiles stop at the
missing assertion helper after producing the exact Boolean flags.
`try-finally-no-exception.py` also completes in both opt-in placements
of the stock truth helper. Run the CPython 3.13.5 controls and exact
pins with `python3.13 -I scripts/check-python-normal-try.py --upstream /path/to/pinned/rigorous`.

Checked exceptional cleanup admits suites of passes, literal or name-read
assignments, and assertions over the same atoms and single scalar equality
or inequality comparisons. A checked `try` can have a `finally` suite,
ordered named handlers followed by an optional bare handler, or both.
Both module runners commit
successful actions in order. A reached Python error skips `else` and selects
the bare handler when present. Cleanup starts from the reached namespace.
Normal cleanup restores the pending completion and a cleanup error replaces it.
Profile failures stop outside Python exception transfer.

Both runners settle the reached bindings before returning the final completion.
The suites preserve both heaps, seeded builtins and earlier call receipts.

An exceptional suite can raise a named stock exception class, call that
class with zero positional arguments and immediately raise the result, or
raise an already supplied exact exception instance. Class normalization and
the explicit zero-argument constructor deliver the same class and empty
argument tuple. A supplied instance carries its exact payload through name
reads and aliases. The checked instance payload covers empty arguments for
the supported stock classes and one exact text argument for `Exception`.
Exception identity and traceback observations are outside this profile.

The runner saves the live callee before evaluating any argument. A module
binding masks the builtin fallback, and a saved alias survives rebinding.
A missing name or invalid named raise operand produces its defined error.
A standalone module-level `raise name` uses the same live lookup and
normalization and delivers its exact error with the reached namespace.
In unchanged `support_exception.py`, each fixed profile retains `s = 1`
and reports missing `TypeError`. Supplying the stock class separately
delivers a `TypeError` with empty arguments. The raise emits no call
receipt.
An explicit call to a known noncallable value produces the call's own
defined error. Immediate constructors emit no separate module receipt.
General callable constructors, standalone instance construction, nontext
stock arguments and explicit causes remain outside this checked path.

The unchanged `testassert1.py` uses the existing scalar truth rule for
its opening direct Boolean assertion. The protected assertion failure
precedes the named raise. The ordinary and empty seeded profiles reach
`NameError:AssertionError` during handler lookup, and both fixed supplied
profiles finish with `x = 5`. Run the differential with
`python3.13 -I scripts/check-python-named-exception-raise.py --upstream /path/to/pinned/rigorous`.

A named handler resolves its class from the reached namespace only after a
defined error. Lookup stops at the first matching arm or first failed class
lookup. The checked ancestry relation uses the represented stock classes.
Missing names and invalid class bindings replace the pending error. If
every class misses, the original error and payload remain pending. Cleanup
runs with that reached state and can replace the pending error. Tuple
filters, general handler expressions and exception chaining are outside
this observation profile.

A selected named handler can bind an explicit stock exception instance or
an empty `AssertionError` to its module target. Reads and aliases carry
the exact class and arguments. On either exit from the handler, the runner
removes the module target before cleanup, even if the handler assigned it
again. Earlier bindings of that name are discarded, aliases retain their
payloads, and the seeded lookup resumes builtin fallback. A selected
target for a runtime error with no represented instance is outside the
execution profile. The checked rules make no instance identity observation.
In unchanged `testtry1.py`, the protected suite completes, both handlers
are skipped, and else and cleanup leave `x = 5`, `y = 6`, `z = 7`. Run
`python3.13 -I scripts/check-python-handler-targets.py --upstream /path/to/pinned/rigorous`.

The protected suite of a standalone module-level try can use bare
`raise` when no exception is active. It produces Python's no-active-exception
`RuntimeError`. Bare re-raise from a handler or cleanup remains separate.
The unchanged `testtry2.py` reaches `NameError:x` in cleanup under the fixed
profiles after lookup of `RuntimeError` fails. It finishes normally when the
stock class is supplied separately. Run the differential with
`python3.13 -I scripts/check-python-typed-handlers.py --upstream /path/to/pinned/rigorous`.


Both unchanged raise pins reach their bare handler and cleanup. Under the
fixed profiles they stop at the first missing `___assertTrue`. A separate
seed supplying stock `Exception` and the Boolean assertion helpers exercises
normal completion. The opt-in `___assertFalse` rule accepts an exact Boolean
and retains it in a failed assertion's payload.
Run the CPython 3.13.5 checks with
`python3.13 -I scripts/check-python-stock-exception-raise.py --upstream /path/to/pinned/rigorous`
and
`python3.13 -I scripts/check-python-exceptional-cleanup.py --upstream /path/to/pinned/rigorous`.

Checked call operands can carry exact text code points, including
surrogates. The ordinary executor transports that tag through argument
preparation. The seeded runner uses its existing live module-first lookup
and call order. The `legacyTextSeed` profile supplies stock `str` and
`bool` alongside the equality and Boolean identity helpers.

Stock conversion covers zero arguments or one scalar or text argument.
Text and Boolean results retain their exact tags. An integer rendered by
`str` must fit within 640 decimal digits, the minimum enabled CPython
3.13.5 digit limit. Text helper equality compares code points and a failure
carries both exact text operands.

A module assignment can bind a checked text literal. A name assignment
reads the live binding and keeps its exact text value across subsequent
rebinding of the source name. An unsuccessful alias read keeps the
destination's prior binding. These assignments leave the closure and
list heaps intact and produce zero receipts. The text carrier represents
contents. Identity on text aliases and on separately evaluated literals
requires provenance outside this profile.

The complete unchanged `immutable-alias.py` finishes with the legacy
equality helper in either stock placement. Each run keeps all six user
bindings and ten successful helper receipts. The ordinary and empty seeded
profiles reach the first missing equality helper with `x = 2` and
`y = 1` still bound.

Run the unchanged conversion pins and CPython 3.13.5 lookup and diagnostic
controls with
`python3.13 -I scripts/check-python-text-conversions.py --upstream /path/to/pinned/rigorous`.

A checked module guard of the form `if not (left == right): raise E("message")`
can compare exact text operands when at least one is a slice. Receivers and
plain operands are live module names or validated text literals. Bounds and
step are omitted, `None`, or integer literals with optional unary minus.
Negative explicit bounds are relative to the code-point length and clip to the direction's
valid endpoints. A negative step has default stop `-1`, which differs from
an explicit `-1`. Selection keeps the indices at exact stride offsets from
the normalized start, in increasing or decreasing order.

The guard evaluates operands from left to right. A reached zero step on
text raises `ValueError("slice step cannot be zero")` before later operands.
Equality skips the entire raise arm. Inequality checks the exception name
and reports a missing name. A reached exception constructor remains outside
the profile. The checked operation changes neither heap and creates zero
receipts. It uses code-point indices and exact content equality.

Both runners complete the unchanged `test_string_slices.py` through its
last comparison with only `a` bound. The pinned replay and CPython 3.13.5
controls also check clipping, reverse defaults and explicit stops, non-ASCII
code points, and the residual state after a failed read or zero step.

A positional call operand can use the same slice core with a validated
literal text receiver and the same literal bounds and step. Both runners
evaluate the operand after the live callee lookup, within the usual
left-to-right argument scan. Successful evaluation delivers the exact
text tag and code points. A reached zero step keeps previous argument
receipts and stops before later operands or invocation. The operand itself
leaves both heaps intact and emits zero receipts.

The unchanged `slice1.py` completes all seven equality-helper calls in
both stock helper placements. Each emits one successful `None` receipt.
Ordinary and empty seeded execution reach the first missing helper with
no user bindings or receipts. Live slice receivers in call operands,
slice assignment and composition remain outside this profile. Live text
receivers in a slice equality guard use the existing guard rule.

A message-free assertion can use `bool()` or `bool(scalar)` on the left
of a single `is` or `is not` link. The checker certifies the optional
positional operand in the shared scalar profile and the right operand in
the singleton profile. Seeded execution reads the live module-first
`bool` binding before preparing the argument. The existing
`legacyBoolIsinstanceSeed` supplies the exact stock type in both
placements. A noncallable mask fails after argument preparation. The
ordinary runner uses its explicit namespace and the same error order.

The stock descriptor uses scalar truth and returns an exact Boolean.
The receipt records that value before the right operand is evaluated.
The identity test uses the existing singleton rule. A failure retains
the caller bindings and both heaps, and skips the tail. Run the exact
CPython 3.13.5 pin and controls with
`python3.13 -I scripts/check-python-bool-identity.py --upstream /path/to/pinned/rigorous`.

A message-free module assertion can compare a stock `list` construction
with an exact flat list literal on either side of equality. The call
accepts zero arguments or one positional flat list or tuple literal.
The checker preserves the scalar tags and order of all elements, and
requires a module global reference for the constructor. The independent
`legacyListSeed` supplies the stock descriptor in both harness placements.

The seeded runner evaluates the operands in source order. It looks up
`list` before allocating a list argument and tests callability after
preparing that argument. A stock call appends a fresh object to the list
allocation table even when the result is empty or matches a prior list.
The receipt records its address and contents. The comparison uses the
closed sequence equality above. The table records reached allocations,
including temporary lists, and keeps the closure-cell heap separate.
An error retains the reached table and skips the tail. The ordinary
runner has no stock list descriptor and keeps its existing namespace
and cell heap on a missing name or noncallable mask.

Run the unchanged pin and CPython 3.13.5 identity and error-order controls
with `python3.13 -I scripts/check-python-list-construction.py --upstream /path/to/pinned/rigorous`.

A checked tuple equality assertion can contain bound `__add__` on an
exact flat tuple literal or unbound `tuple.__add__` with two such positional
literals. The other operands are exact flat tuple literals or the addition
of two such literals. Every link must be equality and the checker validates the
whole chain. The runner evaluates reached operands from left to right
and carries the middle object into the next link. A false link or error
ends evaluation before the next operand.

The unbound path resolves the live module-first `tuple` binding and its
exact stock descriptor before preparing arguments. The separate
`legacyTupleSeed` supplies this type. The runners raise the defined missing
name and stop outside the profile for other bindings. The tuple evaluator
records the absent method on a `None` mask before preparing arguments.
The typed dispatch model returns the nonempty input when adding an
empty tuple, uses the empty singleton for two empty operands, and records
a fresh result for two nonempty inputs. Direct `__eq__` on an exact tuple
with a list returns `NotImplemented`, while operator equality returns
false. The source checker admits the exact `__add__` calls as tuple
operands. The evaluator's literal representatives and reached operands
are local to the assertion, and its equality compares scalar contents. The
existing caller namespaces, closure heap, list heap and generic call
receipts keep their separate observation rules.

The same assertion accepts `tuple()` and `tuple((...))` with one exact
flat scalar literal. The constructor resolves the live `tuple` binding
before preparing its argument. A missing binding raises `NameError`. A
modeled noncallable mask raises `TypeError` after argument preparation.
The stock descriptor delivers the canonical empty tuple or the exact
prepared object and reached tuple heap. The result keeps the argument's
address and incurs no second allocation. These addresses belong to the
assertion. The module binding path tracks addresses for nonempty displays
with live item reads in the shared closure heap.

A reached module name can also supply a comparison operand or the sole
positional operand of stock `tuple`. The constructor reads its callee before
its argument. A missing operand takes precedence over dispatch of a present
mask. A stock call on a known noniterable scalar raises TypeError. For exact
flat tuples the chain carries the live scalar contents directly, with no
projected object address or allocation. These assertions retain the ordinary
and seeded tuple-chain receipt convention. `testtuples11.py` completes when
stock `tuple` is supplied and reaches the defined missing-name error when it
is absent.

Run the unchanged pin and CPython 3.13.5 dispatch and sequencing controls
with `python3.13 -I scripts/check-python-tuple-chain.py --upstream /path/to/pinned/rigorous`.

A named module call can take a single positional tuple identity test, with
one `is` or `is not` link. Its operands are live global reads or the
canonical empty tuple. The runner resolves the callee, reads both operands
from left to right, and delivers an exact Boolean before invoking the saved
callee. Allocated descriptors must resolve in the reached closure heap.
Stock `tuple(existing)` and module aliases retain the original descriptor,
so two tracked tuples with the same contents can still have distinct
identities. Two reads of the same live tuple binding also establish identity.
A module with a checked tuple identity operand retains an origin witness
when binding a closed nonempty display. The witness occupies a slot in the
same closure heap and follows the descriptor through assignment and stock
`tuple(existing)`. Equal witnesses prove positive identity. Different
closed origins leave both identity operators undefined in this profile,
since CPython can share a constant across literal sites.

The opt-in `legacyTupleIdentitySeed` supplies the stock `___assertTrue`
helper. For a Boolean argument, the helper's receipt records `None` on success
and `AssertionError(False)` on a false result. A failed callee or operand read
preserves the reached heaps and prior receipts. The exact four-statement
prefix of `tuple-constructors.py` completes with the stock constructor and
helper, including the positive identity on line 5. The tuple-chain regression
checks the retained descriptor, exact helper receipts, rebound aliases,
independent equal-content closed origins, and the canonical empty case.


A checked stock `tuple` call can consume a new closed flat list
display, either as a direct module call or as the first positional
argument of a named module call. Each element is an exact integer or
Boolean literal, or the singleton `None`. The constructor resolves the callee before it allocates
the display. A present noncallable mask retains that allocation and
reports `TypeError` before any later argument is evaluated. A missing
callee leaves the list heap as it was.

Stock conversion reads the freshly allocated list at its address in the
reached list heap. Empty contents return the canonical empty tuple.
Nonempty contents create a fresh tuple in the closure heap with the
same ordered scalar tags. The result is a tuple reference, and separate
nonempty conversions have distinct addresses. This rule reads the fresh
display immediately. The source profile leaves named lists and mutation
out of this conversion. Seeded execution retains the constructor receipt
and both reached heaps if a later operand fails. Ordinary execution
retains any reached list on a mask in its explicit namespace.

A resolved stock `tuple` descriptor also accepts one checked text value.
Empty text returns the canonical empty tuple without allocating. Nonempty
text creates a fresh tuple in the closure heap with one singleton text
value for each stored Python code point, in order. The checked carrier
covers U+0000 through U+10FFFF, including lone surrogates represented by
escapes in Python source. The source adapter passes code points from the
decoded Python AST. This conversion does not decode bytes, normalize
text, or segment grapheme clusters.

Checked flat tuple displays and the equality helper accept these text
elements alongside the existing scalar tags. Text elements compare by
code-point sequence, and text and scalar elements compare unequal.
The literal's source site provides no separate identity evidence. When
a later argument fails, seeded execution preserves the conversion's
reached heap and receipt, with no outer helper receipt.

The unchanged `tuple-constructors.py` completes in both opt-in
`legacyTupleIdentitySeed` placements. It reaches the missing equality
helper in ordinary and empty seeded execution, and the missing stock
`tuple` in the two legacy helper placements that omit it. The
CPython 3.13.5 differential also exercises separate fresh conversions,
constructor aliases, masks, combining marks, a non-BMP point, and
a lone surrogate.

A checked Boolean equality on two literal Booleans can be lowered to
a Boolean positional operand. This includes the canonical Boolean result
of a checked `not` expression, such as `not ()`. A tuple display in a
positional operand delivers an exact tuple. The live seeded
`___assertTrue` descriptor tests the contents' nonemptiness for either
a tuple payload or a tracked tuple reference. A false Boolean retains
`False` as its assertion payload, and a false tuple retains `()`.

The unchanged `tuple-truth.py` sends `True` and then `(42,)` to the
existing stock helper in both `legacyTupleIdentitySeed` placements.
Both calls settle successful `None` receipts. Profiles without the
helper reach its first missing-name lookup. The two statements leave
both modeled heaps intact and add no user bindings.

A direct named call can take one flat list display or its negation as
its sole positional argument. Entries are checked integer, Boolean, and
`None` literals and live names that read those exact scalar values. Callee
lookup comes first. Entries evaluate left to right before the existing list
table allocates the display. A failed entry leaves that table intact. A
noncallable binding reports its error after the argument is prepared.
Negation allocates the display and supplies its Boolean emptiness result.

The stock `___assertTrue` descriptor accepts the existing list carrier. It
tests nonemptiness, and a failed assertion carries the same empty list
descriptor as its argument. A saved helper alias remains callable after
rebinding its original name. An alias of a supplied list retains its
descriptor and incurs no allocation on read. This profile covers direct
operand construction and seeded list values with their reached list tables.
Ordinary linked functions can receive the Boolean negation. Raw list values
remain outside ordinary closure binding.

The two calls in unchanged `test_list_truth.py` complete with the stock
helper in both opt-in placements. Their allocations are ordered as `[]`
and `[42]`. They deliver `True` and `[42]` and settle two `None` receipts.
Without the helper, the first name lookup fails before allocating a list.

A scalar comparison chain has at least two links. Every link uses one of
`==`, `!=`, `<`, `<=`, `>` or `>=` and every operand is an exact
Boolean or integer literal, including unary minus on an integer literal.
The checker validates the whole chain before folding. Each reached right
value becomes the next comparison's left value. The first false comparison
ends the scan. The result uses the same Boolean operand as a folded tuple
comparison, with no runtime lookup, call, or allocation.

Singleton identity has a separate checked chain for `is` and `is not`.
Each operand must produce `None` or an exact Boolean if evaluation succeeds.
This includes Boolean results of admitted scalar comparisons and nested
identity tests. The checker validates every link and operand, including a
suffix that execution will skip. The runners evaluate reached operands
left to right, carry the middle singleton into the next link, and stop at
the first false comparison or operand error. A successful test produces
a Boolean. Integer and text identities are outside this profile.

Reached operands of a checked `and` or `or` are Boolean or signed integer
literals. The source certificate records the first false value for
`and`, the first true value for `or`, or the last value at the end of
the sequence. A deciding operand permits the checker to use a separate
syntax check on the whole dead suffix. That grammar accepts integer,
Boolean and `None` literals, recursive unary and binary expressions, and
nested Boolean expressions with at least two operands. Names, calls,
and constructs introducing scopes are outside the dead-suffix grammar.
The module still runs full source scope analysis. A reached true division
remains an expression-profile rejection. Skipped true division has no
runtime instruction. The emitted result retains its integer or Boolean tag.

A closed `not` or assertion can also test `None` or a flat literal list or
tuple whose elements pass the scalar check. These tests use only falsity
or emptiness and emit no container value.

`None` can also be bound, read and copied as a module value. It has its
own tag and is false in a truth test. Scalar `==` and `!=` evaluate
their operands from left to right. Two `None` values compare equal, and
`None` compares unequal to an integer or Boolean. The integer
projection used by arithmetic and closed numeric chains applies to
integers and Booleans. Reached scalar arithmetic on `None` stops at the
arithmetic profile boundary. Object identity requires separate evidence
about the objects compared.

The regression emits Lean from Python source and verifies the global
access witnesses, action order and the diagnostic for an assertion
message.

The source runner accepts an initial namespace and builds the Core module
entry using the analyzed spelling of each name. Its correspondence law
matches the exact completion, visible trace and residual namespace.
The execution regression compares CPython and Lean on initialized reads,
overwrites, assertion failure, an unbound read and arithmetic failure.
[Runner contract](../../Silmaril/Languages/Python/Compile/ModuleEntry/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Thms
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms
```

## Function bindings and calls

The function plan keeps the source order of top-level assignments,
definitions and calls. A definition carries its analyzed child path,
fixed positional destinations and lowered body. Each call reads the
function by its module name and supplies ordered positional operands. The
result can be assigned to a name, discarded or tested by a message-free
assertion.

An implicit or declared global read in a function body retains its module
name. This supplies lookup in the namespace at call time, including writes
between a definition and call. Local references continue to use bounded
frame slots. The regression verifies both kinds of lookup.
[Function plan](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Thms
```

The module function runner links the selected bodies and publishes them in
the shared Core namespace, in source order. A positional call reads its
callable and its literal or name arguments through that namespace.
Positional arguments at a module call site may also be direct named calls
with literal or name operands. The ordinary runner saves the outer
callable in a frame local, evaluates each argument once from left to right
into separate locals, then invokes the saved callable. The result updates
the selected binding only on successful completion. The runner gives the
labelled invocation trace and a residual state that can be resumed with
further fuel. Its prefix composition theorem agrees with
a run using the combined fuel.

The adjacent keyword discard profile checks a bare call immediately
after its undecorated function definition. The definition has one required
positional-or-keyword parameter without an annotation. The call has one
`**` mapping literal with one string key and one integer literal value.
The key must equal the parameter's code points. The typed plan records
the adjacent publication and the one-slot argument mapping. The runtime
reads the live function binding and invokes it through the ordinary
positional executor with that integer. The seeded selector requires a
published function with one slot and records the ordinary completion
and reached heap. The call's result is discarded.

An undecorated module function can have one keyword-only parameter with
an integer literal default when its body is a single message-free assertion
comparing that parameter to an integer literal. The checked linked entry
retains the literal and accepts zero positional arguments. After the
ordinary binder accepts omission, a store initializes the parameter's
local slot without touching the heap. A call through an alias uses its
function's own saved literal. Seeded discard uses its existing published
zero-argument selector and settlement rule. Explicit positional values
fail ordinary arity checking. Explicit keyword arguments, dynamic
defaults, and introspection of these defaulted definitions are outside
this profile.

Checked function bodies can add and multiply integer literals and values
read from fast locals, owned or forwarded cells, and live module globals.
The operations can nest. The executor reads the left operand and then the right operand
before checking their types. Booleans contribute 0 or 1 and the result is
an integer. A plain function or `None` operand raises `TypeError` after
both reads succeed. This value profile covers integer arithmetic without
custom operator methods or sequence concatenation. The ordinary and Finite
runners share operand evaluation, and the seeded runner uses it when an
existing selector admits the call.

At module call sites, deeper argument nesting, arithmetic operands,
and keyword or unpacked arguments outside the adjacent discard shape
are rejected. The seeded runner supports these
nested instructions within its [closed call profile](python-seeded-module-runner.md).
The CPython regression checks
result placement, lookup and argument error order, and residual bindings.
The Lean regression also checks the call-entry order across a live prefix.
The ordinary module runner also accepts a message-free `assert not test`
when `test` is an existing module operand. It evaluates the operand once,
propagates evaluation errors, and succeeds exactly when the result is
false by the ordinary truth rule. This includes a name bound to a
returned `None`. The seeded runner also handles this instruction for
its existing [seeded operands](python-seeded-module-runner.md).
[Module-call runner](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
```
