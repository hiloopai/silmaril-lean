# Starlark source frontend

This frontend reads a scalar subset of the [pinned Starlark core
profile](starlark.md). The source specification is Bazel's [Starlark Language
Specification][spec] at `c0af0ea03dc90d3bbc021394b693e6957cc15030`. The SHA-256
of raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
The parse oracle uses [starlark-go][go] at
`4f4267fb140d1e8b91c9bce55cee2f809e8840dd`.

## Lean entry points

- `Frontend.lexUtf8` and `Frontend.lex` produce spanned tokens for logical
  lines. The byte entry point rejects ill-formed UTF-8 and highlights the first
  byte of the bad sequence. Positions use zero-based byte offsets and one-based
  lines and Unicode scalar columns in the original input. A tab occupies one
  source column. [Lexer](../../Silmaril/Languages/Starlark/Frontend/Lexer/Defs.lean)
- `Frontend.parseModuleUtf8` and `Frontend.parseModule` retain top-level
  statement spans. `ParsedModule.toSourceStmt` sequences the existing scalar
  AST in source order, with `pass` for an empty module. `Starlark.runModule`
  resolves and denotes that AST in the closed scalar environment. The module
  example evaluates `out = -1` through arithmetic, a conditional, and an untaken
  error branch. [Lean checks](../../Silmaril/Languages/Starlark/Frontend/Checks.lean)
- `Frontend.parseFunctionUtf8` and `Frontend.parseFunction` accept a file
  containing one `def` with required positional name parameters and a
  multiline suite. They return its name, ordered parameters, function span,
  and located direct body statements. `ParsedFunction.toSourceStmt` lowers
  branches and returns to the existing scalar body AST. Pass that AST and
  already bound globals and parameters to `Starlark.runFunctionBody`.
  [Parser](../../Silmaril/Languages/Starlark/Frontend/Defs.lean)

```starlark
def pick(flag):
  if flag:
    if (1 +
        2) == 3:
      return 8
    else:
      return 0
  else:
    return -1
```

The nested-suite fixture evaluates this body with `flag` bound to `True` and
`False`, yielding `8` and `-1`. It also exercises CRLF, Unicode comments, and
explicit line joining. A smaller multiline function with two open levels at
EOF has a kernel-checked text-to-denotation example. The existing soundness
proofs still begin at the resolved scalar AST, and static and dynamic failures
retain their existing types. Parser soundness and completeness remain open.
[Lean checks](../../Silmaril/Languages/Starlark/Frontend/Checks.lean)

## Module initialization

`Frontend.Module.parseUtf8` and `Frontend.Module.parse` lower complete files
to located `Modules.Resolve.Command`s. The module profile accepts top-level
scalar assignments and expression statements, multiline `def` declarations
with positional and bare-star keyword-only parameters and scalar defaults, postfix call
assignments and expression statements, and leading load statements. Top-level name assignments also accept the collection displays
of the call profile. An application chain starts with a bare identifier or a
parenthesized scalar expression. Module-function returns, name assignments,
expression statements, and `if` and `elif` tests can use the same application
chain. The adapter reuses the logical-line, parameter, and suite parsers.
It emits a normalized declaration for each `def` and a
normalized `.call` expression for each application. A top-level `pass`
produces no command. [Module adapter](../../Silmaril/Languages/Starlark/Frontend/Module/Defs.lean)

```starlark
# 雪
def id(x):
  return x
out = id(7)
```

`Frontend.Module.runUtf8` uses the existing `Modules.Resolve.runModule` with
an empty catalog, initial state, and linked table. The example publishes an
integer `out` with value `7`. Calling `id()` reaches a missing-argument error.
Using `id(missing)` rejects the undefined name during validation. The
result distinguishes a spanned frontend diagnostic, a normalized validation
error, and a runtime result with the existing residual state and publication
rules. Parsed commands retain half-open source spans. Backend errors retain
their native payloads because the normalized evaluator has no token-level
provenance. [Module checks](../../Silmaril/Languages/Starlark/Frontend/Module/Checks.lean)

The module body uses the same admitted scalar statement forms as the standalone
function parser. Its expressions, defaults, and call operands use integer
literals, names, `and`, `or`, and conditional expressions. Unary and binary
operators produce an unsupported diagnostic spanning the containing statement,
default, or argument. Module functions admit calls at the root of a return,
name assignment RHS, or expression statement. Named variadic formals remain
outside this profile.

### Scalar defaults

```starlark
# 雪
seed = 7
def pick(seed=seed):
  return seed
out = pick()
override = pick(seed=9)
```

The default reads the defining module's `seed` when `pick` is installed. The
module publishes `out = 7` and `override = 9`. A separate control puts the
assignment to `seed` after `def` and supplies an explicit named override. It
still fails on the uninitialized default read at definition time.

### Bare-star keyword-only formals

In a module function header, a bare `*` separates ordinary positional
formals from keyword-only formals. The suffix can mix required and
defaulted formals in declaration order, including a required formal
after a defaulted keyword-only formal. The positional prefix can be
empty. Defaults use the existing scalar grammar. The source tree
retains the separator, whole-formal, name, and default spans. Lowering
passes the two ordered groups to the existing normalized signature.

The pinned core and Lean's validator require at least one optional
formal after the bare star. The parser recognizes a required-only suffix
and passes it to validation, which reports `bareStarWithoutOptional`.
Pinned Go also accepts and executes that spelling. Empty and repeated
separators and duplicate names receive spanned frontend diagnostics.
The Go comparison checks its corresponding syntax or validation stage.
Named `*args` and `**kwargs` formals and call-bearing defaults remain
outside this grammar.

The shared three-file fixture loads an exported wrapper that calls its
own captured import. It checks omission and override of a saved
keyword-only default, a saved positional default, omission of a required
keyword, and rejection of positional supply beyond the positional
prefix. Lean inspects the reached closure, saved-default order, and
published dependencies. The pinned Go oracle checks the same exports,
errors and load order, plus formal and separator locations on the CRLF
span fixture. The standalone scalar function parser retains its header
grammar.
[Keyword-only checks](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/KeywordOnlyChecks.lean) · [Pinned spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions)

### Call arguments

Call arguments use the order positional, named, optional `*`, then optional
`**`. Operands use the module expression grammar, including scalar
expressions, applications, and list and tuple displays. This admits
calls such as `f(*identity(xs), **identity(identity(kw)))` and call-free
expressions such as `f(*(xs if flag else ys), **(False or kw))`.
`*` accepts list and tuple displays. At a spread root, `**` also accepts
a dictionary display with simple unescaped quoted keys and scalar values.
Module assignments can bind these displays to names.

```starlark
# 雪
def identity(x):
  return x
def f(a,b):
  return b
xs = [1]
kw = {'b': 7}
out = f(*identity(xs), **identity(kw))
```

The module publishes `out = 7`. Each nested application lowers directly to
one existing normalized call expression. The normalized evaluator reads the
callee first, then evaluates each operand once in source order. It expands the
mapping before the iterable and binds the resulting arguments. An error while
evaluating an operand preempts later operands and expansion. A collision
between a named value and an expanded key reaches binding.

Lowered commands retain every application's full span, callee span, and
grouped operand spans, including spread markers. The records are in preorder,
visiting the callee before operands and operands in source order. The parser
reports a spanned diagnostic where the ordering rules are violated.

The frontend preserves repeated explicit names so normalized validation can
reject them. It also passes required-after-default signatures to normalized
validation. Duplicate keys within a dictionary fail during display evaluation,
while a collision between an explicit named argument and a `**` key reaches
the binder and fails there. The Go controls exercise all three stages and
check the corresponding error messages.
[Module checks](../../Silmaril/Languages/Starlark/Frontend/Module/Checks.lean)

`Frontend.Module.initializes_iff_run` applies the existing module agreement
theorem to the normalized commands. `lowerNamedArguments_names` proves that
successful named-operand lowering preserves explicit names in order, including
repetitions. `lowerCall_operands` identifies the normalized call produced by a
successful lowering, preserves the original span groups, and proves that the
positional count, ordered keyword names, and spread presence agree with the
normalized argument shape. `lowerOperand_call` ties nested operand lowering
to that same call path and records the application location. The kernel
checks the normalized collection
assignments, nested call shape, and callee and operand spans for concrete
UTF-8 inputs. Executable Lean checks cover publication, error precedence, a
named/expanded binding collision, and the single allocation from evaluating
`list(xs)` as a spread operand. A general parser or
source-to-normalized adequacy theorem remains open. [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Postfix applications

A postfix chain can appear directly or within logical and conditional
expressions in a name assignment, return, expression statement, branch
test, or call operand in the module profile. The head can be a bare name or a
parenthesized scalar expression, such as `(f if flag else g)`. The parser
consumes each parenthesized argument group before advancing to the next suffix. Each suffix uses the expression
parsed so far as its callee, so `factory(a)(b)(c)` associates to the left.
The parser's budget depends on token count, with no fixed application cap.

```starlark
# 雪
def identity(x):
  return x
def choose(callable):
  return callable
out = choose(choose)(identity)(7)
```

The first application returns `choose`, the second returns `identity`, and
the final one publishes `out = 7`. Each lowers to an ordinary normalized call
node with its own location entry. The final callee span is the entire
`choose(choose)(identity)` prefix. A parenthesized head includes its opening
and closing delimiters.

`lowerApplication_parts` identifies the lowered callee and relates the
application and grouped operand spans to the normalized call shape.
`denoteCall_calleeFirst` unfolds resolved call evaluation into a single
callee evaluation followed by the operands from its returned state.
`denoteCall_calleeError` proves that a callee error preserves the error state
and bypasses operands. These properties apply at each link in a chain.
A successfully evaluated noncallable value reaches the dispatch check
after operand evaluation and expansion.
[Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

The UTF-8 fixtures exercise four applications, a conditional callee with a
skipped branch, and a failure in the second application. Lean checks that the
first two operand allocations survive that failure and the later operands are
skipped. Pinned Go agrees on export and error outcomes, and a Go-only
mutation control records the effects that survive. A kernel check compares
three left-associated normalized applications and their original UTF-8
spans, then checks the following assignment was parsed separately.

The head's parenthesized expression uses the existing call-free scalar
profile. Attribute lookup, subscripts, and calls within dictionary displays
remain outside this grammar. The normalized checker and evaluator
handle callable values, binding, runtime errors, and the existing restriction
on recursive closure invocation.
[Computed call checks](../../Silmaril/Languages/Starlark/Frontend/Module/ComputedCallChecks.lean)

### Calls in return expressions

Module functions use the same suite parser as the standalone scalar frontend.
Within those suites, a `return` can take a postfix application at its root,
including a return inside an `if`, `elif`, or `else` branch. The adapter
lowers it to `Modules.Resolve.Statement.ret (some expression)`. Existing
body resolution selects the callee binding and collects captures. The
declaration compiler assigns the ID and emits `Body.returnExpr`, which the
existing denotation evaluates in the function frame.

Shared UTF-8 controls exercise a global callable and a callable parameter
that shadows a global function. A failed inner callee masks a later operand
failure, and an undefined callee is rejected during resolution. The kernel
checks the normalized return tree and the application, callee, and operand
spans retained on the declaration. The standalone `parseFunctionUtf8` entry
point keeps the scalar body profile.
[Return call checks](../../Silmaril/Languages/Starlark/Frontend/Module/ReturnCallChecks.lean)

### Call-valued name assignments

A module function can use `name = f(...)` or a postfix chain as the entire
assignment RHS. This includes assignments in indented branches. The
frontend emits the existing normalized `Statement.assign`. The declaration
compiler collects the target in the function layout and emits
`Body.assignExpr`, which writes the local slot after the RHS succeeds.

The shared branch fixture assigns through a callable parameter that shadows
a global function. The next statement reads the assigned local, and module
publication still sees the original global binding of the same name. Taking
the other branch leaves the local uninitialized. Lean checks the resolved
local read, write, and callee slots, and the kernel checks the assignment
and exact UTF-8 application spans.

In the failing fixture, the first call error preserves an earlier local
value and suppresses the later assignments. Lean checks the residual heap.
A Go-only mutation control observes the effect of the first assignment's
operand and confirms that the next RHS is skipped. The assignment targets
in this profile are bare names.
[Assignment call checks](../../Silmaril/Languages/Starlark/Frontend/Module/AssignmentCallChecks.lean) · [Go effect controls](../../scripts/starlark/frontend/spreads.go)

### Call expression statements

Module and module-function suites admit a postfix chain as a whole
expression statement, including on either side of a semicolon. The
frontend lowers it to the existing normalized `.eval` command or body
statement. The checked evaluator keeps the state produced by the call
and discards its result. The call introduces no assignment target.

The kernel checks the normalized discard nodes and exact UTF-8 statement,
application, callee, and operand spans in both positions. Lean verifies
that a function branch containing only call statements adds no locals
and that the published module contains only its source bindings. Two
discarded list copies leave allocations in left-to-right order. A skipped
branch contributes no allocations.

Shared Lean and pinned Go fixtures observe an argument failure before the
following semicolon-separated statement. Lean checks that the first
allocation survives while the later allocation and writes are skipped.
Go-only mutation controls observe ordering and suppression directly.
The standalone scalar parser retains its call-free grammar.
[Call statement checks](../../Silmaril/Languages/Starlark/Frontend/Module/CallStatementChecks.lean) · [Go effect controls](../../scripts/starlark/frontend/spreads.go)

### Calls in short-circuit expressions

The scalar parser and module expression parser share one precedence table.
In the module profile, the postfix hook recognizes a call before considering
infix operators. Calls bind more tightly than `and`, which binds more tightly
than `or`. Both logical operators associate to the left. Parentheses can group
logical operands. This grammar is shared by module and function name
assignments, function returns, expression statements, and call operands.

For example, `f() or g()(2) and h(3) or k(4)` lowers as
`(f() or (g()(2) and h(3))) or k(4)`. The kernel checks this exact
normalized tree and the original UTF-8 expression, application, callee, and
operand spans. `lowerOperand_logical` preserves the normalized logical node
and the source order of the application records. `denoteLogical_order` shows
that the evaluator runs the left operand first, uses its resulting state
for the truth test, and evaluates the right operand only when selected.
An error in the left operand or its truth test retains that error and state.

The UTF-8 fixtures exercise module assignment, function assignment and return,
grouped expressions, and a logical spread operand. Lean checks retained
allocation order, skipped operands, and first-error masking. Go-only
mutation traces confirm order and that later operands are skipped.
Lexical resolution still visits the skipped operand.
[Logical call checks](../../Silmaril/Languages/Starlark/Frontend/Module/LogicalCallChecks.lean) · [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Calls in conditional expressions

In the module expression grammar, `yes if test else no` accepts postfix
applications in all three operands. The same precedence loop runs for
module assignments, function assignments and returns, expression
statements, branch tests, and call operands. Conditional expressions bind
more weakly than `and` and `or`, and an unparenthesized conditional in the `else` arm
nests to the right.

The kernel checks that
`f() or g()(2) if p() and q() else h(3) if r() else k(4)` lowers as
`(f() or g()(2)) if (p() and q()) else (h(3) if r() else k(4))`,
with the original UTF-8 spans. `lowerOperand_conditional` preserves the
normalized conditional and records application spans in source order,
visiting the consequent, condition, and alternative. The checked evaluator
runs the condition first. `denoteConditional_order` gives its exact state
handoff to the selected arm and preserves a condition or truth-test error.

The shared UTF-8 fixtures check module and function forms, condition failure,
and errors in either selected arm. Lean checks that the condition's
allocation precedes the chosen arm's allocation, and that a reached error
retains its prefix while skipping the other arm and later writes. Go-only
mutation controls observe the same ordering and suppression.
[Conditional call checks](../../Silmaril/Languages/Starlark/Frontend/Module/ConditionalCallChecks.lean) · [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Calls in statement branch tests

Inside a module function, `if` and `elif` parse the shared module expression
grammar up to the suite colon. This includes postfix calls, `and`, `or`,
and conditional expressions. An `elif` lowers to a branch in the preceding
false suite, and a missing alternative lowers to `pass`. The frontend
keeps each heading's test span and records applications in heading and
suite source order. Multiline suites may nest. Top-level `if` and inline
suites remain outside the profile.

`compileBody_plainBranch` shows how the normalized statement resolves
its test in the collected block and compiles both suites into one resolved
branch. `denoteBranchExpr_order` gives the exact state handoff from one
evaluation of the test and its truth check to the selected suite. An
earlier true or failing test skips later `elif` tests. The resolver still
visits these tests during validation. The evaluation equation carries a
test or truth-check error with its exact state.

Lean checks the tree and UTF-8 byte, line, and column spans for both
headings and their applications. The pinned Go parser checks the heading
line and column spans on the same CRLF source. Shared fixtures check
parameter shadowing, success in each suite, nested branches, and failure in
a reached test. Lean checks the allocation order and suppressed writes.
Go-only mutation controls record test and suite order and skipped effects.
[Branch checks](../../Silmaril/Languages/Starlark/Frontend/Module/BranchCallChecks.lean) · [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

The checked module operator profile admits `and`, `or`, and conditional
expressions. Computed callees formed from call-containing groups and calls
in parameter defaults and dictionary display elements remain outside this profile.
Unary `not`, `+`, `-`, and `~`, binary arithmetic
`+`, `-`, `*`, `/`, `//`, and `%`, equality, ordering, membership, shifts,
and bitwise operators remain outside the checked module operator profile.
The standalone scalar parser retains its existing call-free operators.

### Calls in list displays

List displays are atoms in the module expression grammar. Each element
uses that same grammar, including postfix calls, short-circuit and
conditional expressions, and nested list displays. Brackets delimit
the display. Commas separate the elements, and a final comma is optional.
Empty lists and multiline continuations are supported. For example,
`[f(), [a() if test() else b(),], g([h(),]),]` works in a module
assignment, function expression, or call operand.

`lowerOperand_list` emits the existing normalized list node and preserves
application metadata in element order. `denoteList_cons` describes the
single evaluation of the first element and the handoff of its state to
the remaining elements. `denoteList_order` allocates the display only
after all elements have evaluated successfully. A reached failure keeps
its exact state, including successful inner allocations and effects of
the failing element. It skips later elements and the outer allocation.

Lean checks the normalized tree and exact UTF-8 byte, line, and column
spans for displays, elements, and applications. Pinned Go checks the
display and immediate element positions on the same CRLF input. Shared
controls cover nested lists and calls, function bodies, spreads, invalid
separators, and a reached binding error. Lean inspects the allocation
prefix. Go-only mutation traces check element order and skipped effects.
The standalone scalar parser stays call-free. Dictionary elements,
comprehensions, and default expressions keep their prior scope.
[List display checks](../../Silmaril/Languages/Starlark/Frontend/Module/ListDisplayChecks.lean) · [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Calls in tuple displays

The module precedence parser shares the opening parse for groups and
tuples. `(f())` groups the call, `(f(),)` makes a singleton tuple, and
`()` makes an empty tuple. After the first comma, the same delimiter
loop as list displays reads the remaining elements with the module
expression grammar. Nested displays, conditional and logical expressions,
and optional trailing commas after multiple elements are supported.
Unparenthesized tuples remain outside this profile. A grouped call can
be a tuple element. Computed callees such as `(f())()` remain outside
the supported callee forms.

`lowerOperand_tuple` preserves element order and collects each element's
application metadata. `denoteTuple_cons` gives one evaluation of the
first element and the exact state handed to the remainder.
`denoteTuple_order` allocates the tuple after all elements succeed and
preserves the exact reached error state. Lean checks a failure after a
completed inner tuple, with no later element effects or outer allocation.
Go-only mutation controls check the reached prefix and skipped effects.

Lean checks grouping, normalized shape, and exact UTF-8 tuple, element,
callee, application, and operand spans. Pinned Go checks the tuple and
element line and column spans on the same CRLF source. The oracle uses
Go's enclosing parenthesis node for nonempty tuples and advances the
empty tuple's closing-token position to its half-open end.
Standalone scalar parsing and the dictionary, comprehension, and
default-expression boundaries retain their prior scope.
[Tuple display checks](../../Silmaril/Languages/Starlark/Frontend/Module/TupleDisplayChecks.lean) · [Theorems](../../Silmaril/Languages/Starlark/Frontend/Module/Thms.lean)

### Leading loads and UTF-8 graphs

The module frontend accepts `load("label", "export")` and renamed imports
such as `load("label", local_name="export")`. A load requires at least one
import, preserves operand order, and permits a trailing comma. Labels and
export spellings use simple unescaped single- or double-quoted strings.
Export and alias names use the frontend's ASCII identifier profile. Parsed
syntax retains half-open spans for each load, its label, and the exported and
local names. The normalized command retains the whole load span. The existing
validator rejects private exports and conflicting bindings.

`Frontend.Module.Loader.prepare` accepts an array of UTF-8 texts and a caller-
supplied label-to-module-ID table for each text. Array positions are module
IDs. The adapter parses and resolves every supplied text in array order,
appending declarations to one table and retaining the spanned commands.
Frontend and validation errors identify the entry. Label lookup, export
lookup, any reached runtime error, and initialization of dependencies are
handled by the finite loader when a prepared module is requested. The adapter
treats label spellings as opaque strings. Filesystem access and path resolution
belong to the caller. The single-module `Frontend.Module.runUtf8` uses an empty
catalog. Use `Frontend.Module.Loader.loadUtf8` to prepare a graph and start a
cold load, or `Prepared.load` to reuse the matching loader session.
[UTF-8 loader](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Defs.lean)

The same return lowering supports a nullary importer wrapper such as
`def relay():` with the indented body `return imported(11)`, after a leading
renamed load of `id`. The UTF-8 manifest fixture checks that the producer
retains declaration ID 0 and that the consumer wrapper receives ID 1 with
the resolved file-local import capture. Lean and pinned Go both observe the
wrapper's return value. When the wrapper calls `imported()`, the missing
argument preempts a later module assignment. As in the normalized examples,
load and return evaluation use the existing resolved loader. The text
fixture exercises the normalized wrapper shape from #4613.
[Importer controls](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Checks.lean) · [Checked wrapper profile](https://github.com/hiloopai/silmaril-lean/pull/4613)


For module 0, the producer text is

```starlark
# 雪
def id(x):
  return x
```

For module 1, the consumer supplies the label table `[("pkg:dep", 0)]` and
uses this text

```starlark
load("pkg:dep", imported="id")
out = imported(7)
```

The kernel-checked cold load publishes only `out = 7` from the consumer. A
missing export in the leading load leaves only the successful producer in the
cache and the consumer's first body assignment unexecuted. The Go controls
exercise both cases. They also run a late load with a missing export and
observe the preceding assignment. The frontend rejects late loads as outside
this leading-load profile. Nested loads, empty import lists, and private export
names have separate diagnostics or validation errors.
[Loader checks](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Checks.lean)

`Frontend.Module.Loader.runs_iff_load` reuses the existing agreement theorem
after preparation, on the normalized manifest and shared declaration table.
The two-module examples exercise specific source texts. General text adequacy
and a correspondence between Go's partial globals and the Lean session remain
open. [Loader theorem](../../Silmaril/Languages/Starlark/Frontend/Module/Loader/Thms.lean)

## Logical lines and layout

- LF, CRLF, and bare CR each end one physical line. Blank and comment-only
  lines contribute no newline or layout tokens. A physical break inside a
  matched `()`, `[]`, or `{}` pair is ignored for layout. A backslash
  immediately before a physical break also joins lines. Leading whitespace on
  the continuation line is ordinary whitespace.
- A significant line with more leading spaces opens an `indent` level. A
  smaller width must match an open level or zero, and emits one `outdent` per
  level closed. `indent` spans the leading spaces. Each `outdent` is zero-width
  at the first token of the new line. A mismatched dedent highlights its
  leading whitespace. Tabs are allowed between tokens and on ignored or
  continued lines. A tab in significant indentation is a `tabIndent` error
  under the pinned [space-only rule][layout-spec].
- EOF closes any remaining levels. When a final indented statement has no
  physical newline, the lexer inserts a zero-width newline before the
  zero-width outdents and EOF. The tests check that every successful token
  stream in the fixture corpus keeps a nonnegative layout depth and ends at
  depth zero with EOF as its final token.
- A stray or mismatched closing delimiter highlights the closer. An unclosed
  delimiter highlights the innermost unmatched opener. A missing suite and an
  unexpected indent are separate parser diagnostics. Function and statement
  spans end at their final code token. Nested source positions remain available
  in the token stream.

## Admitted surface

| Layer | Covered |
| --- | --- |
| Module statements | Name assignment, including a parenthesized name target, `pass`, and scalar expression statements. Newlines and semicolons separate simple statements. A final semicolon is allowed. |
| Function statements | The same simple statements, bare and valued `return`, and nested multiline `if`, `elif`, and `else` suites. Missing `else` lowers to `pass`. The module entry rejects top-level `if` and `return`. |
| Operands | ASCII names, parenthesized scalar expressions, and arbitrary-precision decimal, `0o`/`0O` octal, and `0x`/`0X` hexadecimal integers. Lexical resolution handles the names `None`, `True`, and `False`. |
| Precedence | Strongest first are unary `+`/`-`, `*`/`//`/`%`, `+`/`-`, comparisons, unary `not`, `and`, `or`, and `a if test else b`. Arithmetic and logical binaries associate left, comparisons are non-associative, and conditionals associate right in the `else` branch. |

`unsupported feature` identifies a boundary such as an inline suite, parameter
with a default, nested definition, or a call suffix. Later syntax in that
construct can still be malformed. Parameter binding, function installation, and
module publication remain outside the standalone function entry point. The
existing [Lean quotation](starlark-functions.md#quoting-an-expression-in-lean)
targets the normalized function language and uses Lean syntax.

The lexer retains the contents of simple unescaped quoted strings for load
operands and mapping spread keys. It identifies the closing delimiter and defers content and escape
validation for other quoted literals. Non-ASCII characters outside
comments and quoted literals are possible name characters pending Unicode
category checks. `exhausted` is an internal recursion guard bounded from input
length and token count.

## Pinned parser comparison

```sh
lake build --wfail +Silmaril.Languages.Starlark.Frontend.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks \
  +Silmaril.Languages.Starlark.Frontend.Module.Loader.KeywordOnlyChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.AssignmentCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.CallStatementChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.LogicalCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ConditionalCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.BranchCallChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.ListDisplayChecks \
  +Silmaril.Languages.Starlark.Frontend.Module.TupleDisplayChecks +Silmaril.Languages.Starlark.Checks
scripts/starlark/frontend/run.sh
```

Use the repository Lean toolchain, Git, and Go 1.25 or newer. The oracle feeds
Go the same fixture strings as Lean and checks syntax acceptance with
zero-value `syntax.FileOptions`. The fixtures cover delimiter continuations,
explicit joining with LF, CRLF, and CR, ignored blank and comment lines,
multiple EOF outdents, and mismatched dedents. Both parsers accept inline tabs
and reject form feed and a backslash followed by a space. The module controls
also compile the same Go syntax trees and run successful programs with an
empty host. They compare integer `out` exports, default evaluation,
validation errors, and runtime errors with `out` still unbound. The
observations cover selected bindings and error phases. The Lean residual heap
and Go partial globals remain outside the comparison.

Shared fixtures check nested spread values and binding failures. Competing
errors show that the callee read precedes operands, the named operand precedes
`*`, `*` precedes `**`, and evaluation errors preempt expansion. Other fixtures
show mapping expansion takes precedence when both spread values are invalid.
Go-only controls use mutation and a call in callee position to observe the
callee and four operand groups running once in order. Operand effects survive
reached spread and binding errors. A failed computed callee retains its own
effect and prevents outer operand effects. Go-only controls also check the
rejection of named operands after `*` and `*` after `**`.
[Shared spread checks](../../Silmaril/Languages/Starlark/Frontend/Module/SpreadChecks.lean) · [Go effect controls](../../scripts/starlark/frontend/spreads.go)

The pinned Go scanner accepts significant tabs. The fixtures observe one tab
or a space plus a tab aligned with eight spaces, and two tabs aligned with
fifteen spaces. Dedenting from sixteen spaces to two tabs fails in Go. The
Lean frontend rejects significant tabs under the core rule. Go also admits
`0b` integers and the name `assert`. Its syntax pass accepts an unassignable
scalar target, duplicate parameter names, top-level `if`, and top-level
`return`, with validation handled separately from syntax. The Lean frontend
reports those errors at its source boundary.
[Go scanner][go-scan] · [Oracle driver](../../scripts/starlark/frontend/run.sh)

## Next parser boundary

- Add inline suites and use the layout tokens for `for` and nested definitions.
  Extend the normalized module adapter with named variadic parameters
  and additional call positions. Broader load spellings and
  positions can extend the leading-load profile.
- Extend expressions with tuple and collection displays, calls, attributes,
  indexing and slices. Add membership, the remaining operator levels,
  comprehensions, and lambdas as their target AST forms become available.
- Finish literal validation and decoding for strings, bytes, escapes, and
  floats. Add Unicode letter and decimal-digit classification for identifiers
  and carry nested source locations through the eventual module adapter.

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lexical-elements
[layout-spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#special-tokens
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
[go-scan]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/syntax/scan.go#L495-L658
