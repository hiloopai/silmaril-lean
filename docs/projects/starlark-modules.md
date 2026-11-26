# Starlark module publication and imports

The profile follows the Bazel-team core specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. Raw `spec.md` has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Module execution][modules] · [Load statements][loading]

`Silmaril.Languages.Starlark.Modules.Thms` exposes the resolved entry point
`initializeModule`. It checks argument-list legality and conflicting global
and file names before allocating slots. It executes top-level commands in
order. `TopCode.assignExpr` writes one global after evaluating a resolved RHS,
and `TopCode.evalExpr` evaluates a resolved expression and discards the value.
Both admit nested calls with keyword and spread operands, conditional
expressions, and short-circuit operators in the [direct expression profile][expressions].
Runtime errors retain operand effects without writing the assignment target
or running later commands. Existing atomic commands, definitions, calls,
and loads with named aliases use the same lifecycle. Temporary slots used
by call lowering and file-local imports remain outside the export list.

The entry point assumes resolved bindings, the list of declared globals,
single assignment of explicit globals, and legal load identifiers. The
[source adapter](#resolving-module-declarations) collects the scopes for an
admitted normalized AST.
[Definitions](../../Silmaril/Languages/Starlark/Modules/Defs.lean)

The host supplies a pure catalog of already published modules. It determines
how labels are interpreted. All modules in a catalog share the same heap
and the same linked function-declaration table. An imported value retains
its address, so calling an imported closure uses that closure's original
global slots. A missing catalog entry and a missing exported name are
distinct failures. Private import names are rejected during validation.
A single load calls the host once and looks up its requested exports from
right to left, following the pinned Starlark-Go `LOAD` instruction. It writes
aliases in that same order after every lookup succeeds. If more than one export
is missing, the rightmost missing source item is the reached error and none of
the command's aliases are written.
[Load statements][loading] · [Lexical calls](starlark-functions.md)

A new module begins with fresh slots and no inherited active iterators.
Successful completion freezes all global values, including private ones,
before publishing the public export table. Runtime failure returns the
updated heap with the caller's scope and iterator context restored. The
failure path publishes no module and performs no publication freeze.
A caller supplies both the initial heap and any prepublished imports.
The heap may retain unreachable allocations.
[Module execution][modules] · [Reachable freezing](starlark-lists.md#reachable-freezing)

`runs_iff_runCommands` proves exact agreement before publication, including
the module and file namespace and the shared heap at the first failure.
`initializes_iff_initialize` extends agreement through the publication
boundary, comparing the export table or error and the entire residual
state after restoring the caller. Both proofs compose independent command
sequencing with `Exec`; its native expression rules derive calls and callee
bodies independently of the direct denotation. The module rules and
denotation share validation, namespace entry, the pure catalog contract,
and publication or failure restoration. Calls start with the finite linked
declaration table and remove the active declaration on descent.
[Operational rules](../../Silmaril/Languages/Starlark/Modules/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Modules/Thms.lean)

## Resolving module declarations

`Modules.Resolve.resolve` takes normalized source commands and returns a
checked `Modules.Source` and linked declaration table. Module commands cover
single-name and [nested name-pattern assignment][pattern-assignment], [simple subscript assignment][subscript-assignment],
[integer subscript `+=`][augmented-subscript], expression statements, `def` and
named `load` imports. Function bodies add nested `def`, sequencing, `if`, `pass` and
`return`, as well as `for` loops with `break` and `continue`.
Signatures represent the positional, keyword-only, `*args` and
`**kwargs` classes used by the existing binder. Operands use the
[existing source expression profile][source-expressions], including the Lean
expression quotation.

The resolver collects globals and load aliases across the file, and
parameters and assigned names across each function body. A lexical binding
shadows outer names throughout its block. Undefined names fail statically
even in skipped code. A forward reference resolves to the slot but fails
dynamically if read before its assignment or load. Duplicate module bindings
and load/global collisions are rejected before execution.

For standalone destructuring, `Statement.assignTarget` resolves each name
leaf to a function slot and `Command.assignTarget` resolves each leaf to a
module global. The resolver collects those names before analyzing any RHS.
Both contexts also accept `assignTargetCompExpr` with the same target and
a `CompExpr` right-hand side. This form also accepts subscript leaves
whose receiver and index use the ordinary resolved expression grammar.
Only identifier leaves join the enclosing lexical block.
The module command uses the shared direct binder in source order. A failed
initialization retains earlier heap effects, including partial writes into
its slots, and follows the existing failure path without publication.
[Pattern semantics][pattern-assignment] · [Source assignment fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

The `assignListComp` and `assignDictComp` forms in `Statement` and
`Command` resolve comprehensions assigned to a name. Only that destination joins the
enclosing block. The first iterable uses the enclosing scope and the
remaining clauses resolve with all generator names local to the
comprehension. Quoted expressions can supply the pattern, iterable,
filter and yield ASTs, including dictionary key/value pairs. Resolved module
commands enter the same body
path as function assignments, then use the ordinary publication rules.
[List comprehension semantics](starlark-functions.md#list-comprehension-assignment) · [Dictionary comprehension semantics](starlark-functions.md#dictionary-comprehension-assignment)

The normalized `CompExpr` adapter allows comprehensions in call operands,
conditional and short-circuit operands, collection displays, and index
and slice reads within return values, assignment RHSs for names and
nested name patterns, operands of standalone simple and integer
augmented subscript stores, function-local integer augmentation, and
parameter defaults.
The first and later iterables and filters and the heads of a comprehension
use the same broader placement grammar.
Both selected and skipped AST positions are resolved before execution.
The emitted body evaluates only reached operands, preserves their order
and keeps prior shared heap effects on failure.
[Expression placement](starlark-functions.md#comprehensions-in-checked-expression-positions)

A loop target belongs to the whole function block. The resolver collects
all target names before resolving the iterable and body in that block. Thus
`for x in x` reads the function's `x` before any iteration writes it. The
last assignment to the target is visible after the loop, and an empty
loop performs no target write. Loops emit `Body.forInExpr` and use
the existing validation of `break` and `continue` in each function, including
skipped code and nested definitions. Tuple and list patterns with lexical
name leaves enter through `Statement.forInTarget`, for example
`.forInTarget starlark%[(x, [y, z])] starlark%[rows] .pass`. The resolver
rejects non-name leaves even in skipped code. A single identifier can use
`Statement.forIn`. The module command type admits
only top-level forms permitted in this profile.
[For statements in the pinned spec][loops] · [Resolved loops](starlark-functions.md#calls-inside-loops) · [Source loop fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/LoopChecks.lean)

Defaults resolve in the enclosing scope. Function bodies use the function's
own parameters and locals, and each declaration captures the free slots its
body or nested definitions need. A definition passes those slots through any
intervening function. The evaluator runs defaults when it executes the
definition command and installs the closure only after they succeed.
`SourceParameter.defaultExpr` accepts the normalized `CompExpr` grammar.
An ordinary quoted `SourceExpr` coerces to a plain expression.
[Name binding in the pinned spec][names] · [Resolver](../../Silmaril/Languages/Starlark/Modules/Resolve/Defs.lean) · [Comprehension defaults](starlark-functions.md#comprehensions-in-parameter-defaults)

```lean
module

import Silmaril.Languages.Starlark.Modules.Resolve.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs

open Silmaril.Languages.Starlark.Modules.Resolve
open scoped Silmaril.Languages.Starlark.Functions.Lowering.Quote

def exampleModule : List Command := [
  .assign "seed" starlark%["definition scope"],
  .define "pick" { positional := [⟨"seed", some starlark%[seed]⟩] }
    (.ret (some starlark%[seed])),
  .assign "out" starlark%[pick()]]

def exampleResult := runModule exampleModule (fun _ => none) {}
```

This module exports `out = "definition scope"`. `runModule` reports
elaboration errors separately from runtime errors and uses the resolved
module initialization and publication rules. Supply the existing linked
table when catalog values can contain closures. Resolving another module
appends declarations and preserves the IDs already in that table. To use
the finite loader, clients assemble the manifest and link its resolved
sources to one table.

`checked_of_resolve` states exactly which checked source and declaration
table successful elaboration produces, including the globals in source order
and absence of compiler scratch slots. `initializes_iff_runModule` composes
the elaboration result with the resolved operational theorem. It compares
static rejection, execution outcomes, publication and the exact residual
state. This correspondence shares the elaborator and starts at a normalized
AST with legal identifier spellings. A separate
[mixed assignment theorem](starlark-functions.md#mixed-name-and-subscript-targets)
relates accepted targets and a bounded RHS to independent lexical rules.
The block collection theorem below supplies that environment and write
scope for its admitted forms. A separate theorem covers capture selection
and installation along a bounded nested function chain. Whole-module
elaboration against independent source rules and text parsing remain open.
Lambdas, general comprehension expression
positions, field leaves, store leaves in loop and comprehension targets,
and other augmented assignment forms remain outside this source fragment.
The pinned Starlark spec rejects slice assignment targets.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Resolve/Thms.lean) · [Lean source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

Pinned Starlark-Go checks cover static and dynamic name errors, captures,
defaults, load aliases, and loop scope and control. Go rejects the
load-then-global collision and accepts the global-then-load order. The Lean adapter follows the
Bazel-team spec and rejects both.
[Pinned Go comparison](../../examples/starlark/scope/check.go) · [Name binding in the pinned spec][names]

### Lexical block collection

`ModuleBinders` and `BodyBinders` state which normalized commands and
statements declare names, with their occurrences in source order. The
load-free module subset covers name assignment, mixed patterns,
ordinary subscript stores, expression statements and definitions. The
function subset also covers pass, return, sequences and both branches of
a conditional. A definition binds its name in the current block. Its
parameters, defaults and body do not contribute binders there. A nested
block can be collected separately using the parent's read context.

In a mixed pattern, only a name leaf contributes a declaration. A
receiver, subscript index, RHS and comprehension generator contribute no
declaring occurrence in the surrounding block. `ParameterBinders` follows
the normalized parameter classes. `LocalBinders` keeps the first occurrence
of each other body binder. An assignment to a parameter reuses its slot.
`owned_read` selects a body binder's owned slot even before its first
assignment and even when an enclosing or global name has the same
spelling. An uninitialized slot fails when read.

`moduleBlock_eq` and `collectFunctionLayout_eq` prove the existing
compiler's collection and write-scope phases agree with the declarative
rules. `module_assignment_sound` and `function_assignment_sound` compose
with the independent mixed-assignment elaboration theorem and put each
resolved name leaf among the declared globals or owned slots. Assignment
elaboration still uses the bounded leaf and RHS grammar. The block rules
cover declaration occurrences only. Identifier, parameter, duplicate
global and runtime validation remain in the existing checked entry point.

The function collection theorem takes the parent context as input.
Whole-source execution, unproved binder grammar including load aliases
and loop targets, and broader leaf and RHS elaboration remain open.
[Block judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Checks.lean)

### Nested function captures

The capture theorem starts in a load-free module. The inner function
has required positional parameters and a body
consisting of `(name, receiver[index]) = rhs` followed by `return operand`.
The leaf and return operands use the bounded #3171 grammar. The RHS is a
plain operand or a single-generator list comprehension in that grammar.
`parent_layout` supplies the outer function's owned names and inherited
module globals from the proved block collector. The forwarding theorem
permits any finite number of intervening functions that define and
return their child, with required positional parameters at every level.

`BodyReads` gives the binding occurrences of the RHS, target and return,
in that order. `Selects` ignores owned parameters and locals. For a free
local, `Nearest` chooses the first enclosing block that owns the name.
The module rules resolve an otherwise unshadowed name to its global slot. It retains the first occurrence of
each free reference in the Lean declaration. The comprehension generator
contributes no free read of its own binding. `mixed_definition` connects
these rules to the exact declaration appended by the compiler. Go uses
cells for enclosing free variables and carries the module's global
dictionary separately. The Lean list represents just the module slots
that are read. Its order is a Lean representation property.

`define_installs` relates selected addresses in the defining activation
to the new heap cell and the binding holding its function reference.
Restoring the caller preserves that cell. `activate_selected` preserves
the installed addresses while allocating the callee's own slots.
Creation consults the slot address. Reading an uninitialized binding
through that address fails when invoked. `read_after_rebind` states that
a write by the slot's owner is then visible to that callee. A list store
through the captured value instead changes the list's heap cell. Both
observations agree with the pinned spec's free-variable references and
the pinned Go fixtures.

For each wrapper, `compile_chain` proves that the child definition's
capture demands feed the wrapper's own capture list. `nearest_route`
identifies the forwarding prefix up to the nearest local owner.
`global_route` carries the module-global reference through every
wrapper in the Lean representation. `child_installs` derives all of the
next child's slot addresses from the parent's installed captures and the
owned slots allocated at activation. `local_address` and `global_address`
preserve the original address through every successful creation and
activation on the corresponding route, including its local-cell tag.

The forwarding path starts from the source address and successful definition
and activation steps. It supplies the next child's capture slots from the
parent layout. The entry and argument bridge below derives the root
addresses, the live owned destination cells, and positional argument
preparation that can feed these steps.

The five-level fixture creates the leaf before the nearer owner rebinds
a list reference, then invokes it after escape. It also observes a
separately forwarded module slot before and after initialization. Lean
checks the emitted lists and runtime local-cell tags. The observable
results agree with pinned Go.
[Judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Defs.lean) · [Forwarding judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Defs.lean) · [Forwarding theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Forwarding/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/scope/check.go) · [Pinned definition semantics](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions) · [Go lexical selection](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L960-L990) · [Go shared cells](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L642-L661)

### Checked module entry and positional binding

The independent load-free binder judgment supplies the module's global
list. Actual module entry allocates a fresh owned cell for each declared
global, initially unbound even when the caller has a populated heap.
An independently emitted root capture plan names only those globals.
`checked_root_definition` uses these facts to derive the root capture and
definition-target cells and its exact closure allocation. The proof
uses the supplied declaration lookup in the checked table.

`Assigns` pairs required parameters with evaluated positional actuals in
order. `Binds` accounts for success, a missing suffix, and surplus
arguments. The exact preparation theorem derives signature validity from
module validation. Successful preparation activates with the derived
arguments. Binding errors preserve the pre-dispatch state. For a root
definition immediately followed by preparation, the declaration lookup
also supplies its membership in the initial finite availability set.
`activated_cell` derives a live owned cell for each declared parameter or
local in the resulting frame, even after argument writes.

`checked_first_read_error` starts from a normalized module whose first
command reads a declared global. Its exact result is the uninitialized
error with the caller frame restored and the entry heap retained. The
rest of the commands do not run. The executable fixtures also reach
this error inside a closure call and distinguish it from missing and
surplus argument errors before body entry.

The module entry bridge takes evaluated positional actuals. The source
site and operand theorems below supply these premises in a bounded
profile.
[Binding judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Defs.lean) · [Entry theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Entry/Checks.lean)

### Root definition sites and call operands

`checked_root_site` relates a normalized root definition at its source
command position to the ID in the emitted command and the corresponding
entry in the final declaration table. A linked table and earlier
commands can determine the starting offset. Children are appended
before their parent. The admitted suffix can contain name assignments,
expression statements, and unrelated required-parameter definitions in
the forwarding chain profile. Successful suffix compilation preserves
the root entry at the ID its command emitted. The root and other
admitted definitions use the existing chain acceptance evidence,
uniform in their incoming table. The setup theorem gives the root
definition step in the fresh module frame.

The independent operand judgment covers declared global reads, integer
and string literals, and subscript reads. Its list judgment evaluates
the callee first and positional actuals left to right. These operands
retain the frame and heap. A reached callee, receiver, or argument error
prevents later evaluation and dispatch. The source-site theorem places
the corresponding call at its checked expression-statement position.
After successful reads, the independent binder derives each assigned
parameter or an arity failure. The invocation theorem connects this to
the exact resolved activation, and transports a supplied callee-body
execution through caller restoration and the existing denotation via
`exec_iff_denoteBody`.

Intervening successful name assignments with admitted operands can
copy the live closure to another binding. Their emitted commands
occupy the corresponding source segment. Distinct owned module slots
and binding-only writes preserve the original callee and function heap
cell. These theorems leave whole-module sequencing and independent
wrapper/leaf body execution through escape and publication open.
Assignments to the callee binding, effectful or nested-call operands,
defaults, other argument forms, loads, and broader bodies are outside
this proof. The Lean fixtures distinguish operand failures from
surplus arity and exercise linked code, later unrelated definitions,
and a copy of the live closure.
[Judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/RootCall/Checks.lean) · [Pinned call semantics](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions)

### Wrapper returns and reached command prefixes

The compiler now records the child ID used inside every wrapper.
Checked module elaboration preserves the entire emitted chain in the
final declaration table, including through admitted unrelated suffix
definitions. If the root definition is the first command, fresh module
entry supplies its target cell and the addresses it captures.

A wrapper here has a required positional signature and a body consisting
of its child's definition followed by a return of the child's lexical
name. The independent return rule allocates the child closure and
specifies its address, selected captures, and restored caller state.
The checked activation supplies the local definition cell. The parent
captures and frame layout supply every capture address for the child,
including forwarded local addresses. The proof derives the exact
definition and return body steps, and proves the child cell is
still available after restoration. Pre-existing heap cells and caller
slots are preserved. An assignment of the return to a valid owned
destination reads back the escaped address.

The inductive wrapper path composes successive invocations of escaped
closures. Its bound is the number of available wrapper positions in
the chain. Arity failure stops at the reached invocation with all
earlier allocations retained. Each call body runs with its declaration
removed from the available set. Each separately reached invocation
starts with the full set. The resolved operational path and the
existing dispatch and body denotations agree on the exact result and
state. The path takes already evaluated positional values. The
checked named-assignment theorem uses independent source operand
evidence and derives binding and the wrapper body at the actual
command site. A reached operand or arity error skips the assignment.

The reached-prefix judgment composes source steps in order. Its
transfer theorem preserves the final state at a reached error and passes
a complete trace through the checked publication boundary.
[Wrapper judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Wrapper/Checks.lean)

### Mixed leaf execution and publication

The independent leaf judgment covers the normalized function body
`name, receiver[index] = rhs` followed by `return value`, with one
identifier read in each operand position. It derives lexical references
from the block's owned, enclosing, and module names. Execution reads the
RHS once, checks the two-item unpack before either write, sets the
local, then reads the receiver and index in the updated frame. The
subscript store and final read share the same heap. A reached error
keeps the earlier writes. The proof identifies the emitted leaf code
and shows that removing compiler scratch bindings gives the exact
frame and heap prescribed by the source rules.

`checked_first_definition` supplies the initial source definition step
and links its declaration chain from checked module entry.
`checked_module` composes definition, setup assignment, and named
positional call steps through escaped wrappers and the mixed leaf.
Call operands use the bounded read-only profile. A reached operand
error skips binding and dispatch. A binding error skips activation.
The theorem takes an independent reached trace with command-site,
live-closure, and lexical evidence. It derives the resolved body
execution and the denotation for both outcomes. Independent
publication collects initialized declared globals in order, exports
public names, and freezes the heap reachable from all collected
values. A reached error restores the caller with the residual heap
and yields no publication. The next theorem constructs this trace
for a stated subset of checked modules.

The Lean fixtures check the exact success exports, freezing, and a
late uninitialized read that preserves a mutation before failure.
A separate fixture derives that late leaf error from the independent
assignment rules. Pinned Go checks escaped mutation, later owner
rebinding in a wider wrapper, and successful publication freezing.
Go's `Program.Init` exposes a mutable partial namespace on failure.
`ExecFileOptions` also exposes that namespace and freezes it. The
checked Lean failure result contains the restored caller and the
retained heap.
[Source judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Leaf/Checks.lean) · [Pinned Go fixture](../../scripts/starlark/mixed-leaf.go)

### Constructing the bounded module trace

`Trace.checked_source_module` takes a static `Profile` over normalized
commands and successful checked compilation. It derives declaration
collection, lexical evidence, each reached command position and each live
closure cell, starting from the actual module entry. The initial caller
and linked table can be supplied by the host. Module entry allocates
fresh globals, including those in a suffix that may be skipped.

The profile has one leading definition with any finite number of
required-positional define-and-return wrappers. Each reached wrapper
call stores its child in a module name. Each next call names that
result directly. Setup assignments can occur between the calls and
after the leaf call. While a closure is pending, setup must write a
different name. The operands admit integer and string literals,
declared module reads, and recursive subscripts. Setup also admits
list and tuple displays over those operands. The mixed leaf
uses identifier reads in all operand positions. Its local declarations
and nearest capture owners follow the existing checked block layout.
The ordinary validator still rejects invalid emitted signatures and
duplicate module names.

The proof constructs the trace by induction on the source schedule.
It uses independent operand evaluation, argument binding, wrapper
allocation and leaf rules. No execution premise about the reached
commands is needed. An operand error precedes binding, and an arity
error skips activation. At the first error, the trace stops with the
heap from the reached step, including any earlier leaf writes. The
publication rules derive the exact ordered exports, freezing from all
initialized globals including private ones, or caller restoration with
the retained heap and no published mapping.

The fixtures instantiate the theorem from the static profile for
success and two error cases. The corresponding evaluator checks cover
a frozen private tuple, an uninitialized read after a shared write,
and an index error before surplus-argument rejection. The live-binding
theorem below extends this schedule to independent definitions and calls.
[Profile](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Checks.lean)

### Traces with multiple live callees

`Trace.Bindings.checked_module` derives a reached trace for checked
load-free modules that interleave unrelated definitions, setup, and
independent or repeated calls to the same supported bodies. Its source
schedule tracks which definition or escaped child may be called through
each module name. Explicit copies of tracked names can create aliases.
The initial tracked environment is empty. Execution supplies the actual
binding cells, closure addresses, capture lists, and lexical blocks.

For a reached definition, the checked-site theorem locates its actual
declaration index in the final table. Later emissions preserve earlier
indices. On a successful call, a wrapper advances the destination to
its child while keeping other tracked names callable. An explicit copy
uses the closure already held in the source cell. Other assignments
update or remove provenance at their own destination. Each call reads
the live value and uses the shared heap. Successful leaf stores can
change list or dictionary contents while preserving earlier binding
and function cells. The trace stops at the first error and retains
its state. Publication freezes exactly the values reachable from the
initialized globals on success. Failure restores the caller with the
residual heap and no published mapping.

The normal validator still rejects duplicate module bindings. The
profile preserves lexical reads of later-initialized globals, local
assignment before a target read, and mutations through shared aliases.
A callee needs provenance from a definition, a wrapper return, or a direct
name copy. Calls through arbitrary results or collection lookups,
wider bodies and operands, defaults, loads, and text parsing remain
outside this theorem.

The fixtures check a wrapper's escaped child and an unrelated mixed
leaf at distinct table IDs. Both touch the same list. A repeated call
uses an alias to the escaped child. The failure control reaches an
uninitialized read after the second definition mutates the list and
skips the remaining call. The Go control observes the residual state
through `Program.Init`.
[Profile and invariant](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/multi-callee/check.go)

### Checked positional defaults

`Trace.Defaults.checked_module` constructs an independent reached trace
for one module definition surrounded by read-only or allocation-only
setup assignments. The signature has a required positional prefix and
an optional positional suffix. Default expressions use the module's
defining scope and admit the existing read-only operands and flat list
and tuple displays over those operands. The function body returns one
of its own parameters. Compilation identifies the definition's actual
index in the final declaration table.

The source rules evaluate defaults once in declaration order. Each
operand sees the heap left by its predecessor. A reached error skips
later defaults and leaves the definition target untouched. The module
theorem agrees with operational initialization and the module denotation
on the whole observation, including the restored caller and retained
heap on failure. Successful publication freezes values reachable
through saved defaults even if those values have no exported name.

`checked_installed_defaults` connects successful source evaluation to
the new closure cell. At any later state retaining that cell's closure
record at its address, the independent binder agrees with native call
preparation on the exact activation or an error with the same state.
Explicit operands replace the corresponding defaults, omitted slots
consume the saved values, and missing required slots or surplus
arguments fail before any frame allocation. The finite declaration
guard is the checked module entry table's full index range. Binding
uses the saved values even if the original names have been rebound.
A mutable saved value retains its heap address and observes subsequent
writes through aliases.

The definition-only theorem also has controls for a reached
definition-time error. Go's comparison observes its returned globals
and errors. The Lean fixtures check the residual allocation and its
freeze bit directly.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Checks.lean) · [Pinned spec][default-parameters] · [Pinned Go comparison](../../scripts/starlark/positional-defaults/check.go)

#### Defaulted calls in the multiple-callee trace

`Trace.Bindings.WithDefaults.checked_module` extends the multiple-callee
schedule with module definitions whose bodies return one of their own
parameters. A reached definition evaluates its defaults before binding
the new closure. Its live evidence connects the stored address, the
emitted declaration in the final table, and the ordered saved values.
An explicit name copy keeps that same address and saved record. Calls
to independent required-argument wrappers and mixed leaves preserve
existing closure cells even when they change a collection that a saved
value aliases.

A defaulted call reads the live callee first and evaluates its bounded
read-only operands left to right. Failed operands stop the call before
binding. Once operands succeed, the independent positional binder uses
the saved record for omitted arguments or reports missing or surplus
arguments before allocating a frame. A successful binding supplies the
activation in which the body reads its parameter. The return restores
the caller, and only a successful return writes the destination.
Starting at actual module entry, the reached source trace agrees with
operational initialization and the module denotation on exact exports
and reachable freezing, or the first error with the residual heap and
no publication.

The shared-profile fixtures interleave an aliased defaulted closure
with a separately called mixed leaf that mutates a saved list. They
check repeated omitted calls, an explicit override, and a reached index
error that precedes both a later uninitialized operand and surplus
arity. The pinned Go control also exercises repeated calls after
rebinding a defining local in a nested function. The checked source
trace covers module-level defaulted definitions and the bounded
escaping wrapper below. Broader nested definitions, defaulted bodies
and operands, computed callable provenance, keywords and spreads,
loads and text parsing remain outside the theorem. The existing rejection of
duplicate module bindings also applies.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/default-call-trace/check.go)

#### Escaping nested defaults

The checked schedule also admits a wrapper with one required parameter.
The wrapper defines a positional function whose body returns one of its
own parameters, rebinds the wrapper parameter to an integer, and returns
the child. Defaults may read the wrapper parameter, index that value
with a literal integer, or use an integer or singleton integer list
display. The child body has no captures in this profile.

The source compiler links both declarations at their actual indices.
On entry the wrapper owns a cell initialized by positional binding and
a different cell for the unbound child name. Source defaults evaluate
in that reached frame and run in declaration order. Allocations extend
the heap. On success the child saves the resulting values, including
any mutable alias, before the wrapper write. Returning the child
restores the caller with the same closure cell. The module schedule
tracks its address across copies and uses its saved values for omitted
arguments. An explicit operand overrides its own slot. Publication
freezes values reachable through the saved record.

The failure control allocates the first default before the second
fails on an index. The earlier allocation remains in the residual
heap. The child name stays unbound, the local write and subsequent
module commands are skipped, and there is no publication. Pinned
Starlark-Go agrees on the results and reached error. The Lean checks
also inspect the exact residual heap and restored caller. More general
wrapper bodies, nested chains of defaulted declarations, and captures
in a defaulted child body need separate source rules.
[Profile and source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Defs.lean) · [Frame and body theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Thms.lean) · [Module theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Bindings/Defaults/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/escaping-defaults/check.go)

#### Compositional bodies for defaulted calls

The multiple-callee schedule can also admit a module definition with
a sequence of lexical name assignments followed by a return. The
independent body judgment relates each source operand to its scoped
read and records the reads in source order. The local binder judgment
collects the whole body before any read is resolved. Capture selection
is derived from those reads. The supported operands are name reads,
integers, subscript reads, and singleton list displays over admitted
operands. All assignment targets use owned slots.

`Defaults.Body.body_agrees` derives a complete reached body from that
static relation and the activation invariant. Owned names, including
unbound locals, have fresh binding cells. A selected capture denotes
a live caller cell below the activation's allocation boundary. Each
assignment evaluates its RHS before writing, and any reached error
stops the sequence. The final frame and retained cells agree exactly
with independent operational execution and the body denotation.

Module entry derives the capture addresses and saved-default binding
for root definitions. An alias keeps both records. The source module
trace restores the caller and agrees on publication and freezing or
the first error and residual heap. The fixtures read a module binding
initialized after function definition and compare omitted with explicit
arguments. Calling before that binding initializes retains a prior
local list allocation and assignment, skips subsequent body and
module commands, and leaves the call destination unbound. The pinned
Go control observes its partial globals and error. The Lean control
also checks the residual heap and restored frame.

The generic body theorem accepts live enclosing captures through its
frame premise. The checked module integration derives this premise
for captures of module bindings and for the nested case below.
Control flow and wider body operands and assignment targets remain
outside the compositional body profile.
[Body rules and frame invariant](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Body/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/defaulted-body/check.go)

## Enclosing captures in defaulted bodies

The multiple-callee trace admits an escaping wrapper with required
positional parameters and a compositional child body. The wrapper can
execute a straight-line sequence of lexical assignments before the child
definition. After definition it rebinds its first parameter and can
execute integer assignments to other local names. The whole-block
collector places binders from both sequences and the child definition
in first-binder order. Repeated assignments share one slot.
`Defaults.Escape.Scoped.checked_site` links the layout, the compiled
prefix and the independently selected capture list to the emitted
declarations.

The prefix uses the straight-line body rules for local and module reads,
integers, indexing and singleton list displays. An owned name shadows a
module name throughout the wrapper block. Capture selection visits the
prefix reads followed by the defaults' reads. Module entry supplies
selected addresses from the reached module frame. The trace preserves
those addresses through aliases and module statements.
`prefix_module_read` relates an installed address to the current module
binding, including an uninitialized cell.

The prefix judgment composes with any reached continuation. It preserves
owned slot addresses and existing caller cells. A prefix error restores
the caller immediately with the reached heap, before defaults or child
installation. A successful prefix supplies the actual defining state
to the lexical default rule below.

`returned_frame` identifies the successful prefix state, exact default
values and child capture vector. The suffix updates the captured cells
and preserves the saved arguments. The checked module theorem carries
the escaped closure through aliases and repeated calls and gives exact
operational and denotational agreement on publication and reachable
freezing or on the first error, retained heap and restored caller.

The fixture defines the wrapper before module initialization. Calls
on either side of a checked list mutation save different values read
through the prefix. A further default reads a module name directly,
and another reads a wrapper local that shadows a module name. The
failure controls cover an uninitialized module read in the prefix,
an out-of-range prefix index, an uninitialized local default and an
uninitialized module default after a successful prefix. Lean checks
the capture kinds, retained allocations and caller restoration. The
pinned Go control checks visible results, failure state and freezing
with its default file options. Checked modules reject repeated name
bindings through the existing collision check.
[Source rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Defs.lean) · [Capture and frame theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Escape/Scoped/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/nested-default-body/check.go)

## Lexical defaults and reached definitions

`Defaults.Lexical.Elaborates` relates positional defaults to the same
lexical source expressions used in the straight-line body proof.
Parameter names label the saved results. Resolution of each operand
uses the defining block, including local shadowing and enclosing and
module origins. `translates` relates the lexical derivation to the
compiler's code and ordered reads. `evaluates_agree` gives exact
denotational agreement on the saved values or first error and its
heap.

`defines_total` constructs the reached operational and denotational
definition from the checked operands, the emitted declaration and an
`Installs` derivation in the actual defining frame. On success it
identifies the exact saved values and installed address vector. A
definition that forwards a capture uses the enclosing slot's address
through the same rule. The wrapper proof derives its module addresses
from actual module cells and its child's captures from reached locals.

The lexical rule covers read-only operands and singleton list allocation.
Calls and wider effects in defaults remain outside this rule.
[Lexical rules](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Lexical/Defs.lean) · [Default and definition theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Lexical/Thms.lean)

### Reached nested definitions and forwarded cells

`Defaults.Nested.plan_of_body` builds a local definition plan from the
independent binder, body and default judgments. The child body is a
straight-line assignment and return suite. `compile_definition` links
its ordered local slots and free references to the declaration at the
next code-table index. The enclosing compiler sees the defaults' reads,
followed by the child body's free references. `selects_parent` composes
these demands with surrounding reads, even when the parent makes no
direct read of the forwarded name.

`installs` derives the ordered capture vector and its live binding
cells from the reached parent frame. A name owned by that frame uses
its own cell, including under shadowing. An inherited request uses
the address already in that frame's capture slot. `activate_forwarded`
preserves that address in the child's activation. `reached` composes
these facts with the lexical-default theorem to give exact source,
operational and denotational agreement on installation with saved
values and on the first default error with its reached heap.

The Lean and pinned Go controls escape a child through an intermediate
definition. One call observes the saved list and the outer owner's
later rebinding of the live index. A shadowing parameter redirects the
same reads to the nearer owner. An uninitialized forwarded read stops
installation, preserves the earlier mutation, and prevents publication.
Lean also inspects the original capture address and the allocation
from the first default in the residual heap.

The local theorem takes independent source elaboration, the compiled
declaration lookup, and a reached parent frame invariant.
[Local source rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Thms.lean)

### Sequencing reached definitions

`Defaults.Nested.Sequence.Elaborates` composes any finite number of
local definitions and intervening lexical assignments with a final
return. Each child has the existing bounded straight-line body.
`compiles` links the full suite to normalized source compilation.
`collects` derives binder occurrences and `selects` gives the ordered
free references in the defining block. Later definitions extend the
code table while preserving earlier IDs. The running table may itself
be an extension of the emitted table.

`runs` constructs the independent source trace from the elaborated
suite and the active frame invariant. Every successful prefix supplies
the reached frame for default evaluation and ordered capture
installation. The tail starts in the resulting state, where the
definition's owned binding is live. A reached prefix or default error
skips all later statements. The theorem matches the full outcome and
frame with resolved execution and denotation and preserves the caller's
cells below the activation boundary.

`installation` exposes the exact local binding, function address, and
default record. `prepare_installed` reuses the checked positional
binder for a subsequent evaluated callee at that address when the
record is still live. This gives the exact activation or binder error.
Establishing that a later source operand selects that same record,
particularly after aliases and returns, remains a separate provenance
obligation.

The regression uses an intermediate function that defines siblings
before and after a defaulted child. It checks escape through a local
alias, a forwarded cell and a shadowing parameter. A failing default
retains the earlier allocation and sibling closure and skips the
later sibling and publication. Lean exercises the inductive rule on
the normalized intermediate body, and the module outcomes run through
the existing evaluator and pinned Starlark-Go.

The existing module theorem covers its separately documented call
shapes.
[Sequence rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/forwarded-default/check.go)

### Recursive elaboration of nested suites

`Defaults.Nested.Sequence.Recursive.Elaborates` descends into a
definition's child suite and the remainder of the defining suite.
There is no fixed nesting depth. Each child collects its own
normalized binder occurrences. The enclosing scope collects the
child's name and any assignments in its own block. The independent
binder order and scope judgment determine the emitted parameter and
local slots. The enclosing reads include the default operands' reads
followed by the child's ordered free references, even if the
intermediate body never directly reads those names.

`compiles` agrees with normalized compilation. `indices` places the
emissions at consecutive indices after the incoming table, with
descendants before their enclosing declaration and sibling suites in
source order. `links` gives the exact lookup at each emitted index and
preserves all incoming lookups. Together these results let a caller
reuse the emitted declaration after later siblings or enclosing
definitions have appended their entries.

`installs` uses the reached parent frame to supply the ordered
capture vector. `activate_address` preserves the address supplied by
either an owning slot or an inherited capture. An intermediate binder
with the same name terminates the outer demand and supplies its own
cell. `reached` applies lexical-default evaluation and installation to
one such definition, with exact execution and denotation on success
or on a reached default error.

The Lean control proves a grandchild suite's read order and emitted
IDs for any incoming table. It executes a normalized module with an
unrelated earlier declaration and checks the two closures' capture
addresses. The shadowing variant uses the intermediate parameter's
cell. Lean and pinned Go check both variants and rejection of a
duplicate grandchild parameter through the existing validator.

Syntax validation remains in checked module resolution.
[Recursive source rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/forwarded-default/check.go)

### Whole-suite execution after activation

`Defaults.Nested.Sequence.Recursive.runs` composes the recursive
elaboration with the same independent source execution judgment as the
shallow sequence. It derives each reached definition's lookup in the
final table and supplies its captures from the current frame. The
definition executes its defaults in source order, binds its name to the
new closure with those saved values, and advances to the tail. A
reached prefix or default error keeps the exact residual state. The
full sequence theorem returns the same outcome, frame and heap as
resolved execution and denotation. A child body can have its own
recursively elaborated suite and is deferred until activation.

`runs_activated` constructs the owned and captured frame by activating
the emitted declaration with bound arguments and live captured cells.
It proves the suite agreement there and restores caller bindings and
slots while preserving the caller's pre-existing heap cells. The
caller and the defining activation can differ. The theorem takes the
capture installation evidence, live cells and already-bound arguments.

For a single owned-name copy immediately after a successful definition,
`reads_installed_alias` derives the source read of the installed binding
and the later read of its alias. Both name operands return the same
function address, with the same declaration, captures and saved
defaults in the heap. Later calls through arbitrary expressions and
provenance through unrelated assignments or escape remain separate.

The Lean and pinned Go regression returns the recursively defined
relay through a local alias and reaches the grandchild through it.
Lean checks the forwarded addresses and the retained relay
closure and earlier list allocation after an index error. That error
skips the rest of the suite and the later module invocations.

The suite proof covers straight-line lexical assignments, returns and
nested definitions with the bounded positional default operands.
[Execution theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Thms.lean) · [Alias operand theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Thms.lean)

### Positional calls through a local closure

`Defaults.Nested.Sequence.Recursive.Call` connects an owned local
callee read to execution of its checked positional call. Its
`Arguments` judgment elaborates each operand in the caller's lexical
block. `resolves` proves the normalized resolver returns that code and
records the callee read before the argument reads. The runtime rules
evaluate the callee first, then evaluate positional operands once in
order. The argument profile is the existing lexical reads, integers,
indexing and singleton list displays.

`runs_installed_alias` gets the function address and actual closure
record from a reached definition and an immediate owned-name copy.
It derives the saved-default count and live capture cells from
installation. Operand evaluation retains the loaded record and those
cells. The independent binder reads the saved defaults from that
record, then uses the emitted declaration and original captures to
activate the callee. The whole-suite theorem supplies the callee
execution under the reduced declaration set. Resolved execution and
denotation agree on the exact result or error and state, including
caller restoration after activation. An operand error skips binding
and activation. A binding error leaves the state reached after the
operands, including their allocations.

The nested suite controls below exercise this preparation rule.
They distinguish a reached index error from surplus arity and check
that both failures retain the operand lists without adding an
activation frame.

The expression theorem uses the body's declaration lookup in a
checked table and membership in the available declaration set.
[Call rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Thms.lean)

### Positional call assignments in recursive suites

`Defaults.Nested.Sequence.Recursive.Call.Suite.Elaborates` extends
the bounded recursive suite with a definition, an immediate copy of
its local name, and a positional call assigned to an owned name.
It can compose multiple such segments with lexical assignments
and ordinary nested definitions. The binder and read judgments
include the new assignments and ordered call operands. Each call
ID is an actual emission, and later table extensions preserve it.

The suite theorem supplies the closure from its reached definition,
with the original capture addresses and saved defaults. On call
success it commits the result in the restored caller frame and
continues there. On a definition, operand, binding or body error it
keeps the reached heap and skips the tail. The source trace agrees
exactly with resolved execution and denotation, including the
return or first reached error and residual state. `runs_activated`
obtains the suite frame from live captures and bound arguments.

The guard requires that the current available declaration set
contain the call IDs in the suite and its invoked descendants.
`child_available` shows that the child's own call IDs survive
removing the child declaration ID because those declarations were
emitted earlier. Removing a present ID strictly reduces the
available list's length. The proof applies the same suite theorem
under that smaller list to the child body and follows the
caller tail structurally under the original list. This covers a
finite chain of these calls at any depth.

In Lean and pinned Go, a factory calls a relay through an immediate
alias, and the relay calls a leaf through another immediate alias.
The leaf uses a saved default and reads the original forwarded
index cell. Both callers consume their call results in later
assignments and returns. The inner operand and arity failures stop
before the leaf body. A reached index error inside the leaf stops
both callers before they assign their destinations. Lean checks the
forwarded addresses, retained allocations, unassigned destinations
and restored caller state.

The immediate-copy rule covers the existing lexical, integer,
index and singleton-list positional operands. The suite profile
below removes the syntactic adjacency requirement for owned
locals.
[Suite rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/forwarded-default/check.go)

### Live local closure provenance

`Call.Suite.Provenance.Elaborates` admits calls through owned names
across intervening definitions, lexical assignments and other
checked calls. At activation the provenance map is empty. A
reached definition records its emitted declaration at the target
name. An owned-name copy transfers the source's current witness.
An ordinary assignment or successful call result clears the
destination. Distinct owned slots make rebinding one name
independent of values copied to other slots. The live invariant
connects each tracked name to its reached binding cell, the
closure at the stored address, its saved defaults and its live
capture cells.

At invocation the proof reads that local and dispatches using its
actual closure record. Explicit positional and named operands run
in source order and the binder runs before activation. The callee suite starts
with its own empty map under the reduced available declaration
set. `entry_guard` derives availability from stable table lookup
at ordinary function entry. Each child's earlier-emitted IDs
survive removing its own ID, and the remaining declaration list
strictly decreases. The assignment and the tail run after a
successful restoration of the caller. Failure preserves the first
reached error and exact heap while skipping the destination and
tail.

Lean and pinned Go check a transitive copy across an allocation
and a second definition. The copy uses the original default and
captured index after the original name is rebound and the
intermediate alias overwritten. Calling the rebound name instead
uses the replacement declaration and its required parameter.
A reached operand error takes precedence over its binder. Lean
also checks the earlier return, retained allocations and restored
caller on failure.

Callable provenance from parameters, captures, module names, heap
reads or returned values, calls through untracked values, other
expression positions, untracked dispatch, loads and text parsing
remain outside the suite profile. The load-free module theorem below
connects this suite to publication.
[Provenance rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/Checks.lean) · [Pinned Go comparison](../../scripts/starlark/forwarded-default/check.go)

### Explicit named arguments at tracked local calls

The checked invocation accepts distinct explicit names and
binds required and defaulted parameters by their declared names. Normalized
source places all positional operands before the named operands.
The independent rules read the reached local callee, evaluate those
operands once in order and partition the resulting values by the
resolved positional count and keyword names. The reached closure
record supplies the declaration, saved values and live capture
cells. Its body runs under the existing declaration guard.

For a signature without a positional collector, the independent
binder checks positional overflow before delivering keyword values
to formal slots in source order. A parameter already filled by another
operand ends delivery. An unknown name also ends delivery when the
signature has no keyword collector. Saved defaults fill the remaining
slots and the binder then reports missing required parameters in
declaration order. Agreement with `bindArguments` is exact for the
admitted signatures. Binding failure allocates no activation. A
reached operand failure takes precedence over any binding failure
and preserves earlier allocations.

Repeated names in the explicit syntax fail validation even when an
operand would fail at runtime. Supplying an ordinary parameter
positionally and by name instead reaches the runtime conflict check
after evaluating all operands. Lean and pinned Go cover mixed
success with a saved default and a named override, the first unknown
name or conflict, positional arity precedence and a stopped operand
sequence. Lean also checks the exact allocation order, unassigned
destination and restored caller.

Pinned Go has a separate nullary diagnostic for supplied arguments.
When a call supplies only keywords to a zero-parameter function,
the Lean binder reports the unexpected name. Both reject before
running the body. The Go comparison uses valid identifiers and
stays within Go's per-kind explicit operand count limits. The checked
positional spread profile is described below. Arbitrary dispatch and
module publication remain separate.
[Named rules and theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Pinned spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions) · [Go validation](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L737-L798) · [Go binding](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1384-L1512)

### Keyword-only parameters in checked local suites

A checked nested definition can declare ordinary parameters followed
by a bare-star keyword-only suffix. The independent header derivation
records the suffix's required and defaulted formals in declaration
order. The normalized source signature represents the bare star by
its keyword-only field and absence of a variadic slot. Elaboration
emits the same ordered parameter slots, defining-scope reads and
default expressions as the resolver. A reached definition evaluates
the positional defaults, then the keyword-only defaults. It installs
the function and its saved values after all defaults succeed. An
earlier allocation survives a default error and later defaults are
skipped.

The tracked-local invocation still comes from the reached closure
record and uses the reduced declaration guard. Only positional
formals count toward positional capacity. Named operands can bind
either class of formal, and the binder fills remaining slots from
the saved defaults before checking for missing required arguments.
Lean and pinned Go cover mixed success with a required keyword-only
actual, an explicit override and an omitted default. They also
cover omission of the required keyword-only parameter, excess
positional arguments despite spare keyword-only slots, and the
order and first failure of definition-time defaults. The exact
Lean correspondence retains the reached heap, restores the caller
and leaves the call destination and tail unexecuted after failure.

The pinned prose and existing Lean validator require at least one
defaulted formal after bare `*`. Pinned Go also accepts a suffix
consisting only of required formals. This extension keeps the
existing checked validation rule. The nullary call diagnostic
difference is tracked separately above. The tracked suite also supports
named positional collection as described below.
[Recursive header theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Thms.lean) · [Binder and call theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Pinned function-definition spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions) · [Go resolver](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L819-L899) · [Pinned Go controls](../../scripts/starlark/forwarded-default/check.go)

### Named positional collection in checked local suites

A checked nested definition may declare a named `*args` collector and
trailing required or defaulted keyword-only parameters. The independent
header names the collector slot after the ordinary parameter slots in
the resolved frame. The collector contributes no default expression.
Elaboration preserves the default order across the star boundary and
lexical default evaluation saves each value at its formal key.

The independent binder records surplus positional values in source
order. It finishes keyword delivery, fills omitted defaults and checks
required parameters before packing. Successful packing allocates the
ordinary tuple and supplies its address to the collector slot before
activation. The tuple retains the original element values and addresses.
The empty tuple has the existing canonical key and a fresh heap cell.
An operand or binding failure leaves the reached heap without a packed
tuple. A body failure retains the tuple and any body effects. The same
guarded suite theorem restores the caller and skips the destination and
continuation on failure.

Lean and pinned Go cover an empty and a nonempty surplus, an aliased
list element, a live lexical capture, a child with no lexical captures,
and required keyword-only parameters after named `*args`. They also
cover omitted binding, a reached operand failure and a reached body
failure. Lean checks ordered retained allocations, the empty tuple key,
the exact packed contents and restored caller state. The requirements
and Go differences for bare `*` and nullary calls remain as documented
above. Keyword collection composes with this profile as described below.
[Binder and packing theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/VarargsChecks.lean) · [Pinned spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions) · [Go binding](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1384-L1512) · [Go controls](../../scripts/starlark/forwarded-default/check.go)

### Terminal keyword collection in checked local suites

A checked nested definition can declare terminal `**kwargs` with or
without named `*args`. The independent header emits the keyword
collector at the final parameter slot, after all ordinary slots and any
positional collector. Definition-time defaults keep their existing order
and scope.

The independent binder first delivers explicit names to matching
ordinary positional or keyword-only formals and rejects a second value
for an already supplied formal. It records unmatched names and values
in encounter order, fills omitted ordinary formals with saved defaults,
and checks required formals before packing. The exact surplus theorem
identifies the unmatched subsequence of the explicit operands, including
the original references. On success the keyword collector receives a
fresh unfrozen dictionary, including when that subsequence is empty.
When both collectors exist, the tuple is allocated first and the
dictionary occupies the next address.

The guarded suite theorem agrees exactly with resolved execution and
denotation. Operand and binding errors leave the reached state before
packing. A reached body error retains both packs and earlier body
effects, restores the caller, and skips the destination and suite tail.
The Lean controls check those states and the resolved collector slot.
Pinned Go checks ordered dictionary items, aliased values, distinct
empty dictionaries, saved defaults and an explicit override with
`*args`, and errors before the continuation. Repeated explicit names
are rejected statically, including when they would be unmatched. A
positional and named actual for the same ordinary parameter conflict
at runtime, before a missing-formal error.

Pinned Go creates its private collector objects during binding, with
the dictionary first when both are present. The Lean heap commits the
tuple and dictionary only after successful binding. The differential
checks compare visible results and errors. Allocation order and the
absence of packs in the residual Lean heap are properties of the Lean
model. The earlier bare-star and nullary diagnostic differences still
apply. The checked positional and mapping call-site spreads below
compose with this binder. Arbitrary dispatch and module publication
remain outside this checked suite theorem.
[Binder and packing theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/KwargsChecks.lean) · [Pinned spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions) · [Pinned Go binder](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1418-L1512) · [Go controls](../../scripts/starlark/forwarded-default/check.go)

### Terminal positional spread in checked local suites

A tracked-local call assignment can supply a single `*` operand
after all explicit positional and named arguments. The normalized
shape has one optional positional spread field. It admits direct
list and tuple displays of checked body operands, including reads of
live references, and an integer literal as a noniterable control.
The pinned prose and Go resolver require the same placement, reject
a second positional spread, and reject explicit arguments after it.

The independent argument rules derive the callee read, ordered
explicit operands and reached terminal operand before binding.
The display evaluates its elements left to right and allocates the
ordinary list or tuple. Expansion then reads its exact element
sequence with the original references and appends that sequence to
the explicit positional prefix. It adds no heap cell. The existing
binder delivers fixed positional and named arguments, saved defaults
and `*args` from those actuals. Lean proves agreement with resolved
execution and denotation, including the retained heap and restored
caller in the same guarded suite.

A reached operand error skips the rest of the operand phase. Once
all operands and any mapping key validation succeed, a noniterable
positional spread fails before binding or packing, even if those
arguments would conflict. A binding error
after successful expansion retains the allocated display and prior
effects. These errors skip the destination and suite tail. Pinned
Go controls check order, alias identity, saved defaults, positional
and variadic delivery, and error precedence. The exact layout and
residual private heap are Lean observations.

An arbitrary spread expression yielding a list or tuple needs
evidence of its reached carrier kind to enter this proof. Other
iterable carriers, general dispatch and module publication remain
separate.
[Call theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/SpreadChecks.lean) · [Pinned spec](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions) · [Go resolver](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L737-L798) · [Go compiler](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1650-L1727) · [Go call instruction](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L298-L380) · [Differential controls](../../scripts/starlark/forwarded-default/check.go)

### Terminal mapping spread in checked local suites

The normalized call has one optional `**` field after explicit
positional and named arguments and any positional `*` field. The
pinned prose describes argument evaluation in source order and dynamic
errors for explicit names repeated by a mapping. The pinned Go resolver
requires this terminal placement and rejects a repeated `**` field.
The checked mapping operand is a direct dictionary display of checked
body operands and string literals.

The dictionary display allocates its own cell, then evaluates each key
and value from left to right and checks that pair before the next. A
reached operand or display error stops the call before expansion.
After every operand succeeds, expansion reads the mapping entries in
insertion order and validates that every key is a string. It keeps the
original value references and appends the resulting pairs after
explicit names. Mapping validation precedes positional expansion,
even though the positional spread operand evaluates first.

The ordinary binder runs after both expansions. It checks fixed-slot
and collector conflicts, including duplicates between explicit names
and spread entries. A duplicate dictionary display key fails earlier,
during display insertion. The source, resolved operational and
denotational paths agree on the exact error and retained heap. A
binding error keeps the display but skips both collectors and the
callee. A body error retains the display, reached packs and earlier
body effects, restores the caller, and skips the destination and tail.

The pinned Go comparisons cover empty and ordered mappings, alias
identity, fixed and collected delivery, and reached error precedence
with both spreads. Go's duplicate-display instruction checks uniqueness
after setting the entry in its private temporary. Lean rejects without
replacing the accepted prefix. The differential checks compare visible
errors and effects, while the Lean checks inspect that private prefix and
the exact retained state. Arbitrary carrier expressions and untracked
dispatch remain separate. The module theorem below uses the same
argument rules for reached global aliases.
[Call and mapping theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Named/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/MappingChecks.lean) · [Pinned prose](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions) · [Go resolver](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L737-L798) · [Go call instruction](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L298-L380) · [Go dictionary insertion](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L469-L487) · [Differential controls](../../scripts/starlark/forwarded-default/check.go)

### Checked source calls through module publication

The checked load-free plan composes source definition, assignment,
closure copy and call assignment across an arbitrary finite command
sequence in this profile. Its global declarations come from the source
binder order. Each root is linked to the declaration index following
its checked recursive suite's emissions. Later definitions preserve
the earlier table entries.

At module entry, the proof derives the global cells and their distinct
addresses. At a reached definition it selects the module captures
from those live cells, evaluates defaults in the defining frame, and
keeps the saved values and captured addresses in the installed closure
record. The invariant relates each tracked global or explicit alias to
its actual reached record. Calls through that invariant use the same
lexical read, argument, binder, collector and guarded activation rules
as local calls. A write may update a captured binding while preserving
its address.

`module_agrees` derives the independent source command trace and the
same resolved operational trace. The existing exact initialization
result then gives ordered public exports and the reachable frozen heap,
or the first reached error with the exact retained heap and restored
caller. The proof begins at actual module entry and uses the checked
normalized resolver. The premises contain independent source plans and
checked resolution. They require no reached closure, frame, binder or
body-execution witnesses.

The Lean and pinned Go checks publish a capturing function and its
alias after a call using named arguments and both spreads. The captured
global is initialized after the function is defined. The checks also
distinguish a duplicate binding before packing from an error in the
body after packing. Lean observes the captured global slot and exact
residual allocations. Publication freezes the reachable values and
leaves the module binding cell itself outside closure-local freezing.

[Module theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/Checks.lean) · [Pinned Go controls](../../scripts/starlark/published-checked/check.go)

## Callable returns through module publication

A checked suite can certify a terminal return of a tracked local. The
same suite induction derives the value from its reached slot and the
closure record from its reached heap. A separate source-order argument
links the returned declaration and its independently checked body to
the final table. Definitions and local copies establish the tracking
evidence. Rebinding a destination updates or clears its entry.

The module plan can store the resulting callable, copy it to another
global and call it with explicit arguments and both checked spreads.
Caller restoration keeps the reached heap. The closure retains the
addresses of its enclosing and defining-module cells and the values
saved at definition time. When initialization succeeds, the theorem
relates each tracked public export to its linked declaration and its
original closure record in the frozen heap. The first reached error
retains the exact residual heap and restores the caller without
publishing the module.

Lean and pinned Go controls cover a factory that copies its child and
returns the copy. The child saves an enclosing local as a default,
observes that local's later rebinding and reads a global initialized
after the factory call. A call through a module alias reaches both
spreads. An alternate mapping entry makes indexing fail after the
child's first allocation. Lean checks the retained packs and
allocations, restored caller, and skipped result assignment and tail.
Go checks visible effects, saved and live values, and the publication
freeze.

The checked profile still starts from a load-free normalized module.
Only a terminal return of a tracked local transfers callable
provenance, and the returned declaration's body uses the existing suite
profile. The [checked import profile](#checked-callable-imports) carries an
escaped closure through a single producer-to-consumer load. General
carriers, untracked dispatch and broader command and body forms remain
open.
[Return theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Defaults/Nested/Sequence/Recursive/Call/Suite/Provenance/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/ReturnChecks.lean) · [Pinned Go controls](../../scripts/starlark/escaped-checked/check.go)

## Checked callable imports

The checked graph has a load-free normalized producer and one
normalized consumer. The consumer renames a single public import and
executes a finite suite of ordinary name assignments and calls through
tracked names. The producer emits the shared declaration table. The
consumer's checked elaboration preserves that table and derives its
imported slot and ordered module globals from the source commands.

Cold loading derives publication from the producer's independent
source trace. The producer restores the consumer's frame and retains
the original cell contents, with freezing allowed to update cell flags.
The import binds the actual exported function address. The warm
theorem first derives the producer load and cache entry, then transports
the same record through allocation of the consumer's frame.

The suite invariant relates each tracked name to the closure stored in
its reached file-local or global slot. A name copy transfers the
closure's link, and a checked call updates its destination using the
actual return and reached heap. Successive calls use the closure's
original defining environment, captured addresses and saved defaults.
The reusable suite theorem retains the invariant at the end of a
successful suite and stops at the first reached error.

The independent source rules and loader denotation agree on exact
exports, heap, cache and errors. A missing export stops before any
consumer work. A later call error retains the earlier calls and writes,
as well as the producer publication, and skips consumer publication.
The Lean and pinned Go controls call an imported factory through an
alias, copy the new child and call it with named arguments and both
spreads. The returned function and the child result are distinct
observations. The child shares the producer's global cell with an
earlier closure and owns a different captured local. A second-call
error leaves the earlier factory and ordinary assignment effects.

The same suite admits any finite number of consumer definitions whose return
calls the file-local import. Elaboration appends
each declaration at the current table size, in source order, and retains
every earlier lookup. The reached-prefix proof carries the extended table
and live provenance across definitions, copies, assignments and calls.
Installing a wrapper captures the actual import cell. Every subsequent
invocation reads that cell, and the reduced call guard retains the
producer's declaration IDs. A tracked closure returned through the wrapper
keeps its address and defining record when the caller frame is restored.
The operands support the existing explicit named arguments and checked
tuple/list and dict-display spreads.

The cold and preloaded source rules agree with loader denotation on
publication and freezing, first error, residual heap, caller restoration
and cache. The two-definition control calls an alias copied before the
second definition, then calls the second wrapper with an explicit default
override. A failing override retains the first result and skips the final
assignment. Another control invokes a fresh producer closure returned
through the consumer wrapper.

The UTF-8 adapter compiles normalized modules in manifest order and feeds
the final linked table to the loader. The source theorem starts at
normalized commands. The checked wrapper header admits required and
defaulted positional parameters, a named positional collector, and
required and defaulted keyword-only formals. Defaults use the existing
lexical operand profile of reads, integer literals, singleton list
allocation and indexing. Definition-time calls, keyword collectors and
broader wrapper bodies remain separate.
[Suite theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/Imports/Thms.lean) · [Lean controls](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/ReturnChecks.lean) · [Pinned Go controls](../../scripts/starlark/imported-checked/check.go)

### Composing checked imports

A topologically numbered graph may contain checked load-free roots and
consumers with an ordered list of leading loads. Each consumer supplies its
normalized suite and checked link into the common declaration table.
The prefix induction reads each dependency's actual publication once per load
command. The independent selection rules derive the ordered exported function
addresses from that publication. Only full selection enables the separate
installation proof, which fills distinct file-local alias cells. The suite
inherits the reached importer frame and live provenance for all aliases.
The singleton edge theorem remains available.

The graph theorem follows strictly earlier dependencies. It preserves
earlier cache entries, the original closure records and their capture
addresses, and the caller's slots, bindings and iterator context. A missing
label, reached dependency failure or missing export skips all later loads and
the suite. The independent source trace agrees with the loader on exact
publication and heap, or on the first reached error and residual session.
Requests from an empty cache establish the same invariant for later mixed
cold and cached loads.

The graph transports regular closures, factory results, and exported
consumer wrappers. Recursive wrapper provenance follows the actual published
function address through its captured file-local cell to the imported closure
in the same heap. Each wrapper's declaration index is strictly greater than
its captured callee's index. Removing the active wrapper leaves the lower
declaration range required by the next activation. Validation makes load
aliases and global destinations distinct. The importer fills blank cells,
preserving initialized captures and function records across cache reuse.

The three-module controls exercise direct and nested calls through a published
wrapper. A diamond control shares one producer between two separately linked
wrappers. It runs from an empty cache and after an actual request for the left
branch. A downstream wrapper invokes the second alias of a grouped load under
the same declaration-index guard. A missing first or last export retains both
dependency publications and the earlier load's alias while leaving both alias
cells in the failed load, later load cells and body cells blank. With both
exports missing, the controls check that the rightmost one is reported. The
pinned Go checks observe the error, loader calls, cache hits and public effect
order. Lean additionally checks the residual file-local cells and restored
caller. Go's public initialization result does not expose the file-local cells.

The checked prefix admits a nonempty group of public callable imports per load.
Its static missing-export evidence requires the name to be outside the
dependency's declared globals. Grouped syntax already lowers through the normal
frontend load adapter. The positional wrapper uses the ordinary binder to
deliver values to its own formals in header order. Its body reads operands in
the order written at the inner call. Formal names stay distinct from the
captured alias, preserving the original import cell and lower declaration
index. Arguments supply no callable provenance.

During initialization, positional defaults evaluate left to right in the
reached defining frame. The wrapper records the resulting values, including
addresses of allocated lists, before binding its name. Publication freezes
reachable values and preserves those addresses. A later call or cache hit
uses the saved record. Explicit arguments take precedence through the ordinary
binder. A reached default error retains earlier effects and skips installation,
the remaining defaults and commands, and importer publication.

The three-module controls check a wrapper calling the second import of a
grouped load. They cover ordered forwarding, omitted defaults, explicit
overrides followed by another omission, missing and surplus arguments, and a
failure after an earlier default allocates. Lean checks the retained cells,
restored caller and cache; pinned Go checks the outcomes, call order,
saved default identity and visible pre-error bindings. The controls run
cold and after actual preloads. They preload the producer when the wrapper
definition itself fails.

For keyword-only wrappers, positional capacity comes from the positional
prefix. Named operands can supply required formals or override saved
defaults. The binder uses the reached closure record and installs its
original capture vector on success. Repeated explicit names fail during
validation. An unknown name or a positional-and-named conflict reaches
binding only after all operands succeed. A reached operand error keeps
earlier effects and preempts binding and subsequent operands.

Cold and wrapper-preloaded controls check a required keyword-only name and
a list-valued keyword default. They cover both kinds of duplicate, unknown
and missing names, positional overflow, and a later operand error that
preempts an unknown-name error. Go instruments reached operands to observe
their order. Lean checks the exact retained allocations and restored caller
state. The wrapper proof starts at normalized keyword-only headers. The
frontend guide tracks which headers and call arguments the UTF-8 adapter accepts.
[Frontend coverage](starlark-frontend.md) · [Pinned compiler](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1223-L1237) · [Pinned interpreter](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L580-L617)

With named `*args`, the ordinary binder assigns the positional prefix to
ordinary parameters and places the remaining values in encounter order in
the collector tuple, preserving their references. Successful preparation
allocates the tuple at a fresh address, including a tuple with the canonical
empty key when there is no surplus. Activation uses the reached closure's
original captures and saved defaults. The declaration-index guard and loader
agreement apply to the same normalized wrapper suite. Cold and wrapper-preloaded
controls check an empty collector, an ordered nonempty collector with a list
alias, keyword override and omission, binding failures and a later operand
error. The Lean controls check cache reuse, caller restoration and the
retained heap, including the absence of a new tuple on binding failure.
Pinned Go constructs its private tuple during binding before keyword
validation. Failed binding exposes no tuple through the Go API, so the Go
controls compare observable outcomes and reached operand effects.
[Wrapper preparation theorem](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/Imports/Thms.lean) · [Pinned Go binder](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1430-L1499)

The normalized collector header is exercised directly in Lean. The UTF-8
frontend currently reports an unsupported parameter header for `*rest`.
Arbitrary incoming caches, calls in defaults, `**kwargs` collectors,
untracked exports and calls through parameter values remain outside the
checked wrapper profile.

[Chain theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Trace/Published/Imports/Chain/Thms.lean)

## Finite-manifest loader

`Loader.load` takes a known module ID and an optional session. A session
keeps the shared runtime and the cache for one fixed manifest and linked
declaration table. Manifest array indices are canonical IDs. Each entry
provides its own label table, queried when that module executes a load.
Distinct labels that resolve to the same ID share one successful
initialization and the published values retain their heap identities.
The table uses the first matching label when entries repeat.
The linked declaration table is supplied up front and its signatures and
bodies are checked by the shared module validator. Each source's own
commands, allocations and publication are processed on demand.
[Loader definitions](../../Silmaril/Languages/Starlark/Modules/Loader/Defs.lean)

- A missing label reports the requester and label. An ID outside the
  manifest reports an unknown module when it is requested.
- A cycle reports the current path from the root through the repeated
  ID. The path is local to the request and is discarded when it ends.
- Validation and runtime errors carry the ID of the failing module.
  A missing export is a failure of the importing command. Failure stops
  the remaining commands and propagates to every waiting importer.
- Failed modules leave no cache entry and perform no publication freeze.
  Prior heap effects and successfully published dependencies survive,
  so a later request can retry the failure and reuse those dependencies.
  Callers recover their lexical and iterator state at each module exit.

`runs_iff_denote` proves exact agreement with independent rules on the
result, error, heap and cache. Descent counts inactive manifest IDs and
pending commands, so the loader needs no fuel. A fresh Starlark thread
and publication freeze use the same primitives as `initializeModule`.
Canonical resolution, successful-publication caching and cycle rejection
are policies of this host model. Filesystem I/O, concurrency, custom host
thread state, failure caching and backtraces remain open.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Loader/Thms.lean) · [Load statements][loading] · [Module execution][modules]

The Go loader fixture supplies the same host policy through `Thread.Load`.
It uses `Program.Init` and freezes globals only on success. This lets it
compare dependency order, aliases and failure effects in the pinned
engine. The cycle and cache policy come from the fixture's host, and the
Go convenience wrapper freezes a partial mapping even on failure.
[Lean loader fixtures](../../Silmaril/Languages/Starlark/Modules/Loader/Checks.lean) · [Go loader fixtures](../../examples/starlark/loader/check.go)

The Lean fixtures cover cross-module captures, private freezing, file-local
aliases, validation, missing exports and failure restoration. The native
fixtures check source order, skipped branches, absent assignment after an
effectful error, and the freeze of exported aliases, their nested values and
reachable function defaults. The pinned Go fixtures compare successful
publication through `ExecFileOptions` and observe failure effects through
`Program.Init`. Go's convenience wrapper also freezes the partial global
mapping on error. The Lean failure and loader fixtures check the shared
heap and absence of publication on failure under the pinned prose policy.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Checks.lean) · [Native fixtures](../../Silmaril/Languages/Starlark/Modules/ExpressionChecks.lean) · [Go fixtures](../../examples/starlark/modules/check.go) · [Pinned starlark-go][go]

```sh
lake build --wfail +Silmaril.Languages.Starlark.Modules.Checks \
  +Silmaril.Languages.Starlark.Modules.ExpressionChecks \
  +Silmaril.Languages.Starlark.Modules.Loader.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.LoopChecks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
mixed_leaf="$(pwd)/scripts/starlark/mixed-leaf.go"
multi_callee="$(pwd)/scripts/starlark/multi-callee/check.go"
defaults="$(pwd)/scripts/starlark/positional-defaults/check.go"
default_trace="$(pwd)/scripts/starlark/default-call-trace/check.go"
escaping_defaults="$(pwd)/scripts/starlark/escaping-defaults/check.go"
defaulted_body="$(pwd)/scripts/starlark/defaulted-body/check.go"
nested_default_body="$(pwd)/scripts/starlark/nested-default-body/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/modules/check.go" && go run "$fixtures/loader/check.go" &&
  go run "$fixtures/scope/check.go" && go run "$mixed_leaf" && go run "$multi_callee" &&
  go run "$defaults" && go run "$default_trace" && go run "$escaping_defaults" &&
  go run "$defaulted_body" && go run "$nested_default_body")
```

[default-parameters]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[expressions]: starlark-functions.md#direct-denotation-of-resolved-expressions
[source-expressions]: starlark-functions.md#resolving-a-normalized-expression
[subscript-assignment]: starlark-functions.md#simple-subscript-assignment
[pattern-assignment]: starlark-functions.md#standalone-pattern-assignment
[augmented-subscript]: starlark-functions.md#integer-augmented-subscript-assignment
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[loops]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
