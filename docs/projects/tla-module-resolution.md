# TLA+ module resolution

Import `Silmaril.Logic.Temporal.TLA.Resolution.Defs`. Pass `resolve` a registry
and the root’s `ModuleId`. On success, its `CheckedRegistry` contains the root
and each dependency reached by `EXTENDS`. The result checks declaration order,
scope and arity in the supported Surface fragment. Bindings carry signatures
independently of levels, value carriers and operator interpretation.

[Resolver interface](../../Silmaril/Logic/Temporal/TLA/Resolution/Defs.lean) ·
[Names and registry inputs](../../Silmaril/Logic/Temporal/TLA/Resolution/Names.lean)

## Registry and scope

- A `.parsed` registry entry supplies a `Surface.Module` and an explicit
  mapping from each used `EXTENDS` spelling to a caller-selected module ID.
  Each referenced ID must identify an entry with the matching header. A registry
  may select different same-named modules in different caller contexts.
  The caller owns lookup, provenance and any required file or digest checks.
- A `.signature` entry supplies the module name, ordered import edges, and
  signatures of its own public declarations. Supply inherited signatures as
  edges to the original registry entries. Signature entries attest only to
  declarations and arity. Their `CheckedModule.source` is empty.
- Each import includes its transitive public bindings. Two paths to the same
  binding ID introduce a single binding, including repeated identical
  `EXTENDS` entries. A shared canonical name with distinct declaration IDs
  reports both origins. This implements the language rule in §17.5.1. Pinned
  SANY can instead accept a same-class conflict with a warning. Cycles report the
  identity chain and the edge that closes it.
- Units and LET definitions are checked in source order, including unused
  bodies. Definition formals and rigid binders require fresh names in the
  visible scope. A new operator becomes visible after its body, which sees only
  the incoming scope and its formals. The LET body sees all its definitions.
  LET names can be reused after the frame closes. A LOCAL definition is visible
  within its own module. An imported public operator keeps references to its
  home module’s private helpers.
- Each binding has ordered expression or operator slots. The latter expect a
  first-order operator of exactly the indicated arity. Bare named arguments are
  classified using this expected slot. Matching named, symbolic and lambda
  arguments are supported. Function constructors, rigid quantifiers and set
  binders check all domains before adding the bound names. Function indexing
  visits the function and the index expressions. Lexical arity belongs to
  operator application.

[Specifying Systems, §§16.1 and 17.1–17.5](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=335) ·
[TLA+2 preliminary guide, §3](https://lamport.azurewebsites.net/tla/tla2-guide.pdf) ·
[Pinned SANY symbol merge](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Context.java#L370)

Named built-ins in this fragment come from the pinned SANY built-in table.
Arithmetic and other library operators enter through explicit registry edges.
For example, a signature for `Naturals` can declare `+` as
`.operator (.symbol .infix "+") [.expression, .expression]`. Canonical symbol
keys reuse the parser’s synonym table and retain fixity. Names are
case-sensitive.

[Pinned SANY built-ins](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/BuiltInOperators.java#L80)

## Evaluator and level-checker handoff

Use `CheckedModule.source` for the original Surface syntax and
`CheckedModule.referenceAt path` at each operator occurrence. The returned
`Reference.target` can be looked up with `CheckedRegistry.findBinding`.
A declared ID has the owning module ID and the declaration path. Built-ins
have their own IDs. Resolve imported definition bodies against the checked
module of their declaration, using its reference table and source. This also
gives access to any LOCAL helpers. `CheckedModule.bindingAt` looks up a name
in the final module scope, and `exports` gives the externally visible bindings.

An application and a named or symbolic operator actual have distinct reference
roles. A lambda remains source syntax with formal IDs at the corresponding
parameter paths. Store evaluator environments and level summaries by
`BindingId`. For signature-only modules, use the same IDs to attach external
implementations or level summaries. The resolver records the built-in prime
and its operand uses, including a second prime, so a later pass can enforce
the operand-level bound and assign action level.

Paths index the unchanged Surface tree. Each index is zero-based. For example,
`[.unit 2, .body, .argument 0]` points at the first parenthesized argument in
the body of the third unit when that body is a reference. The other path
conventions are as follows.

| Syntax | Path from the enclosing site |
| --- | --- |
| Module imports and units | `.import_ i` and `.unit i` |
| VARIABLE/CONSTANT or signature entries | `.member i` |
| Operator definition | The unit or `.letDecl i` is the declaration site, with `.parameter i` for its formals and `.body` for its expression |
| Named call, symbolic application | Reference at the call’s own site, with `.argument i` for parenthesized arguments and `.operand i` for fixity operands |
| Lambda | The argument site, with `.parameter i` and `.body` beneath it |
| LET | `.letDecl i` for definitions and `.body` for the IN expression |
| Bounded groups in quantifiers, set maps and function constructors | `.bound i, .domain` and `.bound i, .binder j`, with `.body` for the expression |
| Unbounded quantifiers, CHOOSE and set filters | `.binder i`, `.domain` when present, and `.body` |
| CASE and records | `.arm i, .operand 0` for a CASE condition, `.arm i, .operand 1` for its value, `.other` for OTHER, and `.field i` for a record entry’s value |
| EXCEPT | `.operand 0` for the base, `.update i` for the clause binding, `.update i, .body` for the right-hand side, and `.update i, .updateComponent j, .argument k` for an index argument |
| Other child expressions | `.operand i` in Surface order, with the function at `.operand 0` in an index expression |

This preserves literals, fields, binder grouping, formal declarations and
operator spellings as represented by Surface, along with the original
expression and unit structure. Paths and declared IDs are specific to a given
tree and registry. Diagnostics use module and path coordinates because Surface
does not store byte spans. An `@` occurrence is a reference to its enclosing
clause's `.oldValue` binding. The base and selectors of a nested EXCEPT see
the surrounding binding. Each right-hand side introduces its own binding.
See [the ACP_SB handoff](tla-acp-sb-resolution.md) for the level rules.

## Boundaries and checks

In the core profile, INSTANCE and WITH, selectors, submodules, RECURSIVE,
proof-step references, labels, temporal syntax and other action syntax, and
function-definition units such as `F[x \in S] == e` return explicit unsupported
diagnostics. Anonymous function constructors such as `[x \in S |-> e]` are
name-checked. ASSUME, THEOREM and proof directives are also rejected at this
boundary. Level constraints, instantiation substitutions, proof obligations and
proof verification require later passes. Collection shapes carry no checks
about element values, function domains or record meanings.

The opt-in `namedFunctionSyntax` profile resolves local function declarations
with one identifier in one bounded group. The local name is visible in its
own body and to subsequent LET declarations and IN. The index is visible in
its own body. Both bindings use declaration sites, and the domain is
resolved in the preceding scope. The `namedFunctionInstanceSyntax` profile
also enables the existing INSTANCE syntax and its checks.
[Named predecessor source profile](tla-named-functions.md#source-profile)

### Selecting a root operator

`resolveOperatorWith` takes a root unit index. The checked module keeps the
complete parsed tree and records the selected index in `selectedUnit`. Its
scope includes imports, the preceding variable and constant declarations,
the names of preceding ordinary operators and named instances, and the
selected operator. Earlier operator bodies and named instance members are
unavailable to level checking. An anonymous INSTANCE can introduce
unqualified bindings, so encountering one before the selection fails.
Anonymous assumptions and theorems introduce no names. All dependency
modules reached by checked edges still pass normal registry resolution.

`Levels.checkSelectedOperator` checks that operator and the resolved
dependencies. A reference to a skipped body fails for lack of a level summary.
`Levels.check` requires full resolution. The WriteThroughCache gate uses the
original coordinates and checks the imported declaration identities before
certifying the selected state expression.
[WriteThroughCache gate](tla-named-functions.md#source-profile)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Resolution.Defs \
  +Silmaril.Logic.Temporal.TLA.Resolution.Examples
scripts/check-layout.sh
```

The example build runs the parser-to-resolver guards. They check reference and
binder identities, path uniqueness and reference targets, diamond coalescing,
LOCAL visibility, and diagnostic tags and locations. `CheckedModule.mem_exports`
states the export filter as a Lean theorem.

[Regression module](../../Silmaril/Logic/Temporal/TLA/Resolution/Examples.lean) ·
[Intact fixture pins](../../tests/semantics/tla-parser/check.py)
