# Intrinsic folded Binaryen fragment

The experiment uses Silmaril's actual [layer-D `BExpr`](../../Silmaril/Wasm/Binaryen/Syntax.lean)
and [lowering](../../Silmaril/Wasm/Binaryen/Lower.lean), not a new model of the
upstream C++ implementation. Layer D uses de Bruijn branch indices; the existing
named layer resolves to it. Upstream Binaryen version 133 uses named branch and
call targets and stores operands as children:
[`src/wasm.h`](https://github.com/WebAssembly/binaryen/blob/fba5005a132d85d578be5bd010e0487ed8e2ce3e/src/wasm.h#L869).

## Exact agreement

```text
Expr C result  ─── toCore ──→  Intrinsic.Body C (plain [] result.toList)
     │ erase                                  │ erase
     ▼                                        ▼
   BExpr       ─── lower ───→              List Instr
```

[`Expr`](../../Silmaril/Wasm/Binaryen/Intrinsic/Defs.lean) is an inductive tree
indexed by the Core validation context and a zero-or-one result. It supports
integer constants, `nop`, initialized `local.get`, `drop`, direct `call`,
zero-input `block`/`loop`/`if` (one expression per region), and `br_if` to an
empty label. Lookup and branch-scope premises are Core's. `Operands C ts`
contains one single-valued expression per parameter in order. In the stack
translation, the first expression pushes its result and frames the rest of the
operands under it. The call consumes exactly `ts`. Neither path claims to
cover stack-supplied children, local initialization/writes, multivalue, block
parameters, indirect/tail calls, or stack-polymorphic bottom.

[`Expr.lower_erase` and `Operands.lower_erase`](../../Silmaril/Wasm/Binaryen/Intrinsic/Thms.lean)
prove the square structurally. `Expr.sound` derives the existing `SeqOk` from
`Intrinsic.Body.sound`. The result is forward only: flattening a folded `if`
condition into sibling instructions and lifting back with `liftInstrs` gives
a different tree, as the regression proves. Core still retains the `if` and
both branch sequences. `fold` preserves lowering, not arbitrary original
tree boundaries. Upstream name recovery, block normalization and optimization
are not part of the theorem.

## Observations

`Expr.lower_in_slot` proves exact module equality with all the other
declarations held fixed. A `FunctionSlot` is a syntactic slot, not a certificate
that the supplied context matches the module's function type. The fixture
separately checks whole-module validation. The [observer theorems](../../Silmaril/Wasm/Binaryen/Intrinsic/Observations/Thms.lean)
transfer the existing `moduleObs` (instantiation and export sessions, including
trap and divergence) and `IOAccept.tagTraces` (export enter/exit and role-chosen
import call/answer tags). Both are equal because the Core programs are equal,
not because a second machine or an optimizer has been proved adequate. Exit
tags can conflate a trap or uncaught exception with a result that the role
fails to decode; `moduleObs` is a different observation.

A function-as-instruction variant can share `Body C (plain inputs outputs)`:
`Operands` supplies the input vector, and a declaration retains the function
index/signature used by `FunctionRef`. Recursive calls can keep this same
signature interface, but execution still needs a call-frame simulation or a
recursion semantics. An effectful interpretation could expose import questions
and answers at the call boundary and return Core-typed results, traps or other
outcomes; matching that interpretation to Core requires a separate proof.

## Reproduce

```sh
bash tests/wasm/binaryen-intrinsic/check.sh
BINARYEN_BIN=/path/to/binaryen-version_133/bin bash tests/wasm/binaryen-intrinsic/check.sh
```

The first command builds the proof roots with warnings as errors, checks the
typed and raw fixtures, tests rejection (missing local/label and reversed
`i32`/`i64` call operands), and checks that a valid multivalue function lies
outside the experiment. It also prints the proof axioms. The optional pinned
tool check assembles the structured WAT fixture, decodes it with the Core
decoder, validates it, and compares the types, functions, imports and exports
against the Lean fixture. The native shell checks both if paths, an
import-mediated trap, both branch outcomes, and the assembler rejects the
swapped operands.
The upstream Linux x86-64 archive is
`binaryen-version_133-x86_64-linux.tar.gz` (SHA-256
`2dc9c7813f5375db93d96ead4b78222fcc3e2677bbb832297af4797782a37489`).
This is one interoperability check, not a validation theorem for that tool.
