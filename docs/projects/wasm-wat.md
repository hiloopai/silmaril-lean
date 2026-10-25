# WAT quotations in Lean

Import `Silmaril.Wasm.Wat` to write WebAssembly text directly in a Lean program.
The quotations parse text and resolve names during elaboration, producing
ordinary Lean syntax trees. Lime 1 is a smaller scalar Wasm model.

| Model | Module | Instruction list |
| --- | --- | --- |
| Wasm 1.0 | `wat1!` | `wat1_expr!` |
| Lime 1 | `watLime!` | `watLime_expr!` |
| Core 3.0 | `wat3!` | `wat3_expr!` |

```lean
import Silmaril.Wasm.Wat

open Silmaril.Wasm

def add : Module := wat3! r#"
(module
  (func $add (export "add")
    (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $x) (local.get $y))))
"#

example : add.funcs.length = 1 := rfl

def vector : Expr := wat3_expr! "v128.const i32x4 1 2 3 4"
```

The generated terms can be used with the existing validation and execution
judgments. [Examples](../../Silmaril/Wasm/Wat/Examples.lean) prove validation and
execution of a quoted addition function for arbitrary arguments.

## Syntax and checks

Core 3.0 quotations support recursive types, references and GC operations,
exceptions, typed and tail calls, multiple memories and tables, memory64/table64,
SIMD and relaxed SIMD. Wasm 1.0 and Lime 1 retain their scalar profiles.

The frontends share lexical rules, name resolution, signature parsing, scalar
operators and folded/flat control traversal. Standalone expressions accept
numeric references and local block labels. Expressions that need an implicit
module type table belong inside a module quotation.

Parsing checks immediate widths, symbolic references and supplied signatures.
Stack typing, numeric index bounds and execution preconditions are checked by
the separate validation and execution APIs. Lean checks the generated AST terms
and proofs; text-to-AST correctness remains a separate proof obligation.

## Entry points

- [Quotations](../../Silmaril/Wasm/Wat.lean)
- [Core module examples](../../Silmaril/Wasm/Wat/CoreModuleExamples.lean)
- [Instruction coverage checks](../../Silmaril/Wasm/Wat/CoreInventory.lean)
- [Diagnostics](../../Silmaril/Wasm/Wat/Diagnostics.lean) and
  [Core diagnostics](../../Silmaril/Wasm/Wat/CoreModuleDiagnostics.lean)
- [Literal boundary tests](../../Silmaril/Wasm/Wat/FloatTests.lean)

`make library` checks the quotation frontends and all included examples.
