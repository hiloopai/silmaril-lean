module

public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Worked examples for the every-run logic: programs

Three small Wasm 3.0 programs (as Core 3.0 instruction lists), checked in
`Silmaril.Wasm.Logic.HoareExamples.Thms`:

* `catchProg t x`: a `try_table` inside a `block` that throws the exception tag
  `x` with payload `7` and catches it (`catch x 0`), leaving `7`;
* `loopBody x`: the body of a tail-recursive function (index `x` is the function
  itself) that counts its `i32` argument down to zero by `return_call` and then
  returns `42`;
* `listProg x`: builds a two-node GC linked list of `struct` type `x`
  (`{i32, ref null x}`) with `struct.new`, and reads the value of the second node
  through the first with `struct.get`.

The examples are stated for any module instance and store in which the indices
resolve as the programs expect (the hypotheses of each theorem); building a
concrete module and instantiating it is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.HoareExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- Label index `0`. -/
def l0 : LabelIdx := ⟨0⟩

/-- Local index `0`. -/
def x0 : LocalIdx := ⟨0⟩

/-- Field indices. -/
def i0 : FieldIdx := ⟨0⟩
def i1 : FieldIdx := ⟨1⟩

/-- Throw and catch: `block (result t) (try_table (result t) (catch x 0) (i32.const 7; throw x))`. -/
def catchProg (t : ValType) (x : TagIdx) : List Instr :=
  [.block (.value t) [.tryTable (.value t) [.catch_ x l0] [.intConst .i32 7, .throw x]]]

/-- A tail-recursive count-down: `local.get 0; if (result t) (local.get 0; i32.const 1;
i32.sub; return_call x) (i32.const 42)`. -/
def loopBody (t : ValType) (x : FuncIdx) : List Instr :=
  [.localGet x0, .if_ (.value t)
    [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .returnCall x] [.intConst .i32 42]]

/-- A two-node linked list: `i32.const 1; ref.null x; struct.new x; local.set 0;
i32.const 2; local.get 0; struct.new x; struct.get x 1; struct.get x 0`. -/
def listProg (ht : HeapType) (x : TypeIdx) : List Instr :=
  [.intConst .i32 1, .refNull ht, .structNew x, .localSet x0, .intConst .i32 2, .localGet x0,
    .structNew x, .structGet none x i1, .structGet none x i0]

end Silmaril.Wasm.Logic.HoareExamples
