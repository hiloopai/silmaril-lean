module

public import Silmaril.Wasm.Cfg.Defs
public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Examples.Verified.Defs
public import Silmaril.Wasm.Examples.RustInst.Defs

@[expose] public section

/-!
# Control-flow graphs of example Wasm functions

The functions whose CFGs `Silmaril.Wasm.Cfg.Thms` checks in the kernel:

* `sum` of `Examples.Verified.prog`: a `loop` in a `block`, left by `br_if`, re-entered by `br`;
* `enter` of `Examples.RustInst.door` (compiled Rust): nested `block`s with `br_if` and `br`;
* `dispatch` (below): a `br_table` over three nested blocks with a default, so its four
  targets are known syntactically;
* `edges` (below): `unreachable`, `throw`, `return` and a branch to a label depth that does not
  exist, which go to the `trap`, `raise`, `exit` and `invalid` nodes.
-/

namespace Silmaril.Wasm.Cfg.Examples

open Silmaril.Wasm

/-- The body of a function of a module (empty when out of range). -/
def bodyOf (m : Module) (i : Nat) : Expr := ((m.funcs[i]?).map (·.body)).getD []

/-- `sum n = 1 + ⋯ + n`. -/
def sum : Expr := bodyOf Silmaril.Wasm.Examples.Verified.prog 3

/-- `enter` of the compiled Rust door (function 5; the first five functions are imports). -/
def doorEnter : Expr := bodyOf Silmaril.Wasm.Examples.RustInst.door 0

/-- A module with a `br_table` dispatcher and a function with every special edge. -/
def mod : Module := wat3! r#"
(module
  (tag $e)
  (func $dispatch (export "dispatch") (param $k i32) (result i32)
    (block $c
      (block $b
        (block $a
          (br_table $a $b $c (local.get $k)))
        (return (i32.const 10)))
      (return (i32.const 20)))
    (i32.const 30))
  (func $edges (export "edges") (param $k i32)
    (if (local.get $k) (then unreachable))
    (if (i32.eqz (local.get $k)) (then (throw $e)))
    return))
"#

/-- The dispatcher. -/
def dispatch : Expr := bodyOf mod 0

/-- The special edges. -/
def specials : Expr := bodyOf mod 1

/-- A branch to a label that does not exist (`br 5` at depth 1), built directly: no valid text
module contains one. -/
def badBranch : Expr := [.block .empty [.br ⟨5⟩]]

end Silmaril.Wasm.Cfg.Examples
