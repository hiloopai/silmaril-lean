module

public import Silmaril.Wasm.Auto2.Wat.Defs

@[expose] public section

/-!
# `wat3b!` examples

Binaryen's printing of a two-result function (`tuple.make`) and of a discarded pair
(`tuple.drop`) give the same module terms as their standard WAT, by `rfl`.
-/

namespace Silmaril.Wasm.Auto2.Wat

/-- Binaryen's printing of a function returning a pair (as in the `opt-in` corpus). -/
def pairB : Silmaril.Wasm.Module := wat3b! r#"
(module
 (type $8 (func (param i32 i64) (result i32 i64)))
 (export "f19" (func $19))
 (func $19 (type $8) (param $0 i32) (param $1 i64) (result i32 i64)
  (tuple.make 2
   (local.get $0)
   (local.get $1)
  )
 )
 (func $20 (type $8) (param $0 i32) (param $1 i64) (result i32 i64)
  (tuple.drop 2 (call $19 (local.get $0) (local.get $1)))
  (tuple.make 2 (i32.add (local.get $0) (i32.const 1)) (local.get $1))
 )
)"#

/-- The same module in standard WAT. -/
def pairS : Silmaril.Wasm.Module := wat3! r#"
(module
 (type $8 (func (param i32 i64) (result i32 i64)))
 (export "f19" (func $19))
 (func $19 (type $8) (param $0 i32) (param $1 i64) (result i32 i64)
  (local.get $0)
  (local.get $1)
 )
 (func $20 (type $8) (param $0 i32) (param $1 i64) (result i32 i64)
  (call $19 (local.get $0) (local.get $1))
  drop
  drop
  (i32.add (local.get $0) (i32.const 1))
  (local.get $1)
 )
)"#

theorem pairB_eq : pairB = pairS := rfl

end Silmaril.Wasm.Auto2.Wat
