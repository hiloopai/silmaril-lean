module

public import Silmaril.Wasm.Wat

/-! # Core 3 module diagnostics

Malformed binding and declaration syntax is rejected during expansion. These are
frontend checks, separate from Core instruction and module validation.
-/

/-- error: WAT at character 39: type use does not name a function type -/
#guard_msgs in
#check wat3! "(module (type $t (struct)) (func (type $t)))"

/-- error: WAT at character 37: inline signature does not match referenced type -/
#guard_msgs in
#check wat3! "(module (type $t (func (param i32))) (func (type $t) (param i64)))"

/-- error: WAT at character 37: duplicate identifier $x -/
#guard_msgs in
#check wat3! "(module (type (struct (field $x i32) (field $x i64))))"

/-- error: WAT at character 25: duplicate identifier $x -/
#guard_msgs in
#check wat3! r#"(module (type $x (func)) (type $"x" (func)))"#

/-- error: WAT at character 15: imports must precede definitions -/
#guard_msgs in
#check wat3! "(module (func) (tag (import \"m\" \"t\")))"

/-- error: WAT at character 20: limit exceeds unsigned 64-bit range -/
#guard_msgs in
#check wat3! "(module (memory i64 18446744073709551616))"

/-- error: WAT at character 8: active data segment requires an offset -/
#guard_msgs in
#check wat3! "(module (data (memory 0)))"

/-- error: WAT at character 25: duplicate start declaration -/
#guard_msgs in
#check wat3! "(module (func) (start 0) (start 0))"

/-- error: WAT at character 28: duplicate export name 'f' -/
#guard_msgs in
#check wat3! "(module (func (export \"f\")) (memory (export \"f\") 0))"

/-- error: WAT at character 29: duplicate identifier $x -/
#guard_msgs in
#check wat3! "(module (func (param $x i32) (param $x i64)))"

/-- error: WAT at character 22: tag declaration cannot have a body -/
#guard_msgs in
#check wat3! "(module (type (func)) (tag (type 0) nop))"

/-- error: WAT expression requires implicit function types; use wat3! with a module context -/
#guard_msgs in
#check wat3_expr! "block (result i32 i64) end"
