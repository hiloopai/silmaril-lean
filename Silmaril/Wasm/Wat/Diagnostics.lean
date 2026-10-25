module

public import Silmaril.Wasm.Wat

/-! # Rejected WAT inputs

These check actual macro diagnostics, including range/sign distinctions,
namespace resolution, unsupported extensions, and lexical ambiguity.
-/

/-- error: WAT at character 10: integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i32.const 4294967296"

/-- error: WAT at character 10: integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i32.const +2147483648"

/-- error: WAT at character 10: negative integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i32.const -2147483649"

/-- error: WAT at character 10: misplaced underscore in numeric literal -/
#guard_msgs in
#check wat1_expr! "i32.const 1__0"

/-- error: WAT at character 10: numeric literal must end in a digit -/
#guard_msgs in
#check wat1_expr! "i32.const 0x"

/-- error: WAT at character 10: unknown local identifier $x -/
#guard_msgs in
#check wat1_expr! "local.get $x"

/-- error: WAT at character 13: closing label does not match opening label -/
#guard_msgs in
#check wat1_expr! "block $x end $y"

/-- error: WAT at character 9: alignment must be a nonzero power of two in unsigned 32-bit range -/
#guard_msgs in
#check wat1_expr! "i32.load align=3"

/-- error: WAT at character 0: unsupported instruction 'i32.load32_s' -/
#guard_msgs in
#check wat1_expr! "i32.load32_s"

/-- error: WAT at character 0: unsupported instruction 'memory.copy' -/
#guard_msgs in
#check wat1_expr! "memory.copy"

/-- error: WAT at character 0: folded operands must be parenthesized instructions -/
#guard_msgs in
#check wat1_expr! "(i32.add i32.const 1)"

/-- error: WAT at character 18: duplicate identifier $f -/
#guard_msgs in
#check wat1! "(module (func $f) (func $f))"

/-- error: WAT at character 37: inline signature does not match referenced type -/
#guard_msgs in
#check wat1! "(module (type $t (func (param i32))) (func (type $t) (param i64)))"

/-- error: WAT at character 15: imports must precede definitions -/
#guard_msgs in
#check wat1! "(module (func) (import \"m\" \"f\" (func)))"

/-- error: WAT at character 16: name is not valid UTF-8 -/
#guard_msgs in
#check wat1! r#"(module (export "\ff" (func 0)))"#

/-- error: WAT at character 18: unsupported string escape -/
#guard_msgs in
#check wat1! r#"(module (export "\q" (func 0)))"#

/-- error: WAT at character 0: unterminated block comment -/
#guard_msgs in
#check wat1_expr! "(; unclosed"

/-- error: WAT at character 0: folded if accepts one then group and an optional else group -/
#guard_msgs in
#check wat1_expr! "(if (then nop) (else nop) (else nop))"

/-- error: WAT at character 8: Wasm1 function types have at most one result -/
#guard_msgs in
#check wat1! "(module (func (result i32 i64)))"

/-- error: WAT at character 10: integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i64.const 18446744073709551616"

/-- error: WAT at character 10: integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i64.const +9223372036854775808"

/-- error: WAT at character 10: negative integer literal out of range -/
#guard_msgs in
#check wat1_expr! "i64.const -9223372036854775809"

/-- error: WAT at character 20: unknown label identifier $f -/
#guard_msgs in
#check wat1! "(module (func $f br $f))"

/-- error: WAT at character 14: block signature parameters must be anonymous -/
#guard_msgs in
#check watLime! "(module (func (block (param $x i32))))"

/-- error: WAT at character 14: block signature parameters must be anonymous -/
#guard_msgs in
#check watLime! "(module (func (loop (param $x i32))))"

/-- error: WAT at character 14: block signature parameters must be anonymous -/
#guard_msgs in
#check watLime! "(module (func (if (param $x i32) (then))))"

/-- error: WAT at character 15: call_indirect parameters must be anonymous -/
#guard_msgs in
#check wat1! "(module (func (call_indirect (param $x i32))))"
