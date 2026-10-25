module

public import Silmaril.Wasm.Wat

/-! # Shared WAT lexical and elaboration regressions

These inspect ordinary ASTs produced by the public scalar quotations, so they
exercise the common lexer, signature parser, and instruction traversal together.
-/

@[expose] public section
namespace Silmaril.Wasm.Wat.SharedExamples

/-- Both newline spellings end line comments. -/
example : wat1_expr! "i32.const 1 ;; comment\ri32.const 2" =
    [V1.Instr.intConst .i32 1, .intConst .i32 2] := rfl

/-- Annotations may contain balanced token lists, comments, and quoted delimiters. -/
example : wat1_expr! r#"(@"custom\20name" ("( )") (; ignored ;) (@nested [reserved]))nop"# =
    [V1.Instr.nop] := rfl

example : wat1_expr! r#"block $"outer label" br $"outer label" end $"outer label""# =
    [V1.Instr.block none [.br ⟨0⟩]] := rfl

/-- Quoted and unquoted identifiers denote the same UTF-8 name. -/
def quotedNames := wat1! r#"
(module
  (func $"f x" (param $"x" i32) (param $"λ" i64)
    local.get $x local.get $"\ce\bb")
  (export "f" (func $"f x")))
"#

example : quotedNames.funcs[0].body =
    [V1.Instr.localGet ⟨0⟩, .localGet ⟨1⟩] := rfl
example : quotedNames.exports[0].index = .func ⟨0⟩ := rfl

/-- Names in a type declaration are annotations, not local bindings. -/
def typeAnnotations := wat1! r#"
(module (type $t (func (param $x i32) (param $x i64)))
  (func (type $t) local.get 0 local.get 1))
"#

example : typeAnnotations.types = [⟨[.i32, .i64], []⟩] := rfl

example : wat1_expr! "f32.const 0.1 f64.const -0x0p+0" =
    [V1.Instr.floatConst .f32 0x3dcccccd, .floatConst .f64 0x8000000000000000] := rfl

example : watLime_expr! "(f64.copysign (f64.const inf) (f64.const -nan:0x1))" =
    [Lime1.Instr.floatConst .f64 0x7ff0000000000000,
      .floatConst .f64 0xfff0000000000001, .floatBinOp .f64 .copysign] := rfl

end Silmaril.Wasm.Wat.SharedExamples

/-- error: WAT at character 0: reserved token: adjacent tokens require whitespace, parentheses, or a comment -/
#guard_msgs in
#check wat1_expr! r#""a""b""#

/-- error: WAT at character 0: reserved token: adjacent tokens require whitespace, parentheses, or a comment -/
#guard_msgs in
#check wat1_expr! r#"$x"s""#

/-- error: WAT at character 0: reserved token: adjacent tokens require whitespace, parentheses, or a comment -/
#guard_msgs in
#check wat1_expr! r#"1"s""#

/-- error: WAT at character 0: reserved token: adjacent tokens require whitespace, parentheses, or a comment -/
#guard_msgs in
#check wat1_expr! r#"$"x"$y"#

/-- error: WAT at character 0: identifier is not valid UTF-8 -/
#guard_msgs in
#check wat1_expr! r#"$"\ff""#

/-- error: WAT at character 0: annotation requires an identifier after '(@' -/
#guard_msgs in
#check wat1_expr! "(@)nop"

/-- error: WAT at character 0: unterminated annotation -/
#guard_msgs in
#check wat1_expr! "(@x (nop)"

/-- Raw nested parenthesized annotation contents are not parsed as new annotations. -/
example : wat1_expr! "(@a @ @x (@x) (@x y) (@) (@ x) (@(@(@(@)))))nop" =
    [Silmaril.Wasm.V1.Instr.nop] := rfl

/-- error: WAT at character 0: annotation requires a nonempty identifier -/
#guard_msgs in
#check wat1_expr! r#"(@"")nop"#

/-- error: WAT at character 0: identifier must not be empty -/
#guard_msgs in
#check wat1_expr! r#"$"""#
