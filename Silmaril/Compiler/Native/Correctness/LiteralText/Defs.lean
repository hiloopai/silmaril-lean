module

public import Silmaril.Compiler.Native.Correctness.Literal42.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralInteger.Defs
/-! A word-parametric literal-main assembly grammar/layout boundary. Text uses
exactly the native emitter's unsigned decimal spelling of the64-bit immediate.
Syntax and encoding use the actual Assembly relations and shared fixed labels. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralText
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Assembly

def body (value : Word) : String := "  push rbp\n  mov rbp, rsp\n  sub rsp, 48\n  and rsp, -64\n.Lccomp.0.0.0:\n  mov rax, rsp\n  mov QWORD PTR [rbp - 8], rax\n  jmp .Lccomp.0.0.1\n.Lccomp.0.0.1:\n  movabs rax, " ++ toString value.toNat ++ "\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 32], rax\n  mov rax, QWORD PTR [rbp - 32]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 40], rax\n  mov rax, QWORD PTR [rbp - 40]\n  leave\n  ret\n.Lccomp.0.0.2:\n  movabs rax, 0\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  leave\n  ret\n"

def statements (value : Word) : List Statement := [
  .plain (.push .rbp), .plain (.mov .q (.reg .rbp) .rsp),
  .plain (.aluI8 .q .sub (.reg .rsp) 48), .plain (.aluI8 .q .and (.reg .rsp) 0xc0),
  .label ".Lccomp.0.0.0", .plain (.mov .q (.reg .rax) .rsp),
  .plain (.mov .q (.mem (frame 8)) .rax), .jump ".Lccomp.0.0.1", .label ".Lccomp.0.0.1",
  .plain (.movabs .rax value), .plain (.mov .q (.mem (frame 24)) .rax),
  .plain (.load .q .rax (frame 24)), .plain (.movsxd .rax (.reg .rax)),
  .plain (.mov .q (.mem (frame 32)) .rax), .plain (.load .q .rax (frame 32)),
  .plain (.movsxd .rax (.reg .rax)), .plain (.mov .q (.mem (frame 40)) .rax),
  .plain (.load .q .rax (frame 40)), .plain .leave, .plain .ret,
  .label ".Lccomp.0.0.2", .plain (.movabs .rax 0),
  .plain (.mov .q (.mem (frame 24)) .rax), .plain (.load .q .rax (frame 24)),
  .plain .leave, .plain .ret]

abbrev labels : Labels := Literal42.Text.labels
abbrev bytes (value : Word) : List Byte := LiteralInteger.code value

def assembly (value : Word) : String :=
  Literal42.Text.mainPreamble ++ body value ++ Literal42.Text.mainEnding

end Silmaril.Compiler.Native.Correctness.LiteralText
