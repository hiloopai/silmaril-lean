module

public import Silmaril.Compiler.Core.ElaborationProcess.Defs
public import Silmaril.Compiler.Native.Driver.Defs
/-! A concrete actual typed-Ail literal-main source and the native compiler's
literal assembly template. Bounds inspect the input integer independently of
compiler acceptance or execution. Machine/assembler correctness is separate. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralEmission
open Silmaril.Cerberus
open Silmaril.Compiler.Core.ElaborationProcess

/-- The independently stated mathematical range of a signed 32-bit integer. -/
def IsInt32 (number : Int) : Prop := -(2^31) ≤ number ∧ number < 2^31

def literal (number : Int) : LiteralMain where
  symbol := ⟨⟨[]⟩, 1, .id "main"⟩
  location := .unknown
  marker := 7
  attributes := .mk []
  blockDesugaring := ⟨false, none⟩
  statementLocation := .unknown
  expressionLocation := .unknown
  returnDesugaring := ⟨false, none⟩
  statementAttributes := .mk []
  returnAnnotations := []
  number := number
  basis := .decimal
  suffix := none

def assembly (word : Silmaril.X86.Word) : String := ".intel_syntax noprefix\n.text\n.globl " ++ "\"main\"" ++ "\n.type " ++ "\"main\"" ++ ", @function\n" ++ "\"main\"" ++ ":\n  push rbp\n  mov rbp, rsp\n  sub rsp, 48\n  and rsp, -64\n.Lccomp.0.0.0:\n  mov rax, rsp\n  mov QWORD PTR [rbp - 8], rax\n  jmp .Lccomp.0.0.1\n.Lccomp.0.0.1:\n  movabs rax, " ++ toString word.toNat ++ "\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 32], rax\n  mov rax, QWORD PTR [rbp - 32]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 40], rax\n  mov rax, QWORD PTR [rbp - 40]\n  leave\n  ret\n.Lccomp.0.0.2:\n  movabs rax, 0\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  leave\n  ret\n.size " ++ "\"main\"" ++ ", . - " ++ "\"main\"" ++ "\n.section .note.GNU-stack,\"\",@progbits\n"


end Silmaril.Compiler.Native.Correctness.LiteralEmission
