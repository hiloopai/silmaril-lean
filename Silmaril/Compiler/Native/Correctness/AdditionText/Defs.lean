module

public import Silmaril.Compiler.Native.Assembly.Scalar.Defs
public import Silmaril.Compiler.Native.Emit.AdditionFeatures.Defs
public import Silmaril.Compiler.Native.Correctness.MainLoader.Defs
/-! Complete unoptimized addition function text, including its unreachable
fallback. The formal grammar and layout are independent of native execution.
The existing explicit loader installs the complete156-byte image. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionText
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Assembly
open Silmaril.Compiler.Native.Emit

/-- Actual body lines before metadata framing; both variable immediates use
unsigned decimal word spelling, independently checked by the numeric grammar. -/
def bodyLines (left right : Word) : List String := [
  "  push rbp", "  mov rbp, rsp", "  sub rsp, 96", "  and rsp, -64",
  ".Lccomp.0.0.0:", "  mov rax, rsp", "  mov QWORD PTR [rbp - 8], rax",
  "  jmp .Lccomp.0.0.1", ".Lccomp.0.0.1:",
  "  movabs rax, " ++ Nat.repr left.toNat, "  mov QWORD PTR [rbp - 24], rax",
  "  mov rax, QWORD PTR [rbp - 24]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 32], rax",
  "  movabs rax, " ++ Nat.repr right.toNat, "  mov QWORD PTR [rbp - 40], rax",
  "  mov rax, QWORD PTR [rbp - 40]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 48], rax",
  "  mov rax, QWORD PTR [rbp - 32]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 56], rax",
  "  mov rax, QWORD PTR [rbp - 48]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 64], rax",
  "  mov rax, QWORD PTR [rbp - 56]", "  mov r10, QWORD PTR [rbp - 64]", "  add rax, r10", "  mov QWORD PTR [rbp - 72], rax",
  "  mov rax, QWORD PTR [rbp - 72]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 80], rax",
  "  mov rax, QWORD PTR [rbp - 80]", "  movsxd rax, eax", "  mov QWORD PTR [rbp - 88], rax",
  "  mov rax, QWORD PTR [rbp - 88]", "  leave", "  ret", ".Lccomp.0.0.2:",
  "  movabs rax, 0", "  mov QWORD PTR [rbp - 24], rax", "  mov rax, QWORD PTR [rbp - 24]", "  leave", "  ret"]

def body (left right : Word) : String := Assembly.Scalar.linesText (bodyLines left right)

def preamble : String := ".text\n.globl \"main\"\n.type \"main\", @function\n\"main\":\n"
def ending : String := ".size \"main\", . - \"main\"\n"

def text (left right : Word) : String := preamble ++ body left right ++ ending

def unitPreamble : String := ".intel_syntax noprefix\n"
def unitEnding : String := ".section .note.GNU-stack,\"\",@progbits\n"
def assembly (left right : Word) : String := unitPreamble ++ text left right ++ unitEnding

/-- Metadata framing fixes the complete actual function fragment; the body
still must be derived through the actual structural splitter and tokenizer. -/
inductive MainSyntax : String → List Statement → Prop where
  | function {bodyText : String} {statements : List Statement}
      (parsed : Assembly.Scalar.Parses bodyText statements) :
      MainSyntax (preamble ++ bodyText ++ ending) statements

/-- The complete native unit retains the real driver metadata around its
independently parsed function fragment. -/
inductive UnitSyntax : String → List Statement → Prop where
  | unit {functionText : String} {statements : List Statement}
      (functionSyntax : MainSyntax functionText statements) :
      UnitSyntax (unitPreamble ++ functionText ++ unitEnding) statements

def fallback : List Ext.Instr :=
  [.movabs .rax 0, .mov .q (.mem (frame 24)) .rax, .load .q .rax (frame 24), .leave, .ret]

def instructions (left right : Word) : List Ext.Instr :=
  AdditionFunction.instructions left right ++ fallback

def bytes (left right : Word) : List Byte := (instructions left right).flatMap Ext.encode

def statements (left right : Word) : List Statement :=
  AdditionFunction.plan.instructions.map Statement.plain ++ [.label ".Lccomp.0.0.0"] ++
  (Prologue.frameInstructions 0).map Statement.plain ++ [.jump ".Lccomp.0.0.1", .label ".Lccomp.0.0.1"] ++
  (AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain ++
  [.label ".Lccomp.0.0.2"] ++ fallback.map Statement.plain

def labels : Labels := fun name =>
  if name == ".Lccomp.0.0.0" then some 12
  else if name == ".Lccomp.0.0.1" then some 21
  else if name == ".Lccomp.0.0.2" then some 136
  else none

/-- The concrete deterministic loader installs all emitted bytes, including
the unreachable fallback; execution later uses its real reachable prefix. -/
abbrev image (left right : Word) : Image := MainLoader.image (bytes left right)

/-- Text acceptance requires independent full syntax, unique local labels and
actual encoding/layout. No emitter equality or machine behavior is an input. -/
def Loads (source : String) (arguments : List String) (loaded : Image) : Prop :=
  ∃ left right code,
    UnitSyntax source (statements left right) ∧ Local (statements left right) ∧
    Assembles labels 0 (statements left right) code 156 ∧
    arguments = ["a.out"] ∧ loaded = MainLoader.image code

end Silmaril.Compiler.Native.Correctness.AdditionText
