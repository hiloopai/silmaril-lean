module

public import Silmaril.Compiler.Native.Assembly.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralImage.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralTotal.Defs
public import Silmaril.Compiler.Native.Correctness.Hets.Defs
/-! An independently selected closed-main singleton source and a concrete formal
assembly/loader toolchain. The source domain fixes syntax, target/runtime inputs,
options and argv only; it assumes no compiler success or behavior. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Literal42
open Silmaril Silmaril.X86
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Compiler.Core.ElaborationProcess
open Silmaril.Compiler.Native.Assembly
open Construction

namespace Text
export Silmaril.Compiler.Native.Assembly (Assembles Local)
def body : String := "  push rbp\n  mov rbp, rsp\n  sub rsp, 48\n  and rsp, -64\n.Lccomp.0.0.0:\n  mov rax, rsp\n  mov QWORD PTR [rbp - 8], rax\n  jmp .Lccomp.0.0.1\n.Lccomp.0.0.1:\n  movabs rax, 42\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 32], rax\n  mov rax, QWORD PTR [rbp - 32]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 40], rax\n  mov rax, QWORD PTR [rbp - 40]\n  leave\n  ret\n.Lccomp.0.0.2:\n  movabs rax, 0\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  leave\n  ret\n"

def statements : List Statement := [
  .plain (.push .rbp), .plain (.mov .q (.reg .rbp) .rsp),
  .plain (.aluI8 .q .sub (.reg .rsp) 48), .plain (.aluI8 .q .and (.reg .rsp) 0xc0),
  .label ".Lccomp.0.0.0", .plain (.mov .q (.reg .rax) .rsp),
  .plain (.mov .q (.mem (frame 8)) .rax), .jump ".Lccomp.0.0.1", .label ".Lccomp.0.0.1",
  .plain (.movabs .rax 42), .plain (.mov .q (.mem (frame 24)) .rax),
  .plain (.load .q .rax (frame 24)), .plain (.movsxd .rax (.reg .rax)),
  .plain (.mov .q (.mem (frame 32)) .rax), .plain (.load .q .rax (frame 32)),
  .plain (.movsxd .rax (.reg .rax)), .plain (.mov .q (.mem (frame 40)) .rax),
  .plain (.load .q .rax (frame 40)), .plain .leave, .plain .ret,
  .label ".Lccomp.0.0.2", .plain (.movabs .rax 0),
  .plain (.mov .q (.mem (frame 24)) .rax), .plain (.load .q .rax (frame 24)),
  .plain .leave, .plain .ret]

def labels : Labels := fun name =>
  if name == ".Lccomp.0.0.0" then some 12
  else if name == ".Lccomp.0.0.1" then some 21
  else if name == ".Lccomp.0.0.2" then some 63
  else none

abbrev bytes : List Byte := LiteralImage.code

def mainPreamble : String := ".intel_syntax noprefix\n.text\n.globl \"main\"\n.type \"main\", @function\n\"main\":\n"
def mainEnding : String := ".size \"main\", . - \"main\"\n.section .note.GNU-stack,\"\",@progbits\n"

inductive MainSyntax : String → List Statement → Prop where
  | function {bodyText : String} {statementList : List Statement}
      (parsed : Parses bodyText statementList) :
      MainSyntax (mainPreamble ++ bodyText ++ mainEnding) statementList

/-- A restricted, explicit text-to-byte relation with checked local layout. -/
def EncodesMain (source : String) (code : List Byte) : Prop :=
  ∃ statements labels endPc,
    MainSyntax source statements ∧ Local statements ∧ Assembles labels 0 statements code endPc

def assembly : String := mainPreamble ++ body ++ mainEnding
end Text

def sym (index : Nat) (name : String) : Sym := ⟨⟨[]⟩, index, .id name⟩
def conversion := sym 2 "conv_loaded_int"
def convertInteger := sym 3 "conv_int"
def representable := sym 4 "is_representable_integer"
def typeParameter := sym 10 "type"
def valueParameter := sym 11 "value"
def numberParameter := sym 12 "number"

def representableBody : Pure :=
  operation .and
    (operation .le (ivmin (symbolPure typeParameter)) (symbolPure numberParameter))
    (operation .le (symbolPure numberParameter) (ivmax (symbolPure typeParameter)))

def convertIntegerBody : Pure :=
  ifPure (operation .eq (symbolPure typeParameter) (ctype (.mk [] (.basic (.integer .bool)))))
    (integer 0)
    (ifPure (call (.sym representable) [symbolPure numberParameter, symbolPure typeParameter])
      (symbolPure numberParameter) (integer 0))

def conversionBody : Pure :=
  casePure (symbolPure valueParameter)
    [(.mk [] (.ctor .specified [symbolPattern numberParameter (.object .integer)]),
      specified (call (.sym convertInteger) [symbolPure typeParameter, symbolPure numberParameter]))]

def runtime : Functions.RuntimeInputs where
  stdlib := [
    (conversion, .function (.loaded .integer)
      [(typeParameter, .ctype), (valueParameter, .loaded .integer)] conversionBody),
    (convertInteger, .function (.object .integer)
      [(typeParameter, .ctype), (numberParameter, .object .integer)] convertIntegerBody),
    (representable, .function .boolean
      [(numberParameter, .object .integer), (typeParameter, .ctype)] representableBody)]
  impl := []
  aliases := []

def literal (number : Int) : LiteralMain where
  symbol := sym 1 "main"
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

def source42 : Source where
  program := (literal 42).program
  elaboration := {
    config := Silmaril.Cerberus.Target.pinnedApple
    runtime := runtime
    freshness := ⟨⟨[]⟩, 100, 1000⟩ }
  options := { opt := some .O0 }
  tag := "literal-linkage"
  commit := "formal-literal42-model-certificate"
  implementation := "constructed-conversion-runtime; explicit-pinnedApple; closed-main-model"
  enumBindings := []
  arguments := ["a.out"]

/-- A singleton input predicate fixes source/environment syntax only. -/
def domain (source : Source) : Prop := source = source42

/-- Deterministic closed-main loading of formally assembled bytes. Code,
stack, return word, argv and reset feature state are all constructed explicitly. -/
def loadImage (code : List Byte) : Image := {
  codeBase := 0x1000, code, entry := 0x1000, exit := 0x4000, argvAddress := 0x5000,
  initial := ⟨Features.State.ofCore LiteralImage.core, {
    regions := [⟨0x1000, 0x1000, ⟨true, false, true⟩⟩,
      ⟨0x2000, 0x1000, ⟨true, true, false⟩⟩,
      ⟨0x5000, 0x1000, ⟨true, false, false⟩⟩]
    bytes := Process.Memory.install
      (Process.Memory.install (Process.Memory.install ∅ 0x1000 code)
        0x2ff8 (Machine.LittleEndian.encodeWords [0x4000]))
      0x5000 ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
        fun byte => BitVec.ofNat 8 byte.toNat) }⟩ }

/-- A checked assembly derivation supplies bytes to the actual explicit loader.
The source text must satisfy independent syntax; it is not accepted by equality
with a captured output or by a supplied successful machine interpreter. -/
def Loads (text : String) (arguments : List String) (image : Image) : Prop :=
  ∃ code, Text.MainSyntax text Text.statements ∧ Text.Local Text.statements ∧
    Text.Assembles Text.labels 0 Text.statements code 83 ∧
    arguments = ["a.out"] ∧ image = loadImage code

def target : Target := ⟨Text.assembly, ["a.out"]⟩


end Silmaril.Compiler.Native.Correctness.Literal42
