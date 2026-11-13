module

public import Silmaril.Compiler.Native.Correctness.LiteralText.Defs
public import Silmaril.Compiler.Native.Assembly.Thms
public import Silmaril.Compiler.Native.Correctness.LiteralInteger.Thms
public import Silmaril.Compiler.Native.Assembly.Lexical.Thms
/-! Genuine assembly parsing and fixed-table encoding for every literal word.
The selected immediate is recovered through the actual numeric parser. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralText
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Assembly
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000

private theorem rawAppend_assoc (a b c : String) :
    (a.append b).append c = a.append (b.append c) := String.append_assoc

attribute [local cbv_opaque] String.append

/-- The generic grammar envelope is exactly the actual native emitter text. -/
theorem actual_emission (value : Word) : assembly value = LiteralEmission.assembly value := by
  unfold assembly body LiteralEmission.assembly
  generalize toString value.toNat = immediate
  cbv
  simp only [rawAppend_assoc]
  simp only [String.append]
  cbv

/-- All local uses resolve uniquely, independently of the immediate. -/
theorem local_labels (value : Word) : Local (statements value) := by
  simp [Local, statements]

private theorem suffix_assembles (value : Word) :
    Assembles labels 31 ((statements value).drop 10) (LiteralImage.code.drop 31) 83 := by
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 39 ((statements value).drop 12) (LiteralImage.code.drop 39) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 61 ((statements value).drop 18) (LiteralImage.code.drop 61) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.label (by cbv) ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  show Assembles labels 81 ((statements value).drop 24) (LiteralImage.code.drop 81) 83
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  exact Assembles.nil

private theorem prefix_assembles (value : Word) (tail : List Byte)
    (rest : Assembles labels 21 ((statements value).drop 9) tail 83) :
    Assembles labels 0 (statements value) (LiteralImage.code.take 21 ++ tail) 83 := by
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.label (by cbv) ?_
  refine Assembles.plain ?_
  refine Assembles.plain ?_
  refine Assembles.jump8 (target := 21) (by cbv)
    (by constructor <;> decide +kernel) ?_
  refine Assembles.label (by cbv) ?_
  exact rest

theorem assembles (value : Word) : Assembles labels 0 (statements value) (bytes value) 83 := by
  apply prefix_assembles value
  exact Assembles.plain (suffix_assembles value)

theorem assembly_unique {value : Word} {code : List Byte} {endPc : Nat}
    (assembled : Assembles labels 0 (statements value) code endPc) : code = (bytes value) := by
  let output := code
  change output = (bytes value)
  unfold statements at assembled
  cases assembled with
  | plain assembled =>
    show output = (bytes value)
    cases assembled with
    | plain assembled =>
      show output = (bytes value)
      cases assembled with
      | plain assembled =>
        show output = (bytes value)
        cases assembled with
        | plain assembled =>
          show output = (bytes value)
          cases assembled with
          | label found assembled =>
            show output = (bytes value)
            cases assembled with
            | plain assembled =>
              show output = (bytes value)
              cases assembled with
              | plain assembled =>
                show output = (bytes value)
                cases assembled with
                | jump8 found fits assembled =>
                  show output = (bytes value)
                  cases found
                  cases assembled with
                  | label found assembled =>
                    show output = (bytes value)
                    cases assembled with
                    | plain assembled =>
                      show output = (bytes value)
                      cases assembled with
                      | plain assembled =>
                        show output = (bytes value)
                        cases assembled with
                        | plain assembled =>
                          show output = (bytes value)
                          cases assembled with
                          | plain assembled =>
                            show output = (bytes value)
                            cases assembled with
                            | plain assembled =>
                              show output = (bytes value)
                              cases assembled with
                              | plain assembled =>
                                show output = (bytes value)
                                cases assembled with
                                | plain assembled =>
                                  show output = (bytes value)
                                  cases assembled with
                                  | plain assembled =>
                                    show output = (bytes value)
                                    cases assembled with
                                    | plain assembled =>
                                      show output = (bytes value)
                                      cases assembled with
                                      | plain assembled =>
                                        show output = (bytes value)
                                        cases assembled with
                                        | plain assembled =>
                                          show output = (bytes value)
                                          cases assembled with
                                          | label found assembled =>
                                            show output = (bytes value)
                                            cases assembled with
                                            | plain assembled =>
                                              show output = (bytes value)
                                              cases assembled with
                                              | plain assembled =>
                                                show output = (bytes value)
                                                cases assembled with
                                                | plain assembled =>
                                                  show output = (bytes value)
                                                  cases assembled with
                                                  | plain assembled =>
                                                    show output = (bytes value)
                                                    cases assembled with
                                                    | plain assembled =>
                                                      show output = (bytes value)
                                                      cases assembled
                                                      rfl
                | jump32 found fits assembled =>
                  show output = (bytes value)
                  cases found
                  cases assembled with
                  | label impossible assembled =>
                    show output = (bytes value)
                    change (some 21 : Option Nat) = some 24 at impossible
                    cases impossible



/-- Every literal has the same concrete instruction extent. -/
theorem byte_length (value : Word) : (bytes value).length = 83 :=
  LiteralInteger.code_length value

private def tokenLines (value : Word) : List (List String) := [
  ["push", "rbp"],
  ["mov", "rbp", ",", "rsp"],
  ["sub", "rsp", ",", "48"],
  ["and", "rsp", ",", "-", "64"],
  [".Lccomp.0.0.0:"],
  ["mov", "rax", ",", "rsp"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "8", "]", ",", "rax"],
  ["jmp", ".Lccomp.0.0.1"],
  [".Lccomp.0.0.1:"],
  ["movabs", "rax", ",", Nat.repr value.toNat],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "32", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "32", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "40", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "40", "]"],
  ["leave"],
  ["ret"],
  [".Lccomp.0.0.2:"],
  ["movabs", "rax", ",", "0"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"],
  ["leave"],
  ["ret"],
  []
]

private theorem movabs_selected {expected value : Word}
    (parsed : Spells ["movabs", "rax", ",", toString expected.toNat]
      (.plain (.movabs .rax value))) : value = expected := by
  generalize tokensEq : ["movabs", "rax", ",", toString expected.toNat] = tokens at parsed
  cases parsed with
  | @movabs destination immediate _ n dst number range =>
    have tokenFacts : "rax" = destination ∧ toString expected.toNat = immediate := by
      simpa only [List.cons.injEq, and_true, true_and] using tokensEq
    have immediateEq : toString expected.toNat = immediate := tokenFacts.2
    rw [← immediateEq] at number
    have sameNumber : expected.toNat = n :=
      Except.ok.inj ((natural_toString expected.toNat).symm.trans number)
    rw [← sameNumber]
    exact BitVec.ofNat_toNat 64 expected

private theorem lines_selected {expected value : Word}
    (parsed : Lines (tokenLines expected) (statements value)) : value = expected := by
  cases parsed with
  | cons head rest =>
    show value = expected
    cases rest with
    | cons head rest =>
      show value = expected
      cases rest with
      | cons head rest =>
        show value = expected
        cases rest with
        | cons head rest =>
          show value = expected
          cases rest with
          | cons head rest =>
            show value = expected
            cases rest with
            | cons head rest =>
              show value = expected
              cases rest with
              | cons head rest =>
                show value = expected
                cases rest with
                | cons head rest =>
                  show value = expected
                  cases rest with
                  | cons head rest =>
                    show value = expected
                    cases rest with
                    | cons head rest =>
                      show value = expected
                      exact movabs_selected head

private def charLines (value : Word) : List (List Char) := [
  [' ', ' ', 'p', 'u', 's', 'h', ' ', 'r', 'b', 'p'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'b', 'p', ',', ' ', 'r', 's', 'p'],
  [' ', ' ', 's', 'u', 'b', ' ', 'r', 's', 'p', ',', ' ', '4', '8'],
  [' ', ' ', 'a', 'n', 'd', ' ', 'r', 's', 'p', ',', ' ', '-', '6', '4'],
  ['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '0', ':'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'r', 's', 'p'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '8', ']', ',', ' ', 'r', 'a', 'x'],
  [' ', ' ', 'j', 'm', 'p', ' ', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1'],
  ['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1', ':'],
  [' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' '] ++ (Nat.repr value.toNat).toList,
  [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']'],
  [' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', ',', ' ', 'r', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']'],
  [' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', ',', ' ', 'r', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']'],
  [' ', ' ', 'l', 'e', 'a', 'v', 'e'],
  [' ', ' ', 'r', 'e', 't'],
  ['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '2', ':'],
  [' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' ', '0'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x'],
  [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']'],
  [' ', ' ', 'l', 'e', 'a', 'v', 'e'],
  [' ', ' ', 'r', 'e', 't'],
  []
]

private theorem body_split (value : Word) :
    Silmaril.X86.Assembly.split '\n' (body value).toList = charLines value := by
  have prefixList : "  push rbp\n  mov rbp, rsp\n  sub rsp, 48\n  and rsp, -64\n.Lccomp.0.0.0:\n  mov rax, rsp\n  mov QWORD PTR [rbp - 8], rax\n  jmp .Lccomp.0.0.1\n.Lccomp.0.0.1:\n  movabs rax, ".toList = [' ', ' ', 'p', 'u', 's', 'h', ' ', 'r', 'b', 'p', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'b', 'p', ',', ' ', 'r', 's', 'p', '\n', ' ', ' ', 's', 'u', 'b', ' ', 'r', 's', 'p', ',', ' ', '4', '8', '\n', ' ', ' ', 'a', 'n', 'd', ' ', 'r', 's', 'p', ',', ' ', '-', '6', '4', '\n', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '0', ':', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'r', 's', 'p', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '8', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'j', 'm', 'p', ' ', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1', '\n', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1', ':', '\n', ' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' '] := by cbv
  have suffixList : "\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 32], rax\n  mov rax, QWORD PTR [rbp - 32]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 40], rax\n  mov rax, QWORD PTR [rbp - 40]\n  leave\n  ret\n.Lccomp.0.0.2:\n  movabs rax, 0\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  leave\n  ret\n".toList = ['\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '2', ':', '\n', ' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' ', '0', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n'] := by cbv
  unfold body
  rw [String.toList_append, String.toList_append]
  change Silmaril.X86.Assembly.split '\n'
    (("  push rbp\n  mov rbp, rsp\n  sub rsp, 48\n  and rsp, -64\n.Lccomp.0.0.0:\n  mov rax, rsp\n  mov QWORD PTR [rbp - 8], rax\n  jmp .Lccomp.0.0.1\n.Lccomp.0.0.1:\n  movabs rax, ".toList ++ (Nat.repr value.toNat).toList) ++ "\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 32], rax\n  mov rax, QWORD PTR [rbp - 32]\n  movsxd rax, eax\n  mov QWORD PTR [rbp - 40], rax\n  mov rax, QWORD PTR [rbp - 40]\n  leave\n  ret\n.Lccomp.0.0.2:\n  movabs rax, 0\n  mov QWORD PTR [rbp - 24], rax\n  mov rax, QWORD PTR [rbp - 24]\n  leave\n  ret\n".toList) = charLines value
  have consume := splitAux_repr_append value.toNat
    ['\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '2', ':', '\n', ' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' ', '0', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n']
    [' ', ',', 'x', 'a', 'r', ' ', 's', 'b', 'a', 'v', 'o', 'm', ' ', ' ']
    [['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1', ':'], [' ', ' ', 'j', 'm', 'p', ' ', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1'], [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '8', ']', ',', ' ', 'r', 'a', 'x'], [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'r', 's', 'p'], ['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '0', ':'], [' ', ' ', 'a', 'n', 'd', ' ', 'r', 's', 'p', ',', ' ', '-', '6', '4'], [' ', ' ', 's', 'u', 'b', ' ', 'r', 's', 'p', ',', ' ', '4', '8'], [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'b', 'p', ',', ' ', 'r', 's', 'p'], [' ', ' ', 'p', 'u', 's', 'h', ' ', 'r', 'b', 'p']]
  unfold charLines
  generalize (Nat.repr value.toNat).toList = digits at consume ⊢
  rw [prefixList, suffixList, List.append_assoc]
  unfold Silmaril.X86.Assembly.split
  change Silmaril.X86.Assembly.splitAux '\n'
    (digits ++ ['\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '3', '2', ']', '\n', ' ', ' ', 'm', 'o', 'v', 's', 'x', 'd', ' ', 'r', 'a', 'x', ',', ' ', 'e', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '4', '0', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '2', ':', '\n', ' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' ', '0', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', ',', ' ', 'r', 'a', 'x', '\n', ' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '2', '4', ']', '\n', ' ', ' ', 'l', 'e', 'a', 'v', 'e', '\n', ' ', ' ', 'r', 'e', 't', '\n'])
    [' ', ',', 'x', 'a', 'r', ' ', 's', 'b', 'a', 'v', 'o', 'm', ' ', ' ']
    [['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1', ':'], [' ', ' ', 'j', 'm', 'p', ' ', '.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '1'], [' ', ' ', 'm', 'o', 'v', ' ', 'Q', 'W', 'O', 'R', 'D', ' ', 'P', 'T', 'R', ' ', '[', 'r', 'b', 'p', ' ', '-', ' ', '8', ']', ',', ' ', 'r', 'a', 'x'], [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'a', 'x', ',', ' ', 'r', 's', 'p'], ['.', 'L', 'c', 'c', 'o', 'm', 'p', '.', '0', '.', '0', '.', '0', ':'], [' ', ' ', 'a', 'n', 'd', ' ', 'r', 's', 'p', ',', ' ', '-', '6', '4'], [' ', ' ', 's', 'u', 'b', ' ', 'r', 's', 'p', ',', ' ', '4', '8'], [' ', ' ', 'm', 'o', 'v', ' ', 'r', 'b', 'p', ',', ' ', 'r', 's', 'p'], [' ', ' ', 'p', 'u', 's', 'h', ' ', 'r', 'b', 'p']] = _
  rw [consume]
  rw [Silmaril.X86.Assembly.splitAux]
  simp only [beq_self_eq_true, ite_true]
  rw [List.reverse_append, List.reverse_reverse]
  cbv

private theorem explicit_token (value : Word) :
    Silmaril.X86.Assembly.tokenizeChars
      (['m', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' '] ++
        (Nat.repr value.toNat).toList) [] [] = ["movabs", "rax", ",", Nat.repr value.toNat] := by
  have variableToken := tokenize_movabs_repr value
  unfold Silmaril.X86.Assembly.tokenize at variableToken
  rw [String.toList_append] at variableToken
  generalize Nat.repr value.toNat = numeral at variableToken ⊢
  generalize numeral.toList = digits at variableToken ⊢
  have prefixList : ("movabs rax, " : String).toList =
      ['m', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' '] := by cbv
  rw [prefixList] at variableToken
  exact variableToken

private theorem indented_token (value : Word) :
    Silmaril.X86.Assembly.tokenizeChars
      ([' ', ' ', 'm', 'o', 'v', 'a', 'b', 's', ' ', 'r', 'a', 'x', ',', ' '] ++
        (Nat.repr value.toNat).toList) [] [] = ["movabs", "rax", ",", Nat.repr value.toNat] := by
  have token := explicit_token value
  generalize Nat.repr value.toNat = numeral at token ⊢
  generalize numeral.toList = digits at token ⊢
  exact token

private theorem chars_tokens (value : Word) :
    (charLines value).map (fun chars => Silmaril.X86.Assembly.tokenizeChars chars [] []) =
      tokenLines value := by
  unfold charLines tokenLines
  simp only [List.map_cons, List.map_nil]
  have token := indented_token value
  generalize Nat.repr value.toNat = numeral at token ⊢
  generalize numeral.toList = digits at token ⊢
  rw [token]
  cbv


private theorem body_tokens (value : Word) :
    ((Silmaril.X86.Assembly.split '\n' (body value).toList).map
      (fun chars => Silmaril.X86.Assembly.tokenizeChars chars [] [])) = tokenLines value := by
  rw [body_split]
  exact chars_tokens value

theorem body_syntax (value : Word) : Parses (body value) (statements value) := by
  unfold Parses
  rw [body_tokens]
  unfold tokenLines
  refine Lines.cons (Spells.push (by cbv)) ?_
  refine Lines.cons (Spells.mov (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.aluI8 (n := 48) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)) ?_
  show Lines _ ((statements value).drop 3)
  refine Lines.cons (Spells.aluI8 (n := -64) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.0") (by decide +kernel)) ?_
  refine Lines.cons (Spells.mov (by cbv) (by cbv)) ?_
  show Lines _ ((statements value).drop 6)
  refine Lines.cons (Spells.store (n := 8) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.jump (by decide +kernel)) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.1") (by decide +kernel)) ?_
  refine Lines.cons (movabs_repr value) ?_
  refine Lines.cons (Spells.store (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ ((statements value).drop 12)
  refine Lines.cons (Spells.movsxd (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.store (n := 32) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 32) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.movsxd (by cbv) (by cbv)) ?_
  refine Lines.cons (Spells.store (n := 40) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 40) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ ((statements value).drop 18)
  refine Lines.cons (Spells.leave) ?_
  refine Lines.cons (Spells.ret) ?_
  refine Lines.cons (Spells.label (name := ".Lccomp.0.0.2") (by decide +kernel)) ?_
  refine Lines.cons (Spells.movabs (n := 0) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.store (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  refine Lines.cons (Spells.load (n := 24) (by cbv) (by cbv) (by decide +kernel)) ?_
  show Lines _ ((statements value).drop 24)
  refine Lines.cons (Spells.leave) ?_
  refine Lines.cons (Spells.ret) ?_
  exact Lines.blank Lines.nil

theorem main_syntax (value : Word) :
    Literal42.Text.MainSyntax (assembly value) (statements value) :=
  Literal42.Text.MainSyntax.function (body_syntax value)

/-- Grammar-selected literals are forced by the actual numeric parser. -/
theorem parsed_value_unique {expected value : Word}
    (parsed : Literal42.Text.MainSyntax (assembly expected) (statements value)) :
    value = expected := by
  generalize textEq : assembly expected = text at parsed
  cases parsed with
  | function bodyParsed =>
    unfold assembly at textEq
    have bodyEq := (String.append_right_inj Literal42.Text.mainPreamble).mp
      ((String.append_left_inj Literal42.Text.mainEnding).mp textEq)
    rw [← bodyEq] at bodyParsed
    unfold Parses at bodyParsed
    rw [body_tokens] at bodyParsed
    exact lines_selected bodyParsed

end Silmaril.Compiler.Native.Correctness.LiteralText
