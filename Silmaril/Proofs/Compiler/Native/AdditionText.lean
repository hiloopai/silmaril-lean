module

public import Silmaril.Compiler.Native.Correctness.AdditionText.Defs
public import Silmaril.Compiler.Native.Assembly.Scalar.Thms
public import Silmaril.Compiler.Native.Emit.AdditionFeatures.Thms
public import Silmaril.Compiler.Native.Correctness.MainLoader.Thms
import Init.Data.Nat.ToString
import Init.Data.Int.ToString
import Mathlib.Data.List.Forall2

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionText
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Assembly
open Silmaril.Compiler.Native.Emit
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000

private theorem decimalDigits (n : Nat) :
    Nat.toDigits 10 n = if n < 10 then [n.digitChar]
      else Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] :=
  Nat.toDigits_eq_ite (by decide)
attribute [local cbv_eval] decimalDigits Nat.repr_eq_ofList_toDigits Nat.toString_eq_ofList_toDigits Int.repr_eq_ite
private theorem decimalDigit0 : Nat.digitChar 0 = '0' :=
  Nat.digitChar_eq_zero.mpr rfl
attribute [local cbv_eval] decimalDigit0
private theorem decimalDigit1 : Nat.digitChar 1 = '1' :=
  Nat.digitChar_eq_one.mpr rfl
attribute [local cbv_eval] decimalDigit1
private theorem decimalDigit2 : Nat.digitChar 2 = '2' :=
  Nat.digitChar_eq_two.mpr rfl
attribute [local cbv_eval] decimalDigit2
private theorem decimalDigit3 : Nat.digitChar 3 = '3' :=
  Nat.digitChar_eq_three.mpr rfl
attribute [local cbv_eval] decimalDigit3
private theorem decimalDigit4 : Nat.digitChar 4 = '4' :=
  Nat.digitChar_eq_four.mpr rfl
attribute [local cbv_eval] decimalDigit4
private theorem decimalDigit5 : Nat.digitChar 5 = '5' :=
  Nat.digitChar_eq_five.mpr rfl
attribute [local cbv_eval] decimalDigit5
private theorem decimalDigit6 : Nat.digitChar 6 = '6' :=
  Nat.digitChar_eq_six.mpr rfl
attribute [local cbv_eval] decimalDigit6
private theorem decimalDigit7 : Nat.digitChar 7 = '7' :=
  Nat.digitChar_eq_seven.mpr rfl
attribute [local cbv_eval] decimalDigit7
private theorem decimalDigit8 : Nat.digitChar 8 = '8' :=
  Nat.digitChar_eq_eight.mpr rfl
attribute [local cbv_eval] decimalDigit8
private theorem decimalDigit9 : Nat.digitChar 9 = '9' :=
  Nat.digitChar_eq_nine.mpr rfl
attribute [local cbv_eval] decimalDigit9


/-- The complete formal image includes the emitted fallback after RET. -/
theorem bytes_split (left right : Word) :
    bytes left right = AdditionFunction.code left right ++ fallback.flatMap Ext.encode := by
  simp only [bytes, instructions, AdditionFunction.code, List.flatMap_append]

theorem byte_length (left right : Word) : (bytes left right).length = 156 := by
  rw [bytes_split, List.length_append, AdditionFunction.code_length]
  rfl

/-- Exact actual complete Emit.function text, with all three blocks. -/
theorem actual_render (left right : Word) : text left right = AdditionFunction.render 0 0 left right := by
  have repr0 : Nat.repr 0 = "0" := by cbv
  have repr1 : Nat.repr 1 = "1" := by cbv
  have repr2 : Nat.repr 2 = "2" := by cbv
  have repr8 : Nat.repr 8 = "8" := by cbv
  have repr24 : Nat.repr 24 = "24" := by cbv
  have repr32 : Nat.repr 32 = "32" := by cbv
  have repr40 : Nat.repr 40 = "40" := by cbv
  have repr48 : Nat.repr 48 = "48" := by cbv
  have repr56 : Nat.repr 56 = "56" := by cbv
  have repr64 : Nat.repr 64 = "64" := by cbv
  have repr72 : Nat.repr 72 = "72" := by cbv
  have repr80 : Nat.repr 80 = "80" := by cbv
  have repr88 : Nat.repr 88 = "88" := by cbv
  have repr96 : Nat.repr 96 = "96" := by cbv
  have negative : Int.repr (-(↑(64 : Nat) : Int)) = "-64" := by cbv
  have symbol : Asm.symbol "main" = "\"main\"" := by cbv
  simp only [text, body, bodyLines, Assembly.Scalar.linesText, AdditionFunction.render,
    AdditionBody.render, AdditionBody.operations, Scalar.Operation.render, Scalar.Register.index,
    Prologue.Plan.render, Prologue.renderFrame, Asm.read, Asm.write, Asm.slot,
    Asm.unary, Asm.binary, Epilogue.render, Emit.label, symbol,
    preamble, ending, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil,
    ToString.toString, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
    repr0, repr1, repr2, repr8, repr24, repr32, repr40, repr48, repr56, repr64,
    repr72, repr80, repr88, repr96, negative, Nat.zero_mod]
  apply String.toList_injective
  simp only [String.toList_append, String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
  simp only [List.cons.injEq, true_and]
  apply congrArg (fun chars => (Nat.repr left.toNat).toList ++ chars)
  simp only [List.cons.injEq, true_and]
  apply congrArg (fun chars => (Nat.repr right.toNat).toList ++ chars)
  simp only [List.cons.injEq, true_and]
  have zeroValue : (0 : Word).toNat = 0 := rfl
  rw [zeroValue, repr0]
  rfl

/-- Full local symbol resolution is independent of the immediate words. -/
theorem local_labels (left right : Word) : Local (statements left right) := by
  simp [Local, statements, Prologue.Plan.instructions,
    Prologue.frameInstructions, AdditionBody.instructions, AdditionBody.operations,
    Scalar.Operation.instructions, Epilogue.instructions, fallback]

/-- The real encoder lays out the reachable136 bytes followed by20 fallback
bytes. Both declarations adjacent to the short jump are checked at their PCs. -/
theorem assembles (left right : Word) :
    Assembles labels 0 (statements left right) (bytes left right) 156 := by
  have fallbackLayout : Assembles labels 136 (fallback.map Statement.plain)
      (fallback.flatMap Ext.encode) 156 := Assembly.Scalar.Assembles.plains labels 136 fallback
  have returnLayout : Assembles labels 21
      ((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain)
      ((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode) 136 := by
    have actual : Assembles labels 21
        ((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain)
        ((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode)
        (21 + ((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode).length) :=
      Assembly.Scalar.Assembles.plains labels 21 (AdditionBody.instructions left right ++ Epilogue.instructions)
    have bodyLength : (List.flatMap Ext.encode (AdditionBody.instructions left right)).length = 109 :=
      AdditionBody.code_length left right
    have epilogueLength : (Epilogue.instructions.flatMap Ext.encode).length = 6 := Epilogue.code_length
    simpa only [List.flatMap_append, List.length_append, bodyLength, epilogueLength] using actual
  have later : Assembles labels 21
      (((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain) ++
        .label ".Lccomp.0.0.2" :: fallback.map Statement.plain)
      (((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode) ++
        fallback.flatMap Ext.encode) 156 := Assembly.Scalar.Assembles.append returnLayout (Assembles.label (name := ".Lccomp.0.0.2")
    (by cbv) fallbackLayout)
  have jump : Assembles labels 19
      (.jump ".Lccomp.0.0.1" :: .label ".Lccomp.0.0.1" ::
        (((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain) ++
          .label ".Lccomp.0.0.2" :: fallback.map Statement.plain))
      (Ext.encode (.jmp8 (BitVec.ofInt 8 (displacement 21 (19 + 2)))) ++
        (((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode) ++
          fallback.flatMap Ext.encode)) 156 := Assembles.jump8 (name := ".Lccomp.0.0.1") (pc := 19) (target := 21)
    (by cbv) (by constructor <;> decide +kernel) (Assembles.label (name := ".Lccomp.0.0.1") (by cbv) later)
  have activated : Assembles labels 12
      ((Prologue.frameInstructions 0).map Statement.plain ++
        (.jump ".Lccomp.0.0.1" :: .label ".Lccomp.0.0.1" ::
          (((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain) ++
            .label ".Lccomp.0.0.2" :: fallback.map Statement.plain)))
      ((Prologue.frameInstructions 0).flatMap Ext.encode ++
        (Ext.encode (.jmp8 (BitVec.ofInt 8 (displacement 21 (19 + 2)))) ++
          (((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode) ++
            fallback.flatMap Ext.encode))) 156 := Assembly.Scalar.Assembles.append
    (Assembly.Scalar.Assembles.plains labels 12 (Prologue.frameInstructions 0)) jump
  have complete : Assembles labels 0
      (AdditionFunction.plan.instructions.map Statement.plain ++
        (.label ".Lccomp.0.0.0" :: ((Prologue.frameInstructions 0).map Statement.plain ++
          (.jump ".Lccomp.0.0.1" :: .label ".Lccomp.0.0.1" ::
            (((AdditionBody.instructions left right ++ Epilogue.instructions).map Statement.plain) ++
              .label ".Lccomp.0.0.2" :: fallback.map Statement.plain)))))
      (AdditionFunction.plan.instructions.flatMap Ext.encode ++
        ((Prologue.frameInstructions 0).flatMap Ext.encode ++
          (Ext.encode (.jmp8 (BitVec.ofInt 8 (displacement 21 (19 + 2)))) ++
            (((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode) ++
              fallback.flatMap Ext.encode)))) 156 := Assembly.Scalar.Assembles.append
    (Assembly.Scalar.Assembles.plains labels 0 AdditionFunction.plan.instructions)
    (Assembles.label (name := ".Lccomp.0.0.0") (by cbv) activated)
  have jumpZero : BitVec.ofInt 8 (displacement 21 (19 + 2)) = (0 : BitVec 8) := by decide +kernel
  rw [jumpZero] at complete
  simpa only [statements, bytes, instructions, AdditionFunction.instructions, Prologue.Plan.activate,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    List.map_append, List.singleton_append, List.cons_append, List.nil_append, displacement] using complete

theorem slot_frame (register : Nat) : Prologue.slot register = Assembly.frame (8 * (register + 1)) := by
  simp only [Prologue.slot, Assembly.frame, BitVec.neg_ofNat_eq_ofInt_neg]

private theorem spelled_lines (left right : Word) :
    List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
      (bodyLines left right) (statements left right) := by
  refine .cons (by
    change Assembly.Scalar.Spells ["push", "rbp"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["push", "rbp"] _ from .basic (.push (token := "rbp") (register := .rbp) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rbp", ",", "rsp"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rbp", ",", "rsp"] _ from .basic (.mov (destination := "rbp") (source := "rsp") (d := .rbp) (s := .rsp) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["sub", "rsp", ",", "96"] _
    have selected : Prologue.adjust .sub (↑(96 : Nat) : Int) = .aluI8 .q .sub (.reg .rsp) (BitVec.ofInt 8 96) := by cbv
    rw [selected]
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["sub", "rsp", ",", "96"] _ from .basic (.aluI8 (operation := "sub") (destination := "rsp") (immediate := ["96"]) (op := .sub) (d := .rsp) (n := 96) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["and", "rsp", ",", "-", "64"] _
    have selected : Prologue.adjust .and (-(↑(64 : Nat) : Int)) = .aluI8 .q .and (.reg .rsp) (BitVec.ofInt 8 (-64)) := by cbv
    rw [selected]
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["and", "rsp", ",", "-", "64"] _ from .basic (.aluI8 (operation := "and") (destination := "rsp") (immediate := ["-", "64"]) (op := .and) (d := .rsp) (n := -64) (by cbv) (by cbv) (by cbv) (by decide +kernel) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 4) ((statements left right).drop 4)
  refine .cons (by
    change Assembly.Scalar.Spells [".Lccomp.0.0.0:"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells [".Lccomp.0.0.0:"] _ from .basic (.label (name := ".Lccomp.0.0.0") (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "rsp"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "rsp"] _ from .basic (.mov (destination := "rax") (source := "rsp") (d := .rax) (s := .rsp) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "8", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "8", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "8") (s := .rax) (n := 8) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["jmp", ".Lccomp.0.0.1"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["jmp", ".Lccomp.0.0.1"] _ from .basic (.jump (name := ".Lccomp.0.0.1") (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells [".Lccomp.0.0.1:"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells [".Lccomp.0.0.1:"] _ from .basic (.label (name := ".Lccomp.0.0.1") (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 9) ((statements left right).drop 9)
  refine .cons (by rw [Assembly.Scalar.tokenize_indented_movabs]; exact .basic (movabs_repr left)) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "24") (s := .rax) (n := 24) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"] _ from .basic (.load (destination := "rax") (offset := "24") (d := .rax) (n := 24) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "32", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "32", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "32") (s := .rax) (n := 32) (by cbv) (by cbv) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 14) ((statements left right).drop 14)
  refine .cons (by rw [Assembly.Scalar.tokenize_indented_movabs]; exact .basic (movabs_repr right)) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "40", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "40", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "40") (s := .rax) (n := 40) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "40", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "40", "]"] _ from .basic (.load (destination := "rax") (offset := "40") (d := .rax) (n := 40) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "48", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "48", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "48") (s := .rax) (n := 48) (by cbv) (by cbv) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 19) ((statements left right).drop 19)
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "32", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "32", "]"] _ from .basic (.load (destination := "rax") (offset := "32") (d := .rax) (n := 32) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "56", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "56", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "56") (s := .rax) (n := 56) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "48", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "48", "]"] _ from .basic (.load (destination := "rax") (offset := "48") (d := .rax) (n := 48) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "64", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "64", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "64") (s := .rax) (n := 64) (by cbv) (by cbv) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 25) ((statements left right).drop 25)
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "56", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "56", "]"] _ from .basic (.load (destination := "rax") (offset := "56") (d := .rax) (n := 56) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "r10", ",", "QWORD", "PTR", "[", "rbp", "-", "64", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "r10", ",", "QWORD", "PTR", "[", "rbp", "-", "64", "]"] _ from .basic (.load (destination := "r10") (offset := "64") (d := .r10) (n := 64) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["add", "rax", ",", "r10"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["add", "rax", ",", "r10"] _ from .arithmetic (operation := "add") (destination := "rax") (source := "r10") (op := .add) (d := .rax) (s := .r10) (by cbv) (by cbv) (by cbv))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "72", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "72", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "72") (s := .rax) (n := 72) (by cbv) (by cbv) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 29) ((statements left right).drop 29)
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "72", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "72", "]"] _ from .basic (.load (destination := "rax") (offset := "72") (d := .rax) (n := 72) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "80", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "80", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "80") (s := .rax) (n := 80) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "80", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "80", "]"] _ from .basic (.load (destination := "rax") (offset := "80") (d := .rax) (n := 80) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movsxd", "rax", ",", "eax"] _ from .basic (.movsxd (destination := "rax") (source := "eax") (d := .rax) (s := .rax) (by cbv) (by cbv)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "88", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "88", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "88") (s := .rax) (n := 88) (by cbv) (by cbv) (by decide +kernel)))) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 35) ((statements left right).drop 35)
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "88", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "88", "]"] _ from .basic (.load (destination := "rax") (offset := "88") (d := .rax) (n := 88) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["leave"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["leave"] _ from .basic .leave)) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["ret"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["ret"] _ from .basic .ret)) ?_
  show List.Forall₂ (fun line statement => Assembly.Scalar.Spells (X86.Assembly.tokenize line) statement)
    ((bodyLines left right).drop 38) ((statements left right).drop 38)
  refine .cons (by
    change Assembly.Scalar.Spells [".Lccomp.0.0.2:"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells [".Lccomp.0.0.2:"] _ from .basic (.label (name := ".Lccomp.0.0.2") (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["movabs", "rax", ",", "0"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["movabs", "rax", ",", "0"] _ from .basic (.movabs (destination := "rax") (immediate := "0") (d := .rax) (n := 0) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"] _ from .basic (.store (source := "rax") (offset := "24") (s := .rax) (n := 24) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"] _ from .basic (.load (destination := "rax") (offset := "24") (d := .rax) (n := 24) (by cbv) (by cbv) (by decide +kernel)))) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["leave"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["leave"] _ from .basic .leave)) ?_
  refine .cons (by
    change Assembly.Scalar.Spells ["ret"] _
    simpa only [slot_frame, Scalar.Register.index, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using (show Assembly.Scalar.Spells ["ret"] _ from .basic .ret)) ?_
  exact .nil



private theorem lines_without_newline (left right : Word) :
    ∀ line ∈ bodyLines left right, ∀ c ∈ line.toList, (c == '\n') = false := by
  have checked : (bodyLines left right).all (fun line => line.toList.all (fun c => c != '\n')) = true := by
    simp only [bodyLines, List.all_cons, List.all_nil, String.toList_append, List.all_append,
      Assembly.Scalar.repr_without_newline, Bool.and_true]
    decide +kernel
  intro line member c present
  have lineChecked := List.all_eq_true.mp checked line member
  have different := List.all_eq_true.mp lineChecked c present
  exact beq_eq_false_iff_ne.mpr (bne_iff_ne.mp different)

/-- Genuine full body parsing through the actual tokenizer and splitter. -/
theorem parsed (left right : Word) : Assembly.Scalar.Parses (body left right) (statements left right) :=
  Assembly.Scalar.Parses.of_lines (bodyLines left right) (statements left right)
    (lines_without_newline left right) (spelled_lines left right)

/-- Independent metadata framing and actual body syntax accept every emitted
word pair, including the unreachable fallback. -/
theorem main_syntax (left right : Word) : MainSyntax (text left right) (statements left right) :=
  .function (parsed left right)

private theorem bind_ok {α β : Type} (value : α) (next : α → Except String β) :
    (Except.ok value >>= next) = next value := rfl

theorem emitted (left right : Word) :
    Emit.emit #[AdditionLower.artifact left right] =
      .ok (assembly left right) := by
  have function := AdditionFunction.rendered left right 0 0
  have artifacts : (#[AdditionLower.artifact left right] : Array Silmaril.Compiler.Native.Artifact).toList.zipIdx =
      [(AdditionLower.artifact left right, 0)] := rfl
  have functions : (AdditionLower.artifact left right).mir.funcs.toList.zipIdx =
      [(AdditionLower.function left right, 0)] := rfl
  have objects : (AdditionLower.artifact left right).mir.data = #[] := rfl
  simp only [Emit.emit, artifacts, functions, objects, List.forIn_cons, List.forIn_nil,
    Array.forIn_eq_foldlM, List.foldlM_toArray', List.foldlM_nil,
    bind_pure_comp, map_pure, ForInStep.value_yield]
  change (do
    let functionText ← Emit.function 0 0 (AdditionLower.artifact left right) (AdditionLower.function left right)
    pure (unitPreamble ++ functionText ++ unitEnding)) = _
  rw [function]
  simp only [bind_ok]
  rw [← actual_render]
  rfl

theorem compile_O0 (left right : Int) (bounded : AdditionSource.Bounds left right) (tag : String)
    (optimize : Bool) :
    Driver.compile {opt := some .O0} tag (AdditionSource.program left right) optimize =
      .ok (assembly (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) := by
  unfold Driver.compile
  rw [AdditionLower.compile left right bounded tag]
  simp only [bind_ok]
  have skip : (optimize && ({opt := some .O0} : Silmaril.Compile.Driver.Options).opt != some .O0) = false := by
    cases optimize <;> rfl
  rw [skip]
  exact emitted _ _


/-- Real unit metadata frames the independently parsed complete function. -/
theorem unit_syntax (left right : Word) : UnitSyntax (assembly left right) (statements left right) :=
  .unit (main_syntax left right)

/-- Actual full syntax/layout/encoding supplies an inhabited formal load.
No output-text equality or successful machine run is an admission rule. -/
theorem loads_actual (left right : Word) : Loads (assembly left right) ["a.out"] (image left right) :=
  ⟨left, right, bytes left right, unit_syntax left right, local_labels left right,
    assembles left right, rfl, rfl⟩

/-- Actual installed full bytes, argv, reset state and closed-main return word. -/
theorem loaded (left right : Word) : Loaded ["a.out"] (image left right) :=
  MainLoader.loaded (bytes left right) (by rw [byte_length]; decide +kernel) (by rw [byte_length]; decide +kernel)

theorem fetched (left right : Word) :
    Ext.Loaded (image left right).initial.memory 0x1000 (bytes left right) :=
  MainLoader.code_fetch (bytes left right) (by rw [byte_length]; decide +kernel)

theorem prefix_loaded (left right : Word) :
    Ext.Loaded (image left right).initial.memory 0x1000 (AdditionFunction.code left right) := by
  have sub := Ext.Loaded.fetchBytes_sub (fetched left right) (offset := 0)
    (len := (AdditionFunction.code left right).length)
    (by rw [AdditionFunction.code_length]; decide +kernel)
    (by rw [AdditionFunction.code_length, byte_length]; decide +kernel)
  simpa only [Ext.Loaded, Nat.add_zero, List.drop_zero, bytes_split, List.take_left] using sub

theorem function_entry (left right : Word) :
    AdditionFunction.Entry (image left right).initial.toBase 0x4000 := by
  refine ⟨⟨rfl, True.intro, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change (0x2ff8 : Nat) % 16 = 8
    decide +kernel
  · exact LiteralLoader.return_read (bytes left right)
  · change (0x2ff8 : Nat) + 8 + 8 * (0 - 6) ≤ 2 ^ 64
    decide +kernel
  · change 176 ≤ (0x2ff8 : Nat)
    decide +kernel
  · change (image left right).initial.memory.Permitted .read (0x2ff8 - 96) 96
    apply (Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro index below
    have inside : 0x2000 ≤ 0x2ff8 - 96 + index ∧ 0x2ff8 - 96 + index < 0x3000 := by omega
    simp [Process.Memory.permits, image, MainLoader.image, LiteralLoader.image, Literal42.loadImage,
      Process.Region.Contains, Process.Permissions.allows, inside.1, inside.2]
  · change (image left right).initial.memory.Permitted .write (0x2ff8 - 96) 96
    apply (Process.Memory.checkSpan_iff _ _ _ _).mpr
    refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro index below
    have inside : 0x2000 ≤ 0x2ff8 - 96 + index ∧ 0x2ff8 - 96 + index < 0x3000 := by omega
    simp [Process.Memory.permits, image, MainLoader.image, LiteralLoader.image, Literal42.loadImage,
      Process.Region.Contains, Process.Permissions.allows, inside.1, inside.2]

theorem code_disjoint (left right : Word) :
    Silmaril.X86.FetchTrace.Disjoint 0x1000 (AdditionFunction.code left right)
      (AdditionFunction.footprint ((image left right).initial.state.core.read .rsp)) := by
  intro offset bound
  rw [AdditionFunction.code_length] at bound
  change ¬ ((0x2ff8 - 16 ≤ 0x1000 + offset ∧ 0x1000 + offset < 0x2ff8) ∨
    (0x2ff8 - 96 ≤ 0x1000 + offset ∧ 0x1000 + offset < 0x2ff8 - 24))
  omega

theorem entry (left right : Word) :
    AdditionFeatures.Entry (image left right).initial left right 0x4000 :=
  ⟨function_entry left right, prefix_loaded left right, code_disjoint left right⟩

private def tokenLines (left right : Word) : List (List String) := [
  ["push", "rbp"],
  ["mov", "rbp", ",", "rsp"],
  ["sub", "rsp", ",", "96"],
  ["and", "rsp", ",", "-", "64"],
  [".Lccomp.0.0.0:"],
  ["mov", "rax", ",", "rsp"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "8", "]", ",", "rax"],
  ["jmp", ".Lccomp.0.0.1"],
  [".Lccomp.0.0.1:"],
  ["movabs", "rax", ",", Nat.repr left.toNat],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "32", "]", ",", "rax"],
  ["movabs", "rax", ",", Nat.repr right.toNat],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "40", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "40", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "48", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "32", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "56", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "48", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "64", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "56", "]"],
  ["mov", "r10", ",", "QWORD", "PTR", "[", "rbp", "-", "64", "]"],
  ["add", "rax", ",", "r10"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "72", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "72", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "80", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "80", "]"],
  ["movsxd", "rax", ",", "eax"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "88", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "88", "]"],
  ["leave"],
  ["ret"],
  [".Lccomp.0.0.2:"],
  ["movabs", "rax", ",", "0"],
  ["mov", "QWORD", "PTR", "[", "rbp", "-", "24", "]", ",", "rax"],
  ["mov", "rax", ",", "QWORD", "PTR", "[", "rbp", "-", "24", "]"],
  ["leave"],
  ["ret"]]

private theorem body_tokens (left right : Word) :
    ((X86.Assembly.split '\n' (body left right).toList).map
      (fun chars => X86.Assembly.tokenizeChars chars [] [])) = tokenLines left right ++ [[]] := by
  have actual := Assembly.Scalar.linesText_tokens (bodyLines left right) (lines_without_newline left right)
  have mapped : (bodyLines left right).map X86.Assembly.tokenize = tokenLines left right := by
    simp only [bodyLines, List.map_cons, List.map_nil, Assembly.Scalar.tokenize_indented_movabs]
    rfl
  exact actual.trans (congrArg (fun tokens => tokens ++ [[]]) mapped)

private theorem movabs_selected {expected value : Word}
    (parsed : Assembly.Scalar.Spells ["movabs", "rax", ",", Nat.repr expected.toNat]
      (.plain (.movabs .rax value))) : value = expected := by
  cases parsed with
  | basic basic =>
    generalize tokensEq : ["movabs", "rax", ",", Nat.repr expected.toNat] = tokens at basic
    cases basic with
    | @movabs destination immediate _ n dst number range =>
      have tokenFacts : "rax" = destination ∧ Nat.repr expected.toNat = immediate := by
        simpa only [List.cons.injEq, and_true, true_and] using tokensEq
      have immediateEq : Nat.repr expected.toNat = immediate := tokenFacts.2
      rw [← immediateEq] at number
      have sameNumber : expected.toNat = n :=
        Except.ok.inj ((natural_toString expected.toNat).symm.trans number)
      rw [← sameNumber]
      exact BitVec.ofNat_toNat 64 expected

private theorem parsed_body_words {expectedLeft expectedRight left right : Word}
    (parsed : Assembly.Scalar.Parses (body expectedLeft expectedRight) (statements left right)) :
    left = expectedLeft ∧ right = expectedRight := by
  unfold Assembly.Scalar.Parses at parsed
  rw [body_tokens] at parsed
  have spelled := Assembly.Scalar.Lines.spelled parsed
  have filtered : ((tokenLines expectedLeft expectedRight) ++ [[]]).filter (fun line => !line.isEmpty) =
      tokenLines expectedLeft expectedRight := by simp [tokenLines]
  rw [filtered] at spelled
  have leftParsed := spelled.get (i := 9) (by simp [tokenLines]) (by simp [statements, Prologue.Plan.instructions,
    Prologue.frameInstructions, AdditionBody.instructions, AdditionBody.operations,
    Scalar.Operation.instructions, Epilogue.instructions, fallback])
  have rightParsed := spelled.get (i := 14) (by simp [tokenLines]) (by simp [statements, Prologue.Plan.instructions,
    Prologue.frameInstructions, AdditionBody.instructions, AdditionBody.operations,
    Scalar.Operation.instructions, Epilogue.instructions, fallback])
  change Assembly.Scalar.Spells ["movabs", "rax", ",", Nat.repr expectedLeft.toNat]
    (.plain (.movabs .rax left)) at leftParsed
  change Assembly.Scalar.Spells ["movabs", "rax", ",", Nat.repr expectedRight.toNat]
    (.plain (.movabs .rax right)) at rightParsed
  exact ⟨movabs_selected leftParsed, movabs_selected rightParsed⟩

/-- Both independently parsed immediate words are forced by the actual numeric
parser, at their own full-source token positions. -/
theorem parsed_words {expectedLeft expectedRight left right : Word}
    (parsed : UnitSyntax (assembly expectedLeft expectedRight) (statements left right)) :
    left = expectedLeft ∧ right = expectedRight := by
  generalize unitEq : assembly expectedLeft expectedRight = fullText at parsed
  cases parsed with
  | unit functionSyntax =>
    unfold assembly at unitEq
    have functionEq := (String.append_right_inj unitPreamble).mp
      ((String.append_left_inj unitEnding).mp unitEq)
    rw [← functionEq] at functionSyntax
    generalize mainEq : text expectedLeft expectedRight = functionText at functionSyntax
    cases functionSyntax with
    | function bodyParsed =>
      unfold text at mainEq
      have bodyEq := (String.append_right_inj preamble).mp
        ((String.append_left_inj ending).mp mainEq)
      rw [← bodyEq] at bodyParsed
      exact parsed_body_words bodyParsed

private theorem plan_length : (AdditionFunction.plan.instructions.flatMap Ext.encode).length = 12 := by cbv
private theorem frame_length : ((Prologue.frameInstructions 0).flatMap Ext.encode).length = 7 := by cbv
private theorem return_length (left right : Word) :
    ((AdditionBody.instructions left right ++ Epilogue.instructions).flatMap Ext.encode).length = 115 := by
  rw [List.flatMap_append, List.length_append]
  have bodyLength := AdditionBody.code_length left right
  change (List.flatMap Ext.encode (AdditionBody.instructions left right)).length = 109 at bodyLength
  rw [bodyLength]
  rfl

theorem assembly_unique {left right : Word} {code : List Byte} {endPc : Nat}
    (assembled : Assembles labels 0 (statements left right) code endPc) : code = bytes left right := by
  simp only [statements, List.append_assoc, List.singleton_append] at assembled
  obtain ⟨afterPlan, planBytes, planLayout⟩ := Assembly.Scalar.Assembles.plains_inv
    AdditionFunction.plan.instructions assembled
  rw [plan_length] at planLayout
  change Assembles labels 12 _ afterPlan endPc at planLayout
  cases planLayout with
  | label found planRest =>
    show code = bytes left right
    obtain ⟨afterFrame, frameBytes, frameLayout⟩ := Assembly.Scalar.Assembles.plains_inv
      (Prologue.frameInstructions 0) planRest
    rw [frame_length] at frameLayout
    change Assembles labels 19 _ afterFrame endPc at frameLayout
    cases frameLayout with
    | jump8 found fits jumped =>
      show code = bytes left right
      change some 21 = some _ at found
      cases found
      cases jumped with
      | label declaration later =>
        show code = bytes left right
        obtain ⟨afterReturn, returnBytes, returnLayout⟩ := Assembly.Scalar.Assembles.plains_inv
          (AdditionBody.instructions left right ++ Epilogue.instructions) later
        rw [return_length] at returnLayout
        change Assembles labels 136 _ afterReturn endPc at returnLayout
        cases returnLayout with
        | label found tail =>
          show code = bytes left right
          obtain ⟨empty, fallbackBytes, finished⟩ := Assembly.Scalar.Assembles.plains_inv fallback tail
          cases finished
          simp only [List.append_nil] at fallbackBytes
          have jumpZero : BitVec.ofInt 8 (displacement 21 (19 + 2)) = (0 : BitVec 8) := by decide +kernel
          simp only [bytes, instructions, AdditionFunction.instructions, Prologue.Plan.activate,
            List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [planBytes, frameBytes, returnBytes, fallbackBytes, jumpZero]
          simp only [List.flatMap_append, List.append_assoc]
    | jump32 found fits jumped =>
      change some 21 = some _ at found
      cases found
      cases jumped with
      | label impossible later =>
        change (some 21 : Option Nat) = some 24 at impossible
        cases impossible


/-- Every formal load contains the exact canonical full bytes for the two
independently parsed words. -/
theorem loads_shape {source : String} {arguments : List String} {loaded : Image}
    (accepted : Loads source arguments loaded) :
    ∃ left right, UnitSyntax source (statements left right) ∧
      arguments = ["a.out"] ∧ loaded = image left right := by
  obtain ⟨left, right, code, parsed, localSymbols, assembled, args, selected⟩ := accepted
  have same : code = bytes left right := assembly_unique assembled
  rw [same] at selected
  exact ⟨left, right, parsed, args, selected⟩

/-- Actual full text syntax forces both immediate words, while independent
layout forces every loaded byte, including the unreachable fallback. -/
theorem loads_words {left right : Word} {arguments : List String} {loaded : Image}
    (accepted : Loads (assembly left right) arguments loaded) :
    arguments = ["a.out"] ∧ loaded = image left right := by
  obtain ⟨actualLeft, actualRight, parsed, args, selected⟩ := loads_shape accepted
  obtain ⟨rfl, rfl⟩ := parsed_words parsed
  exact ⟨args, selected⟩

/-- Every load admitted by the explicit formal toolchain establishes the real
closed-main loader contract. No machine behavior is required for acceptance. -/
theorem loads_loaded {source : String} {arguments : List String} {loadedImage : Image}
    (accepted : Loads source arguments loadedImage) : Loaded arguments loadedImage := by
  obtain ⟨left, right, parsed, rfl, rfl⟩ := loads_shape accepted
  exact loaded left right

end Silmaril.Compiler.Native.Correctness.AdditionText
