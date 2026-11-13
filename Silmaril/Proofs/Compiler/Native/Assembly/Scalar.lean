module

public import Silmaril.Compiler.Native.Assembly.Scalar.Defs
public import Silmaril.Compiler.Native.Assembly.Lexical.Thms
public import Silmaril.Compiler.Native.Assembly.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Assembly.Scalar
open Silmaril Silmaril.X86

/-- Leading emitter indentation is consumed by the actual tokenizer. -/
theorem tokenize_indent (line : String) :
    X86.Assembly.tokenize ("  " ++ line) = X86.Assembly.tokenize line := by
  simp [X86.Assembly.tokenize, String.toList_append, X86.Assembly.tokenizeChars,
    X86.Assembly.flushToken]

theorem tokenize_indented_movabs (value : Word) :
    X86.Assembly.tokenize ("  movabs rax, " ++ Nat.repr value.toNat) =
      ["movabs", "rax", ",", Nat.repr value.toNat] := by
  calc
    _ = X86.Assembly.tokenize ("  " ++ ("movabs rax, " ++ Nat.repr value.toNat)) := by
      rw [← String.append_assoc]
      rfl
    _ = _ := by rw [tokenize_indent, tokenize_movabs_repr]

/-- Decimal immediates cannot inject a structural source newline. -/
theorem repr_without_newline (number : Nat) :
    ((Nat.repr number).toList.all (fun c => c != '\n')) = true := by
  apply List.all_eq_true.mpr
  intro c member
  have digit : c.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) (by simpa using member)
  have different : c ≠ '\n' := fun same => by subst c; contradiction
  exact bne_iff_ne.mpr different

/-- Consecutive typed instructions retain the actual encoder and layout. -/
theorem Assembles.plains (labels : Labels) (pc : Nat) (instructions : List Ext.Instr) :
    Assembly.Assembles labels pc (instructions.map Statement.plain)
      (instructions.flatMap Ext.encode) (pc + (instructions.flatMap Ext.encode).length) := by
  induction instructions generalizing pc with
  | nil => exact .nil
  | cons instruction rest ih =>
    simpa only [List.map_cons, List.flatMap_cons, List.length_append, Nat.add_assoc] using
      Assembly.Assembles.plain (ih (pc + (Ext.encode instruction).length))

theorem Assembles.append {labels : Labels} {pc middle finish : Nat}
    {before after : List Statement} {first second : List Byte}
    (initial : Assembly.Assembles labels pc before first middle)
    (later : Assembly.Assembles labels middle after second finish) :
    Assembly.Assembles labels pc (before ++ after) (first ++ second) finish := by
  induction initial with
  | nil => exact later
  | label found rest ih => exact .label found (ih later)
  | plain rest ih => simpa only [List.cons_append, List.append_assoc] using Assembly.Assembles.plain (ih later)
  | jump8 found fits rest ih => simpa only [List.cons_append, List.append_assoc] using Assembly.Assembles.jump8 found fits (ih later)
  | jump32 found fits rest ih => simpa only [List.cons_append, List.append_assoc] using Assembly.Assembles.jump32 found fits (ih later)

/-- Existing grammar derivations remain valid in the modular extension. -/
theorem Lines.basic {tokens : List (List String)} {statements : List Statement}
    (parsed : Assembly.Lines tokens statements) : Lines tokens statements := by
  induction parsed with
  | nil => exact .nil
  | blank rest ih => exact .blank ih
  | cons head rest ih => exact .cons (.basic head) ih

theorem Lines.append {first second : List (List String)} {before after : List Statement}
    (initial : Lines first before) (later : Lines second after) : Lines (first ++ second) (before ++ after) := by
  induction initial with
  | nil => exact later
  | blank rest ih => exact .blank ih
  | cons head rest ih => exact .cons head ih

theorem linesText_toList (lines : List String) :
    (linesText lines).toList = lines.flatMap (fun line => line.toList ++ ['\n']) := by
  induction lines with
  | nil => rfl
  | cons line rest ih =>
    have newline : "\n".toList = ['\n'] := by cbv
    simpa only [linesText, List.foldr_cons, String.toList_append, newline, List.flatMap_cons, List.append_assoc] using
      congrArg (fun chars => line.toList ++ ['\n'] ++ chars) ih

/-- Actual structural splitting of newline-terminated lines, with arbitrary
existing chunks and exactly the real splitter's final blank line. -/
theorem splitAux_lines (lines : List (List Char)) (chunks : List (List Char))
    (without : ∀ line ∈ lines, ∀ c ∈ line, (c == '\n') = false) :
    X86.Assembly.splitAux '\n' (lines.flatMap (fun line => line ++ ['\n'])) [] chunks =
      chunks.reverse ++ lines ++ [[]] := by
  induction lines generalizing chunks with
  | nil => simp [X86.Assembly.splitAux]
  | cons line rest ih =>
    show X86.Assembly.splitAux '\n' ((line :: rest).flatMap (fun line => line ++ ['\n'])) [] chunks =
      chunks.reverse ++ (line :: rest) ++ [[]]
    have first := splitAux_append_without '\n' line ('\n' :: rest.flatMap (fun line => line ++ ['\n'])) [] chunks
      (without line (by simp))
    have consumed : X86.Assembly.splitAux '\n' (line ++ '\n' :: rest.flatMap (fun line => line ++ ['\n'])) [] chunks =
        X86.Assembly.splitAux '\n' (rest.flatMap (fun line => line ++ ['\n'])) [] (line :: chunks) := by
      simpa only [List.reverse_nil, List.append_nil, X86.Assembly.splitAux, beq_self_eq_true,
        ↓reduceIte, List.reverse_reverse] using first
    have tailWithout : ∀ line ∈ rest, ∀ c ∈ line, (c == '\n') = false :=
      fun line member => without line (by simp [member])
    calc
      _ = X86.Assembly.splitAux '\n' (rest.flatMap (fun line => line ++ ['\n'])) [] (line :: chunks) := by
        simpa only [List.flatMap_cons, List.append_assoc, List.singleton_append] using consumed
      _ = (line :: chunks).reverse ++ rest ++ [[]] := ih (line :: chunks) tailWithout
      _ = _ := by simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem split_lines (lines : List (List Char))
    (without : ∀ line ∈ lines, ∀ c ∈ line, (c == '\n') = false) :
    X86.Assembly.split '\n' (lines.flatMap (fun line => line ++ ['\n'])) = lines ++ [[]] :=
  splitAux_lines lines [] without

theorem Lines.of_forall₂ {lines : List String} {statements : List Statement}
    (spelled : List.Forall₂ (fun line statement => Spells (X86.Assembly.tokenize line) statement) lines statements) :
    Lines (lines.map (fun line => X86.Assembly.tokenize line)) statements := by
  induction spelled with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- Per-line real tokenizer/grammar witnesses compose to the actual full
source splitter/tokenizer relation. No alternative parser is introduced. -/
theorem Parses.of_lines (lines : List String) (statements : List Statement)
    (without : ∀ line ∈ lines, ∀ c ∈ line.toList, (c == '\n') = false)
    (spelled : List.Forall₂ (fun line statement => Spells (X86.Assembly.tokenize line) statement) lines statements) :
    Parses (linesText lines) statements := by
  have parsed : Lines (lines.map (fun line => X86.Assembly.tokenize line)) statements := Lines.of_forall₂ spelled
  have charsWithout : ∀ line ∈ lines.map String.toList, ∀ c ∈ line, (c == '\n') = false := by
    intro chars member
    obtain ⟨line, present, same⟩ := List.mem_map.mp member
    exact same ▸ without line present
  have split : X86.Assembly.split '\n' (linesText lines).toList = lines.map String.toList ++ [[]] := by
    rw [linesText_toList]
    simpa only [List.flatMap_map, Function.comp_def] using split_lines (lines.map String.toList) charsWithout
  unfold Parses
  rw [split, List.map_append]
  simpa only [List.map_map, Function.comp_def, X86.Assembly.tokenize, List.map_cons, List.map_nil,
    X86.Assembly.tokenizeChars, X86.Assembly.flushToken, List.isEmpty_nil, ↓reduceIte, List.reverse_nil,
    List.append_nil] using parsed.append (Lines.blank Lines.nil)

/-- Grammar-selected instructions never consume a blank token line. -/
theorem Spells.nonempty {tokens : List String} {statement : Statement}
    (spelled : Spells tokens statement) : tokens.isEmpty = false := by
  cases spelled with
  | basic actual => cases actual <;> rfl
  | arithmetic mnemonic dst src => rfl

/-- Blank lines carry no statement; all other line positions retain their
actual grammar witnesses. -/
theorem Lines.spelled {tokens : List (List String)} {statements : List Statement}
    (parsed : Lines tokens statements) :
    List.Forall₂ Spells (tokens.filter (fun line => !line.isEmpty)) statements := by
  induction parsed with
  | nil => exact .nil
  | blank rest ih => simpa using ih
  | cons head rest ih =>
    simpa only [List.filter_cons, Spells.nonempty head, Bool.not_false, ↓reduceIte] using
      List.Forall₂.cons head ih

/-- A concrete typed prefix fixes both its bytes and the remaining layout. -/
theorem Assembles.plains_inv {labels : Labels} {pc finish : Nat}
    (instructions : List Ext.Instr) {statements : List Statement} {code : List Byte}
    (assembled : Assembly.Assembles labels pc (instructions.map Statement.plain ++ statements) code finish) :
    ∃ suffix, code = instructions.flatMap Ext.encode ++ suffix ∧
      Assembly.Assembles labels (pc + (instructions.flatMap Ext.encode).length) statements suffix finish := by
  induction instructions generalizing pc code with
  | nil => exact ⟨code, rfl, by simpa using assembled⟩
  | cons instruction rest ih =>
    cases assembled with
    | plain later =>
      obtain ⟨suffix, same, tail⟩ := ih later
      refine ⟨suffix, ?_, ?_⟩
      · simpa only [List.flatMap_cons, List.append_assoc] using
          congrArg (fun bytes => Ext.encode instruction ++ bytes) same
      · simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using tail

/-- The actual splitter/tokenizer of newline-terminated source lines, including
the real splitter's final blank line. -/
theorem linesText_tokens (lines : List String)
    (without : ∀ line ∈ lines, ∀ c ∈ line.toList, (c == '\n') = false) :
    ((X86.Assembly.split '\n' (linesText lines).toList).map
      (fun chars => X86.Assembly.tokenizeChars chars [] [])) =
      lines.map X86.Assembly.tokenize ++ [[]] := by
  have charsWithout : ∀ line ∈ lines.map String.toList, ∀ c ∈ line, (c == '\n') = false := by
    intro chars member
    obtain ⟨line, present, same⟩ := List.mem_map.mp member
    exact same ▸ without line present
  have split : X86.Assembly.split '\n' (linesText lines).toList = lines.map String.toList ++ [[]] := by
    rw [linesText_toList]
    simpa only [List.flatMap_map, Function.comp_def] using split_lines (lines.map String.toList) charsWithout
  rw [split, List.map_append]
  simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    X86.Assembly.tokenizeChars, X86.Assembly.flushToken, List.isEmpty_nil, ↓reduceIte, List.reverse_nil]
  apply congrArg (fun tokens => tokens ++ [[]])
  apply List.map_congr_left
  intro line member
  rfl

end Silmaril.Compiler.Native.Assembly.Scalar
