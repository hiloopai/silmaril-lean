module

public import Silmaril.Compiler.Native.Asm.Defs
/-! Character and UTF-8 specifications of the actual GNU symbol quoter. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Asm

@[simp] theorem symbolChar_backslash : symbolChar '\\' = ['\\', '\\'] := rfl
@[simp] theorem symbolChar_quote : symbolChar '"' = ['\\', '"'] := rfl

theorem symbolChar_other (character : Char) (backslash : character ≠ '\\')
    (quote : character ≠ '"') : symbolChar character = [character] := by
  simp only [symbolChar]

/-- Exact character sequence, including the surrounding quotes. -/
theorem symbol_toList (s : String) :
    (symbol s).toList = '"' :: s.toList.flatMap symbolChar ++ ['"'] := by
  exact String.toList_ofList

/-- The emitted bytes are precisely UTF-8 encoding of the character spec. -/
theorem symbol_toByteArray (s : String) :
    (symbol s).toByteArray =
      ('"' :: s.toList.flatMap symbolChar ++ ['"']).utf8Encode := by
  rw [← String.utf8Encode_toList, symbol_toList]

private theorem plain_flatMap (characters : List Char)
    (ordinary : ∀ character ∈ characters, character ≠ '\\' ∧ character ≠ '"') :
    characters.flatMap symbolChar = characters := by
  revert ordinary
  induction characters with
  | nil => intro _; rfl
  | cons character rest ih =>
      intro ordinary
      have head := ordinary character (by simp)
      rw [List.flatMap_cons, symbolChar_other character head.1 head.2]
      rw [ih (by intro next member; exact ordinary next (by simp [member]))]
      rfl

/-- Non-special Unicode characters are preserved exactly between the quotes. -/
theorem symbol_of_plain (s : String)
    (ordinary : ∀ character ∈ s.toList, character ≠ '\\' ∧ character ≠ '"') :
    (symbol s).toList = '"' :: s.toList ++ ['"'] := by
  rw [symbol_toList, plain_flatMap s.toList ordinary]

end Silmaril.Compiler.Native.Asm
