module

public import Silmaril.Formats.SExp.Printer

@[expose] public section

namespace Silmaril.Formats.SExpPrinter

universe u
variable {α : Type u}

/-! Build the existing printer's exact output as chunks, then join once.
In particular, a long cons spine does not repeatedly copy its rendered suffix.
The original printer remains the specification and is available unchanged. -/

mutual
  def printSExp2ChunksWith (printAtom : α → String) : SExp2 α → List String → List String
    | .nil, suffix => "()" :: suffix
    | .atom value, suffix => printAtom value :: suffix
    | .cons car cdr, suffix =>
        "(" :: printSExp2ChunksWith printAtom car
          (printTailChunksWith printAtom cdr (")" :: suffix))

  def printTailChunksWith (printAtom : α → String) : SExp2 α → List String → List String
    | .nil, suffix => suffix
    | .atom value, suffix => " . " :: printAtom value :: suffix
    | .cons car cdr, suffix =>
        " " :: printSExp2ChunksWith printAtom car (printTailChunksWith printAtom cdr suffix)
end

private theorem printChunksWith_join (printAtom : α → String) (value : SExp2 α) :
    (∀ suffix, String.join (printSExp2ChunksWith printAtom value suffix) =
      printSExp2With printAtom value ++ String.join suffix) ∧
    (∀ suffix, String.join (printTailChunksWith printAtom value suffix) =
      printTailWith printAtom value ++ String.join suffix) := by
  induction value with
  | nil =>
      constructor <;> intro suffix <;>
        simp [printSExp2ChunksWith, printTailChunksWith, printSExp2With, printTailWith]
  | atom value =>
      constructor <;> intro suffix <;>
        simp [printSExp2ChunksWith, printTailChunksWith, printSExp2With, printTailWith,
          String.append_assoc]
  | cons car cdr ihcar ihcdr =>
      constructor <;> intro suffix
      · simp only [printSExp2ChunksWith, String.join_cons, ihcar.1, ihcdr.2,
          printSExp2With, String.append_assoc]
      · simp only [printTailChunksWith, String.join_cons, ihcar.1, ihcdr.2,
          printTailWith, String.append_assoc]

/-- Chunked implementation, exactly equal to the original printer on every tree,
including improper lists and arbitrary caller-supplied atom printers. -/
def printSExp2FastWith (printAtom : α → String) (value : SExp2 α) : String :=
  String.join (printSExp2ChunksWith printAtom value [])

theorem printSExp2FastWith_eq (printAtom : α → String) (value : SExp2 α) :
    printSExp2FastWith printAtom value = printSExp2With printAtom value := by
  simpa [printSExp2FastWith] using (printChunksWith_join printAtom value).1 []

/-- The compiler may use the proved-equal implementation while existing
definitions and their specification/proof APIs remain unchanged. -/
@[csimp] theorem printSExp2With_eq_fast : @printSExp2With = @printSExp2FastWith := by
  funext α printAtom value
  exact (printSExp2FastWith_eq printAtom value).symm

end Silmaril.Formats.SExpPrinter
