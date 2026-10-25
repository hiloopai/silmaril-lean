module

public import Silmaril.Wasm.Text.Extensions.SharedMemory.RenderTypes
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

theorem memoryTypeSyntax?_sound {m : MemoryType} {xs : List SExp}
    (h : memoryTypeSyntax? m = some xs) : MemTypeT xs m := by
  unfold memoryTypeSyntax? at h
  obtain ⟨ys, hy, h⟩ := Option.bind_eq_some_iff.mp h
  cases m with
  | mk core shared =>
    cases shared
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def] at h
      cases h
      exact .unshared (Wat.memoryTypeSyntax?_sound hy)
    · simp only [↓reduceIte] at h
      split at h
      · rename_i hmax
        cases h
        exact .shared (Wat.memoryTypeSyntax?_sound hy) hmax
      · cases h

end Silmaril.Wasm.Text.Extensions.SharedMemory
