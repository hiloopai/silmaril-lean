module

public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.RenderInstructions
public import Silmaril.Wasm.Text.Extensions.AtomicMemory.RenderInstructionsSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.BinaryenMemory

open Silmaril Silmaril.Formats.SExpEncoding Binaryen.Toolkit Wasm.Extensions.BinaryenMemory

theorem leafSyntax?_sound {I : Core.IdCtx} {i : Wasm.Extensions.BinaryenMemory.Leaf} {xs : List SExp}
    (h : leafSyntax? I i = some xs) : LeafT I xs i := by
  cases i with
  | base i => exact .base (AtomicMemory.leafSyntax?_sound h)
  | arrayAccess op type arg =>
    simp only [leafSyntax?] at h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .array (Wat.indexSyntax?_sound hi _) (Wat.memoryArgSyntax?_sound ha _)
  | vectorArrayAccess store type arg =>
    simp only [leafSyntax?] at h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .vectorArray (Wat.indexSyntax?_sound hi _) (Wat.memoryArgSyntax?_sound ha _)
  | orderedAccess op memory arg order =>
    simp only [leafSyntax?] at h
    split at h
    · cases h
    · next horder =>
      simp at horder
      obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      exact .ordered horder (Wat.indexSyntax?_sound hi _) (Wat.memoryArgSyntax?_sound ha _)
  | orderedFence order => cases h; exact .fence

theorem instructionTree?_sound {I : Core.IdCtx} {i : Wasm.Extensions.BinaryenMemory.Instr} {xs : List SExp}
    (h : instructionTree? I i = some xs) : InstrT I xs i :=
  Structured.instructionTree?_sound leafSyntax? (fun _ _ _ h => leafSyntax?_sound h) h

end Silmaril.Wasm.Text.Extensions.BinaryenMemory
