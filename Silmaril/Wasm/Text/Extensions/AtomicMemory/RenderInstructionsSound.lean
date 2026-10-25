module

public import Silmaril.Wasm.Text.Extensions.AtomicMemory.RenderInstructions
public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructionsSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.AtomicMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Wasm.Extensions.AtomicMemory Binaryen.Toolkit

theorem atomicSyntax?_sound {i : AtomicInstr} {xs : List SExp}
    (h : atomicSyntax? i = some xs) (I : Core.IdCtx) : AtomicT I xs i := by
  cases i with
  | access op memory arg =>
    unfold atomicSyntax? at h
    obtain ⟨index, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨args, ha, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .access (Wat.indexSyntax?_sound hi _) (Wat.memoryArgSyntax?_sound ha _)
  | fence => cases h; exact .fence
  | pause => cases h; exact .pause

theorem leafSyntax?_sound {I : Core.IdCtx} {i : Leaf} {xs : List SExp}
    (h : leafSyntax? I i = some xs) : LeafT I xs i := by
  cases i with
  | core i => exact .core (Wat.instructionSyntaxAt?_sound h)
  | atomic i => exact .atomic (atomicSyntax?_sound h I)

theorem instructionTree?_sound {I : Core.IdCtx} {i : Wasm.Extensions.AtomicMemory.Instr} {xs : List SExp}
    (h : instructionTree? I i = some xs) : InstrT I xs i :=
  Structured.instructionTree?_sound leafSyntax? (fun _ _ _ h => leafSyntax?_sound h) h

end Silmaril.Wasm.Text.Extensions.AtomicMemory
