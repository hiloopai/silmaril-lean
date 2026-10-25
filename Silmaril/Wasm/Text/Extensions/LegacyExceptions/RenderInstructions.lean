module

public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.Instructions
public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.RenderInstructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.LegacyExceptions

open Silmaril Silmaril.Formats.SExpEncoding Binaryen.Toolkit

abbrev LeafRenderer := Core.IdCtx → Wasm.Extensions.LegacyExceptions.Leaf → Option (List SExp)

def catchSyntaxFuel? (leaf : LeafRenderer) (fuel : Nat) (I : Core.IdCtx)
    (c : TagIdx × Wasm.Extensions.LegacyExceptions.Expr) : Option SExp := do
  let tag ← Wat.indexSyntax? c.1
  let parts ← c.2.mapM (Structured.instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
  pure (L (K "catch" :: tag :: parts.flatten))

def finalSyntaxFuel? (leaf : LeafRenderer) (fuel : Nat) (I : Core.IdCtx) :
    Option Wasm.Extensions.LegacyExceptions.Expr → Option (List SExp)
  | none => some []
  | some is => do
    let parts ← is.mapM (Structured.instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
    pure [L (K "catch_all" :: parts.flatten)]

def leafSyntaxFuel? : Nat → LeafRenderer
  | 0, _, _ => none
  | _ + 1, I, .base i => BinaryenMemory.leafSyntax? I i
  | _ + 1, _, .rethrow label => do pure [K "rethrow", ← Wat.indexSyntax? label]
  | fuel + 1, I, .try_ type body catches all => do
    let header ← Wat.blockTypeSyntaxAt? I type
    let parts ← body.mapM (Structured.instructionTreeFuel? (leafSyntaxFuel? fuel) fuel { I with labels := none :: I.labels })
    let cs ← catches.mapM (catchSyntaxFuel? (leafSyntaxFuel? fuel) fuel I)
    let fs ← finalSyntaxFuel? (leafSyntaxFuel? fuel) fuel I all
    pure [L (K "try" :: (header ++ [L (K "do" :: parts.flatten)] ++ cs ++ fs))]
  | fuel + 1, I, .delegate type body label => do
    let header ← Wat.blockTypeSyntaxAt? I type
    let parts ← body.mapM (Structured.instructionTreeFuel? (leafSyntaxFuel? fuel) fuel { I with labels := none :: I.labels })
    let label ← Wat.indexSyntax? label
    pure [L (K "try" :: (header ++ [L (K "do" :: parts.flatten), L [K "delegate", label]]))]

def leafSyntax? (I : Core.IdCtx) (i : Wasm.Extensions.LegacyExceptions.Leaf) : Option (List SExp) :=
  leafSyntaxFuel? (Wasm.Extensions.LegacyExceptions.leafDepth i) I i

def instructionTree? := Structured.instructionTree? leafSyntax?

end Silmaril.Wasm.Text.Extensions.LegacyExceptions
