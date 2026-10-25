module

public import Silmaril.Wasm.Text.Extensions.Structured.Instructions
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntax

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def instructionTreeFuel? {Leaf : Type} (leaf : Core.IdCtx → Leaf → Option (List SExp)) :
    Nat → Core.IdCtx → Wasm.Extensions.Structured.Instr Leaf → Option (List SExp)
  | 0, _, _ => none
  | _ + 1, I, .leaf i => leaf I i
  | fuel + 1, I, .block bt body => do
      let header ← Wat.blockTypeSyntaxAt? I bt
      let parts ← body.mapM (instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
      pure [L (K "block" :: (header ++ parts.flatten))]
  | fuel + 1, I, .loop bt body => do
      let header ← Wat.blockTypeSyntaxAt? I bt
      let parts ← body.mapM (instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
      pure [L (K "loop" :: (header ++ parts.flatten))]
  | fuel + 1, I, .if_ bt left right => do
      let header ← Wat.blockTypeSyntaxAt? I bt
      let ls ← left.mapM (instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
      let rs ← right.mapM (instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
      pure [L (K "if" :: (header ++ [L (K "then" :: ls.flatten), L (K "else" :: rs.flatten)]))]
  | fuel + 1, I, .tryTable bt catches body => do
      let header ← Wat.blockTypeSyntaxAt? I bt
      let cs ← catches.mapM Wat.catchSyntax?
      let parts ← body.mapM (instructionTreeFuel? leaf fuel { I with labels := none :: I.labels })
      pure [L (K "try_table" :: (header ++ cs ++ parts.flatten))]

mutual
  def instructionDepth {Leaf : Type} : Wasm.Extensions.Structured.Instr Leaf → Nat
    | .leaf _ => 1
    | .block _ is | .loop _ is | .tryTable _ _ is => instructionDepths is + 1
    | .if_ _ a b => max (instructionDepths a) (instructionDepths b) + 1
  def instructionDepths {Leaf : Type} : Wasm.Extensions.Structured.Expr Leaf → Nat
    | [] => 0
    | i :: is => max (instructionDepth i) (instructionDepths is)
end

def instructionTree? {Leaf : Type} (leaf : Core.IdCtx → Leaf → Option (List SExp))
    (I : Core.IdCtx) (i : Wasm.Extensions.Structured.Instr Leaf) : Option (List SExp) :=
  instructionTreeFuel? leaf (instructionDepth i) I i

end Silmaril.Wasm.Text.Extensions.Structured
