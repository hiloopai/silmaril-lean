module

public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Recursive.Block

open CategoryTheory

/-- Retain the old definition bodies and add the translated bodies of the entire block at once. -/
def extendPresentation (P : Presentation) (B : Block P.signature) : Presentation where
  signature := B.signature
  body {k} f :=
    if hm : B.members.arity f.val = some k then
      some ((B.body ⟨f.val, hm⟩).toTerm B)
    else
      let old : P.signature.Symbol k := ⟨f.val, by
        have hf := f.property
        cases he : B.members.arity f.val <;> simp_all [Block.signature]⟩
      (P.body old).map (Term.map B.inclusion)

/-- The signature inclusion preserves the name, arity and translated body of each old symbol. -/
def presentationHom (P : Presentation) (B : Block P.signature) :
    P ⟶ B.extendPresentation P where
  signature := B.inclusion
  body {k} f t ht := by
    have old : B.members.arity f.val ≠ some k := by
      intro h
      have declared := f.property
      simp [B.fresh h] at declared
    simp [extendPresentation, Signature.Hom.symbol, old, ht]

/-- Function names are fresh by construction of the block. Check the other half of
`World.Fresh` for each block member before extending a world. -/
def TheoremNamesFresh (W : World) (B : Block W.signature) : Prop :=
  ∀ {name k}, B.members.arity name = some k → W.theoremAt name = none

/-- Extend the definition table and translate the existing named theorem table. -/
def extendWorld (W : World) (B : Block W.signature) (_fresh : B.TheoremNamesFresh W) : World :=
  ⟨B.extendPresentation W.presentation, fun name => (W.theoremAt name).map (Sentence.map B.inclusion)⟩

/-- The recursive world extension composes with the extensions of checked books. -/
def worldExtension (W : World) (B : Block W.signature) (fresh : B.TheoremNamesFresh W) :
    W.Extension (B.extendWorld W fresh) :=
  ⟨B.presentationHom W.presentation, fun name p h => by simp [extendWorld, presentationHom, h]⟩

end Silmaril.Logic.ACL2.Recursive.Block
