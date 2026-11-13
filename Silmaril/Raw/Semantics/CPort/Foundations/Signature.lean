module

public import Silmaril.Semantics.CPort.Foundations.Types.Defs
/-!
# Instruction interfaces

Typing and effects are independent. A signature may supply either interface;
`Signature` bundles both without adding a purity requirement or effect laws.
-/

@[expose] public section

universe u v w

namespace Silmaril

class HasTy (Φ : Type u) (τ : Type v) where
  src : Φ → τ
  trg : Φ → τ

class HasEff (Φ : Type u) (ε : Type v) where
  eff : Φ → ε

class Signature (Φ : Type u) (τ : Type v) (ε : Type w)
    extends HasTy Φ τ, HasEff Φ ε

variable {Φ : Type u} {τ : Type v} {ε : Type w}

def instrSrc [HasTy Φ τ] (f : Φ) : τ := HasTy.src f
def instrTrg [HasTy Φ τ] (f : Φ) : τ := HasTy.trg f
def instrEff [HasEff Φ ε] (f : Φ) : ε := HasEff.eff f

/-- Primitive purity relative to a chosen effect; independent of typing. -/
def IsPure [HasEff Φ ε] (pureEff : ε) (f : Φ) : Prop := instrEff f = pureEff

end Silmaril
