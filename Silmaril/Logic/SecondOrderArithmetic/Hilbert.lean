module

public import Silmaril.Logic.SecondOrderArithmetic.Systems

@[expose] public section

/-! The independent classical implication/negation fragment. Its bridge to
native derivations is separate from the larger subsystem correspondence. -/
namespace Silmaril.Logic.SecondOrderArithmetic

variable {N : Type}

inductive HilbertProof : Formula N → Type
  | ax1 (φ ψ) : HilbertProof (.imp φ (.imp ψ φ))
  | ax2 (φ ψ χ) : HilbertProof (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | ax3 (φ ψ) : HilbertProof (.imp (.imp (.neg φ) (.neg ψ)) (.imp ψ φ))
  | mp {φ ψ} : HilbertProof φ → HilbertProof (.imp φ ψ) → HilbertProof ψ

/-- The usual five-node derivation of `φ → φ`. -/
def HilbertProof.identity (φ : Formula N) : HilbertProof (.imp φ φ) :=
  .mp (.ax1 φ φ) (.mp (.ax1 φ (.imp φ φ)) (.ax2 φ (.imp φ φ) φ))

variable [DecidableEq N]

def HilbertProof.toProof {φ : Formula N} (S : Subsystem) : HilbertProof φ → Proof S φ
  | .ax1 φ ψ => .axiom (.base (.ax1 φ ψ))
  | .ax2 φ ψ χ => .axiom (.base (.ax2 φ ψ χ))
  | .ax3 φ ψ => .axiom (.base (.ax3 φ ψ))
  | .mp p q => .mp (p.toProof S) (q.toProof S)

end Silmaril.Logic.SecondOrderArithmetic
