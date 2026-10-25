module

public import Silmaril.Logic.SecondOrderArithmetic.Syntax

@[expose] public section

/-! A small Hilbert presentation with explicit logical/equality/arithmetic
constructors for axioms. Its formulas are independent of Metamath trees.
Freshness is deliberately syntactic and includes bound names, matching the
native database's disjoint-variable convention. -/
namespace Silmaril.Logic.SecondOrderArithmetic

variable {N : Type} [DecidableEq N]

/-- All written names, including bound names, with sorts forgotten. This is
stronger than free-name freshness and is used only for native-style schemas. -/
def Formula.names : Formula N → Finset N
  | .equal t u | .less t u => t.names ∪ u.names
  | .member t X => insert X t.names
  | .setEqual X Y => {X, Y}
  | .neg φ => φ.names
  | .imp φ ψ | .iff φ ψ | .conj φ ψ => φ.names ∪ ψ.names
  | .all x φ | .ex x φ | .setAll x φ | .setEx x φ => insert x φ.names

inductive BaseAxiom : Formula N → Prop
  | ax1 (φ : Formula N) (ψ : Formula N) : BaseAxiom (.imp φ (.imp ψ φ))
  | ax2 (φ : Formula N) (ψ : Formula N) (χ : Formula N) : BaseAxiom (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | ax3 (φ : Formula N) (ψ : Formula N) : BaseAxiom (.imp (.imp (.neg φ) (.neg ψ)) (.imp ψ φ))
  | dfBi1 (φ : Formula N) (ψ : Formula N) : BaseAxiom (.imp (.iff φ ψ) (.imp φ ψ))
  | dfBi2 (φ : Formula N) (ψ : Formula N) : BaseAxiom (.imp (.iff φ ψ) (.imp ψ φ))
  | dfBi3 (φ : Formula N) (ψ : Formula N) : BaseAxiom (.imp (.imp φ ψ) (.imp (.imp ψ φ) (.iff φ ψ)))
  | dfAn (φ : Formula N) (ψ : Formula N) : BaseAxiom (.iff (.conj φ ψ) (.neg (.imp φ (.neg ψ))))
  | ax4 (φ : Formula N) (ψ : Formula N) (nx : N) : BaseAxiom (.imp (.all nx (.imp φ ψ)) (.imp (.all nx φ) (.all nx ψ)))
  | ax5 (φ : Formula N) (nx : N) : nx ∉ φ.names → BaseAxiom (.imp φ (.all nx φ))
  | ax6 (nx : N) (ny : N) : BaseAxiom (.neg (.all nx (.neg (.equal (.var nx) (.var ny)))))
  | ax7 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.imp (.equal t v) (.equal u v)))
  | ax10 (φ : Formula N) (nx : N) : BaseAxiom (.imp (.neg (.all nx φ)) (.all nx (.neg (.all nx φ))))
  | ax11 (φ : Formula N) (nx : N) (ny : N) : BaseAxiom (.imp (.all nx (.all ny φ)) (.all ny (.all nx φ)))
  | ax12 (φ : Formula N) (nx : N) (ny : N) : BaseAxiom (.imp (.equal (.var nx) (.var ny)) (.imp (.all ny φ) (.all nx (.imp (.equal (.var nx) (.var ny)) φ))))
  | ax13 (nx : N) (ny : N) (nz : N) : BaseAxiom (.imp (.neg (.equal (.var nx) (.var ny))) (.imp (.equal (.var ny) (.var nz)) (.all nx (.equal (.var ny) (.var nz)))))
  | axTex (nx : N) (t : Term N) : nx ∉ t.names → BaseAxiom (.neg (.all nx (.neg (.equal (.var nx) t))))
  | dfEx (φ : Formula N) (nx : N) : BaseAxiom (.iff (.ex nx φ) (.neg (.all nx (.neg φ))))
  | axS4 (φ : Formula N) (ψ : Formula N) (sX : N) : BaseAxiom (.imp (.setAll sX (.imp φ ψ)) (.imp (.setAll sX φ) (.setAll sX ψ)))
  | axS5 (φ : Formula N) (sX : N) : sX ∉ φ.names → BaseAxiom (.imp φ (.setAll sX φ))
  | axS6 (sX : N) (sY : N) : BaseAxiom (.neg (.setAll sX (.neg (.setEqual sX sY))))
  | axS7 (sX : N) (sY : N) (sZ : N) : BaseAxiom (.imp (.setEqual sX sY) (.imp (.setEqual sX sZ) (.setEqual sY sZ)))
  | axS10 (φ : Formula N) (sX : N) : BaseAxiom (.imp (.neg (.setAll sX φ)) (.setAll sX (.neg (.setAll sX φ))))
  | axS11 (φ : Formula N) (sX : N) (sY : N) : BaseAxiom (.imp (.setAll sX (.setAll sY φ)) (.setAll sY (.setAll sX φ)))
  | axS12 (φ : Formula N) (sX : N) (sY : N) : BaseAxiom (.imp (.setEqual sX sY) (.imp (.setAll sY φ) (.setAll sX (.imp (.setEqual sX sY) φ))))
  | axS13 (sX : N) (sY : N) (sZ : N) : BaseAxiom (.imp (.neg (.setEqual sX sY)) (.imp (.setEqual sY sZ) (.setAll sX (.setEqual sY sZ))))
  | axNs11 (φ : Formula N) (nx : N) (sX : N) : BaseAxiom (.imp (.all nx (.setAll sX φ)) (.setAll sX (.all nx φ)))
  | axSn11 (φ : Formula N) (nx : N) (sX : N) : BaseAxiom (.imp (.setAll sX (.all nx φ)) (.all nx (.setAll sX φ)))
  | dfSex (φ : Formula N) (sX : N) : BaseAxiom (.iff (.setEx sX φ) (.neg (.setAll sX (.neg φ))))
  | dfSeq (nx : N) (sX : N) (sY : N) : BaseAxiom (.iff (.setEqual sX sY) (.all nx (.iff (.member (.var nx) sX) (.member (.var nx) sY))))
  | axEqS (t : Term N) (u : Term N) : BaseAxiom (.imp (.equal t u) (.equal (.succ t) (.succ u)))
  | axEqpl1 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.equal (.add t v) (.add u v)))
  | axEqpl2 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.equal (.add v t) (.add v u)))
  | axEqmu1 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.equal (.mul t v) (.mul u v)))
  | axEqmu2 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.equal (.mul v t) (.mul v u)))
  | axEqlt1 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.imp (.less t v) (.less u v)))
  | axEqlt2 (t : Term N) (u : Term N) (v : Term N) : BaseAxiom (.imp (.equal t u) (.imp (.less v t) (.less v u)))
  | axEqel1 (sX : N) (t : Term N) (u : Term N) : BaseAxiom (.imp (.equal t u) (.imp (.member t sX) (.member u sX)))
  | axEqel2 (sX : N) (sY : N) (t : Term N) : BaseAxiom (.imp (.setEqual sX sY) (.imp (.member t sX) (.member t sY)))
  | axS0 (t : Term N) : BaseAxiom (.neg (.equal (.succ t) (.zero)))
  | axSinj (t : Term N) (u : Term N) : BaseAxiom (.imp (.equal (.succ t) (.succ u)) (.equal t u))
  | axPl0 (t : Term N) : BaseAxiom (.equal (.add t (.zero)) t)
  | axPlS (t : Term N) (u : Term N) : BaseAxiom (.equal (.add t (.succ u)) (.succ (.add t u)))
  | axMu0 (t : Term N) : BaseAxiom (.equal (.mul t (.zero)) (.zero))
  | axMuS (t : Term N) (u : Term N) : BaseAxiom (.equal (.mul t (.succ u)) (.add (.mul t u) t))
  | axLt0 (t : Term N) : BaseAxiom (.neg (.less t (.zero)))
  | axLtS (t : Term N) (u : Term N) : BaseAxiom (.iff (.less t (.succ u)) (.imp (.neg (.less t u)) (.equal t u)))

end Silmaril.Logic.SecondOrderArithmetic
