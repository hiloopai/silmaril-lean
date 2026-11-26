module

public import Silmaril.SSA.Peggy.Bridge.Equational.Compiler
import Silmaril.Proofs.SSA.Peggy.Bridge.Equational.Semantics

/-! # Sentence and model translation for the equational bridge -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational

open CategoryTheory Silmaril.Logic.Algebraic

variable {S : Type} {A : ManySorted.Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

/-- A compiled term is a certified loop-free PEG with one root. -/
abbrev TermGraph (A : ManySorted.Signature S) (Γ : Fin k → S) (s : S) :=
  Σ n, Dialect.OpenGraph (Opcode A) (profile Γ) [.data s] n emptyForest

theorem Numbered.wellFormed {t : ManySorted.Term A Γ s} (code : Numbered t) :
    code.graph.WellFormed := Proofs.wellFormed code

def compileTerm (t : ManySorted.Term A Γ s) : TermGraph A Γ s :=
  let code := Numbered.compile t
  ⟨_, ⟨code.graph, rfl, code.wellFormed⟩⟩

def equationOf (lhs rhs : TermGraph A Γ s) : Dialect.Equation ((signature S).obj A) :=
  ⟨profile Γ, [.data s], 0, emptyForest, lhs.1, rhs.1, lhs.2, rhs.2⟩

/-- Compile both terms at the same declared variable context, including unused slots. -/
def compileEquation (e : ManySorted.Equation A) : Dialect.Equation ((signature S).obj A) :=
  equationOf (compileTerm e.lhs) (compileTerm e.rhs)

/-- The model translation lands in the existing category of sorted algebras and homomorphisms. -/
def algebraFunctor (A : ManySorted.Signature S) :
    Silmaril.Inst.Disc (TotalPrimitiveModel ((signature S).obj A)) ⥤ ManySorted.Model A where
  obj := algebra
  map h := eqToHom (congrArg (fun m => algebra m) h.down)
  map_id _ := rfl
  map_comp f g := by cases f; cases g; subst_vars; rfl

end Silmaril.SSA.Peggy.Bridge.Equational
