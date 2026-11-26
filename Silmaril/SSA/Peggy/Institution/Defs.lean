module

public import Silmaril.SSA.Peggy.Dialect.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

/-! # Models and satisfaction for fixed-sort Peggy -/

@[expose] public section

namespace Silmaril.SSA.Peggy

open CategoryTheory
open RVSDG (Tuple)

universe u v w

variable {Data : Type u}

namespace Institution

/-- Models choose carriers for the data sorts and partial primitive operations. -/
abbrev Model (S : Dialect.FixedSortSignature.{u,v} Data) := PEG.Interpretation.{u,v,w} S.ops

/-- A reduct precomposes primitive interpretations with the opcode map. -/
def reduct {S T : Dialect.FixedSortSignature.{u,v} Data} (f : S ⟶ T)
    (m : Model.{u,v,w} T) : Model.{u,v,w} S :=
  m.reduct (Dialect.FixedSortSignature.opcodeMap f)

end Institution

namespace Dialect

variable {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {nodes loops : Nat} {forest : PEG.LoopForest loops}

/-- The guarded Figure 11 denotation at every vertex and iteration index. -/
noncomputable def OpenGraph.denote (g : OpenGraph P params results nodes forest)
    (m : PEG.Interpretation.{u,v,w} P) (input : Tuple m.Value params) : g.graph.Valuation m :=
  g.graph.denote m input (g.graph.demandWellFounded g.wellFormed)

/-- Observe the denotation in root order, retaining bottom at each root. -/
noncomputable def OpenGraph.observe (g : OpenGraph P params results nodes forest)
    (m : PEG.Interpretation.{u,v,w} P) (input : Tuple m.Value params) (i : PEG.Index loops) :
    Tuple (fun ty => Option (m.Value ty)) results :=
  g.graph.observe m (g.denote m input) i

/-- Equality of the ordered root observations for every input and common loop index. -/
def Equation.Holds {S : FixedSortSignature.{u,v} Data} (e : Equation S)
    (m : Institution.Model.{u,v,w} S) : Prop :=
  ∀ (input : Tuple m.Value e.params) (i : PEG.Index e.loops),
    e.lhs.observe m input i = e.rhs.observe m input i

end Dialect
end Silmaril.SSA.Peggy
