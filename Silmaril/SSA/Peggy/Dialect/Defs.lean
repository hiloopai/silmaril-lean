module

public import Mathlib.CategoryTheory.Types.Basic
public import Silmaril.SSA.PEG.Thms

/-!
# Peggy signatures and open equations

A signature varies the instruction alphabet over a fixed type of data sorts.
Opcode maps preserve the ordered operand sorts and result sort exactly. The
PEG control and count sorts, open boundaries and loop frames are shared
verbatim by translation.
-/

@[expose] public section

namespace Silmaril.SSA.Peggy.Dialect

open CategoryTheory

universe u v w

/-- A PEG instruction alphabet over fixed data sorts. -/
structure FixedSortSignature (Data : Type u) where
  ops : PEG.InstructionSet.{u,v} Data

/-- A forward map of opcodes, fiberwise at each ordered operand/result profile. -/
structure FixedSortSignature.Hom {Data : Type u} (P Q : FixedSortSignature.{u,v} Data) where
  op : PEG.InstructionMap P.ops Q.ops

instance {Data : Type u} : Category.{max u v} (FixedSortSignature.{u,v} Data) where
  Hom := FixedSortSignature.Hom
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.op (f.op op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace FixedSortSignature

variable {Data : Type u} {P Q R : FixedSortSignature.{u,v} Data}

/-- Bundle an indexed opcode map as a signature arrow. -/
def ofOpcodeMap (f : PEG.InstructionMap P.ops Q.ops) : P ⟶ Q := ⟨f⟩

/-- Use a signature arrow to relabel primitive nodes of a PEG. -/
def opcodeMap (f : P ⟶ Q) : PEG.InstructionMap P.ops Q.ops :=
  fun op => Hom.op (P := P) (Q := Q) f op

@[simp] theorem opcodeMap_id (P : FixedSortSignature.{u,v} Data) :
    @opcodeMap _ P P (𝟙 P) = (fun {_ _} op => op) := rfl

@[simp] theorem opcodeMap_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    @opcodeMap _ P R (f ≫ g) = (fun {_ _} op => opcodeMap g (opcodeMap f op)) := rfl

end FixedSortSignature

variable {Data : Type u}

/-- An admitted open graph in a specified loop frame. -/
structure OpenGraph (ops : PEG.InstructionSet.{u,v} Data) (params results : List (PEG.Ty Data))
    (nodes : Nat) {loops : Nat} (forest : PEG.LoopForest loops) where
  graph : PEG.Graph ops params results nodes loops
  forest_eq : graph.forest = forest
  wellFormed : graph.WellFormed

variable {P : PEG.InstructionSet.{u,v} Data} {Q : PEG.InstructionSet.{u,w} Data}
variable {params results : List (PEG.Ty Data)} {nodes loops : Nat} {forest : PEG.LoopForest loops}

/-- Relabel opcodes while retaining the interface, loop frame and admission. -/
def OpenGraph.map (f : PEG.InstructionMap P Q) (g : OpenGraph P params results nodes forest) :
    OpenGraph Q params results nodes forest where
  graph := g.graph.mapOps f
  -- The forest projection of `mapOps` is independent of the opcode map.
  forest_eq := (congrArg PEG.Graph.forest g.graph.mapOps_id).trans g.forest_eq
  wellFormed := (g.graph.wellFormed_mapOps f).2 g.wellFormed

/-- An equation between admitted graphs with a common ordered input/output boundary
and loop forest. Each side has its own node table. -/
structure Equation (S : FixedSortSignature.{u,v} Data) where
  params : List (PEG.Ty Data)
  results : List (PEG.Ty Data)
  loops : Nat
  forest : PEG.LoopForest loops
  leftNodes : Nat
  rightNodes : Nat
  lhs : OpenGraph S.ops params results leftNodes forest
  rhs : OpenGraph S.ops params results rightNodes forest

def Equation.map {S T : FixedSortSignature.{u,v} Data} (f : S ⟶ T) (e : Equation S) :
    Equation T where
  params := e.params
  results := e.results
  loops := e.loops
  forest := e.forest
  leftNodes := e.leftNodes
  rightNodes := e.rightNodes
  lhs := e.lhs.map (FixedSortSignature.opcodeMap f)
  rhs := e.rhs.map (FixedSortSignature.opcodeMap f)

end Silmaril.SSA.Peggy.Dialect
