module

public import Silmaril.SSA.Peggy.Dialect.Defs

/-! # Covariant sentence translation for fixed-sort Peggy signatures -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Dialect

open CategoryTheory

universe u v w x

variable {Data : Type u}
variable {P : PEG.InstructionSet.{u,v} Data} {Q : PEG.InstructionSet.{u,w} Data}
variable {R : PEG.InstructionSet.{u,x} Data}
variable {params results : List (PEG.Ty Data)} {nodes loops : Nat} {forest : PEG.LoopForest loops}

@[ext] theorem OpenGraph.ext {a b : OpenGraph P params results nodes forest}
    (h : a.graph = b.graph) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[simp] theorem OpenGraph.map_id (g : OpenGraph P params results nodes forest) :
    g.map (fun op => op) = g :=
  OpenGraph.ext g.graph.mapOps_id

theorem OpenGraph.map_comp (f : PEG.InstructionMap P Q) (g : PEG.InstructionMap Q R)
    (graph : OpenGraph P params results nodes forest) :
    (graph.map f).map g = graph.map (fun op => g (f op)) :=
  OpenGraph.ext (graph.graph.mapOps_comp f g)

variable {S T U : FixedSortSignature.{u,v} Data}

@[simp] theorem Equation.map_id (S : FixedSortSignature.{u,v} Data) (e : Equation S) :
    e.map (𝟙 S) = e := by
  cases e
  simp only [Equation.map, FixedSortSignature.opcodeMap_id, OpenGraph.map_id]

theorem Equation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equation S) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [Equation.map, FixedSortSignature.opcodeMap_comp, OpenGraph.map_comp]

/-- Peggy's equations as a `Type`-valued covariant sentence functor. -/
def sentenceFunctor (Data : Type u) : FixedSortSignature.{u,v} Data ⥤ Type (max u v) where
  obj := Equation
  map f := TypeCat.ofHom (Equation.map f)
  map_id S := by
    ext e
    exact Equation.map_id S e
  map_comp f g := by
    ext e
    exact Equation.map_comp f g e

end Silmaril.SSA.Peggy.Dialect
