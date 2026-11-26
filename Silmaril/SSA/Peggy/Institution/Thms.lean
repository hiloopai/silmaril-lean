module

public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.SSA.Peggy.Dialect.Thms
public import Silmaril.SSA.Peggy.Institution.Defs

/-! # The fixed-sort Peggy institution -/

@[expose] public section

namespace Silmaril.SSA.Peggy

open CategoryTheory
open RVSDG (Tuple)

universe u v w x

variable {Data : Type u}

namespace Dialect

variable {P : PEG.InstructionSet.{u,v} Data} {Q : PEG.InstructionSet.{u,w} Data}
variable {params results : List (PEG.Ty Data)} {nodes loops : Nat} {forest : PEG.LoopForest loops}

/-- Relabelling and reduct agree at every vertex and index. -/
theorem OpenGraph.denote_map (f : PEG.InstructionMap P Q)
    (g : OpenGraph P params results nodes forest) (m : PEG.Interpretation.{u,w,x} Q)
    (input : Tuple m.Value params) :
    (g.map f).denote m input = g.denote (m.reduct f) input :=
  g.graph.denote_mapOps f input _ _

/-- Root observations commute with opcode relabelling and reduct, including bottom. -/
theorem OpenGraph.observe_map (f : PEG.InstructionMap P Q)
    (g : OpenGraph P params results nodes forest) (m : PEG.Interpretation.{u,w,x} Q)
    (input : Tuple m.Value params) (i : PEG.Index loops) :
    (g.map f).observe m input i = g.observe (m.reduct f) input i :=
  g.graph.observe_denote_mapOps f input _ _ i

/-- Exact satisfaction along a fixed-sort signature morphism. -/
theorem Equation.holds_map {S T : FixedSortSignature.{u,v} Data} (f : S ⟶ T)
    (m : Institution.Model.{u,v,w} T) (e : Equation S) :
    (e.map f).Holds m ↔ e.Holds (Institution.reduct f m) := by
  simp only [Equation.Holds, Equation.map, OpenGraph.observe_map, Institution.reduct]

end Dialect

namespace Institution

open Dialect (FixedSortSignature Equation)
open Silmaril.Logic.Institution (Room)

variable {S T U : FixedSortSignature.{u,v} Data}

@[simp] theorem reduct_id (S : FixedSortSignature.{u,v} Data) (m : Model.{u,v,w} S) :
    reduct (𝟙 S) m = m := rfl

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (m : Model.{u,v,w} U) :
    reduct (f ≫ g) m = reduct f (reduct g m) := rfl

/-- Peggy's discrete model presentation for the shared institution builder. -/
def plain (Data : Type u) :
    Silmaril.Inst.Plain.{max u (v + 1), max u v, max u v, max u v (w + 1)}
      (FixedSortSignature.{u,v} Data) where
  Sen := Equation
  map := Equation.map
  map_id := Equation.map_id
  map_comp := Equation.map_comp
  Mod := Model.{u,v,w}
  reduct := reduct.{u,v,w}
  reduct_id := reduct_id.{u,v,w}
  reduct_comp := reduct_comp.{u,v,w}
  Sat m e := Equation.Holds.{u,v,w} e m
  sat_map := Equation.holds_map.{u,v,w}

/-- The Peggy institution on fixed data sorts, with discrete model categories. -/
abbrev inst (Data : Type u) := (plain.{u,v,w} Data).toInst

theorem sentenceFunctor_inst (Data : Type u) :
    Silmaril.Logic.Institution.sentenceFunctor (inst.{u,v,w} Data).I =
      Dialect.sentenceFunctor.{u,v} Data := rfl

/-- The contravariant model functor of the Peggy institution. -/
abbrev modelFunctor (Data : Type u) :=
  Silmaril.Logic.Institution.modelFunctor (inst.{u,v,w} Data).I

@[simp] theorem modelFunctor_map_obj (f : S ⟶ T) (m : Model.{u,v,w} T) :
    ((modelFunctor.{u,v,w} Data).map f.op).toFunctor.obj m = reduct f m := rfl

@[simp] theorem reductFunctor_id (S : FixedSortSignature.{u,v} Data) :
    ((inst.{u,v,w} Data).I.map (𝟙 S)).mod = 𝟭 _ := by
  simp only [Functor.map_id, Room.id_mod]

theorem reductFunctor_comp (f : S ⟶ T) (g : T ⟶ U) :
    ((inst.{u,v,w} Data).I.map (f ≫ g)).mod =
      ((inst.{u,v,w} Data).I.map g).mod ⋙ ((inst.{u,v,w} Data).I.map f).mod := by
  simp only [Functor.map_comp, Room.comp_mod]

end Institution
end Silmaril.SSA.Peggy
