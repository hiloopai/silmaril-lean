module

public import Silmaril.Compiler.Category.Cerberus.Hets.Defs

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus.Hets

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category

/-- The graph's operational edge is the genuine Core realization comorphism. -/
theorem realize_edge (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    (graph target convention readback).comor Translation.realize = realization := rfl

/-- The target edge is the existing compiler-category read-back comorphism. -/
theorem observe_edge (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    (graph target convention readback).comor Translation.observe =
      Convention.comorphism readback := rfl

/-- Hets path lifting acts by the declared operational comorphism. -/
theorem realizationPath_comorphism (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    IndexedCoInst.coHom (graph target convention readback).indexed
      ((graph target convention readback).pathHom (realizationPath target convention readback)) =
      realization :=
  (graph target convention readback).coHom_toPath Translation.realize

/-- Hets path lifting preserves the target observation translation exactly. -/
theorem observationPath_comorphism (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) :
    IndexedCoInst.coHom (graph target convention readback).indexed
      ((graph target convention readback).pathHom (observationPath target convention readback)) =
      Convention.comorphism readback :=
  (graph target convention readback).coHom_toPath Translation.observe

/-- The registered operational translation satisfies the actual institution
satisfaction condition, with operational models reduced to their real behaviors.
This does not rely on any compiler or an Ail elaborator accepting a source. -/
theorem operational_satisfaction (target : Language.{0}) (convention : language ⟶ target)
    (readback : Convention.ReadBack convention) (model : Core.Model) (sentence : Core.Sentence) :
    (Core.room fullVocabulary).Sat (Discrete.mk model)
      ((((graph target convention readback).comor Translation.realize).ρ.app
        (Discrete.mk PUnit.unit)).sen {behavior | sentence behavior}) ↔ Core.Satisfies model sentence :=
  Iff.rfl

end Silmaril.Compiler.Category.Cerberus.Hets
