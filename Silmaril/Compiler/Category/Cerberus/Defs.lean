module

public import Silmaril.Cerberus.Institution.Defs
public import Silmaril.Compiler.Category.Institution.Defs

/-! The category-of-compilers language of actual Cerberus Core LTS models.
Observations retain both finite prefixes and complete infinite executions.
This is a fixed whole-program interface, not a C symbol/ABI signature model.
No Ail elaborator or native compiler correctness is assumed here.
-/

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category

namespace Core
export Silmaril.Cerberus.Institution (Model Behavior Signature Sentence Satisfies room bundled)
end Core

/-- Core's actual operational models and behaviors as a compiler-category
language. In particular the behavior relation is independent of bounded runs,
compiler acceptance, or an elaborator's success set. -/
def language : Language.{0} where
  Iface := PUnit
  Prog := Core.Model
  iface _ := PUnit.unit
  Obs := Core.Behavior
  beh model := {behavior | model.realises behavior}

/-- The full vocabulary needed to interpret every behavioral specification. -/
def fullVocabulary : Core.Signature := Set.univ

/-- Interpret behavior predicates in actual Core models. Model reduction sends
an operational model to its genuine LTS behavior set. Its converse would require
realizing an arbitrary set of behaviors by a Core program, which is not assumed.
-/
def realizationCorridor (signature : language.Iface) :
    language.room signature ⟶ Core.room fullVocabulary where
  sen (sentence : Set Core.Behavior) := ⟨(· ∈ sentence), Set.mem_univ _⟩
  mod := Discrete.functor fun model => {behavior | model.realises behavior}
  sat _ _ := Iff.rfl

/-- The actual operational realization is an institution comorphism. This is
not asserted model-expansive: arbitrary behavior-set models need not be program
semantics. Compiler validity remains a separate proof obligation. -/
def realization : Inst.CoHom language.inst Core.bundled where
  Φ := Discrete.functor fun _ => fullVocabulary
  ρ := Discrete.natTrans fun signature => realizationCorridor signature.as

end Silmaril.Compiler.Category.Cerberus
