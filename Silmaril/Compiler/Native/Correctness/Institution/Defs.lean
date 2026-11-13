module

public import Silmaril.Compiler.Native.Correctness.Defs
public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Compiler.Category.Cerberus.Process.Defs
/-! Institutions of the actual native compiler's projected observations. The
Core projection forgets intermediate states, memory and labels. Its exact
satisfaction condition concerns only that projection, not arbitrary full-state
Core properties. Native compiler correctness remains a separate obligation. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Compile.Category
namespace Core
export Silmaril.Cerberus.Institution (Model Behavior Signature Sentence Satisfies room bundled)
end Core

/-- A fixed projection of genuine Core behaviors to the native checkpoint's
closed-main observations. Reachable source UB allows any target observation;
defined results preserve exit status and empty output; divergence is retained.
Intermediate prefixes and unsupported/error endings do not justify returns. -/
def ReachesUB : Core.Behavior → Prop
  | .finite _ state => ∃ location ub, state.control = .halt (.ub location ub)
  | .infinite _ _ => False

def ProjectionMatches (behavior : Core.Behavior) (observation : Observation) : Prop :=
  ReachesUB behavior ∨
    Silmaril.Compiler.Category.Cerberus.Process.Observes behavior (observe observation)

def project (model : Core.Model) : Set Observation := {observation |
  ∃ behavior, model.realises behavior ∧ ProjectionMatches behavior observation}

/-- Interpret only projected specifications as full Core behavior predicates.
The quantifier accounts for the relation's many concrete native states with the
same process result. No source state is invented from a native observation. -/
def sentence (specification : Set Observation) : Core.Sentence :=
  fun behavior => ∀ observation, ProjectionMatches behavior observation → observation ∈ specification

def projectionCorridor (domain : Source → Prop) (signature : (sourceLanguage domain).Iface) :
    (sourceLanguage domain).room signature ⟶ Core.room (Set.univ : Core.Signature) where
  sen specification := ⟨sentence specification, Set.mem_univ _⟩
  mod := Discrete.functor project
  sat model specification := by
    change Set Observation at specification
    change (∀ behavior, model.as.realises behavior →
      ∀ observation, ProjectionMatches behavior observation → observation ∈ specification) ↔
      ∀ observation, (∃ behavior, model.as.realises behavior ∧
        ProjectionMatches behavior observation) → observation ∈ specification
    constructor
    · intro satisfied observation ⟨behavior, realised, matching⟩
      exact satisfied behavior realised observation matching
    · intro satisfied behavior realised observation matching
      exact satisfied observation ⟨behavior, realised, matching⟩

/-- The projection has an exact institution satisfaction condition. It does not
assert model expansiveness, native compiler validity or reconstruction of Core
states from a process result. -/
def projection (domain : Source → Prop) : Inst.CoHom (sourceLanguage domain).inst Core.bundled where
  Φ := Discrete.functor fun _ => (Set.univ : Core.Signature)
  ρ := Discrete.natTrans fun signature => projectionCorridor domain signature.as

def readback (domain : Source → Prop) (toolchain : Toolchain domain) :
    Convention.ReadBack (convention domain toolchain) :=
  ⟨id, fun _ _ => Iff.rfl⟩

/-- Concrete native source/target behavioral institutions at the fixed
observation convention. This translation is not a proof of Driver.compile. -/
def native (domain : Source → Prop) (toolchain : Toolchain domain) :
    Inst.CoHom (sourceLanguage domain).inst (targetLanguage toolchain).inst :=
  Convention.comorphism (readback domain toolchain)

end Silmaril.Compiler.Native.Correctness.Institution
