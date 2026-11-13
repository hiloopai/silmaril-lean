module

public import Silmaril.Cerberus.Core.Run.Defs
public import Silmaril.Logic.Institution.Basic
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Cerberus Core as an institution

Models are a Core program, its saved-label environment and its initial machine
state. Behaviors are finite labeled traces or infinite labeled executions of
the imported Core LTS. Sentences are semantic specifications of those behaviors;
a model satisfies a sentence when all of its behaviors satisfy it.

Signatures select a vocabulary of specifications. Inclusion translates sentences
forwards and leaves Core models unchanged, with the satisfaction condition proved
by construction. This supports extending the specification vocabulary without
changing the meaning of an existing assertion. These are semantic predicates,
not a claimed syntax or complete proof calculus for C11 assertions.
-/

@[expose] public section
namespace Silmaril.Cerberus.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Cerberus.Core.Dynamics

/-- Both complete infinite executions and arbitrary finite prefixes are observable.
Finite behaviors retain memory (including stdout), UB, errors and unsupported
endings through the final machine state. -/
inductive Behavior where
  | finite (actions : List Label) (finalState : State)
  | infinite (states : Nat → State) (actions : Nat → Label)

/-- An operational model fixes the source program and execution environment.
Use the imported `Dynamics.initial` to select a C startup state; arbitrary states
also permit local reasoning about compiler passes and continuation frames. -/
structure Model where
  program : Program
  labels : Labels
  initialState : State

/-- Exact relation to the Core LTS, independent of any fuel bound or runner's
choice policy. Every nondeterministic branch remains quantified over. -/
def Model.realises (model : Model) : Behavior → Prop
  | .finite actions finalState =>
      (lts model.program model.labels).MTr model.initialState actions finalState
  | .infinite states actions =>
      states 0 = model.initialState ∧
        ∀ n, (lts model.program model.labels).Tr (states n) (actions n) (states (n + 1))

/-- Same-language refinement reduces the set of possible Core behaviors.
Compiler passes between different IRs additionally need their own explicit
observation translation; this definition does not identify machine states. -/
def Model.Refines (target source : Model) : Prop :=
  ∀ behavior, target.realises behavior → source.realises behavior

/-- A semantic specification of finite and infinite Core behaviors. -/
abbrev Sentence := Behavior → Prop

/-- An observation vocabulary. Arrows are inclusions of vocabularies. -/
abbrev Signature := Set Sentence

/-- Universal satisfaction over the actual Core transition relation. -/
def Satisfies (model : Model) (sentence : Sentence) : Prop :=
  ∀ behavior, model.realises behavior → sentence behavior

/-- The room of a selected specification vocabulary and Core models. -/
def room (signature : Signature) : Room.{0, 0, 0} where
  Sen := {sentence : Sentence // sentence ∈ signature}
  Mod := Cat.of (Discrete Model)
  Sat model sentence := Satisfies model.as sentence.val

/-- Change of vocabulary preserves satisfaction exactly. -/
def inst : Signature ⥤ Room.{0, 0, 0} where
  obj := room
  map inclusion :=
    { sen sentence := ⟨sentence.val, inclusion.le sentence.property⟩
      mod := 𝟭 _
      sat _ _ := Iff.rfl }
  map_id _ := by
    apply Corridor.ext
    · rfl
    · rfl
  map_comp _ _ := by
    apply Corridor.ext
    · rfl
    · rfl

/-- The same institution in the classic sentence/model-functor presentation. -/
def classic : ClassicInstitution Signature :=
  ClassicInstitution.ofRoomFunctor inst

/-- Bundled institution, suitable for later compiler-pass comorphisms. -/
def bundled : Inst.{0, 0, 0, 0, 0} where
  Sign := Signature
  I := inst

/-- Safety: every reachable finite state avoids an undefined-behavior ending.
Infinite executions are checked through all their finite prefixes, which are
separately included in `Model.realises`. Errors and unsupported endings remain
distinct outcomes and are not asserted impossible by this specification. -/
def noUndefinedBehaviour : Sentence
  | .finite _ state => ∀ location ub, state.control ≠ .halt (.ub location ub)
  | .infinite _ _ => True

/-- A stdout postcondition, imposed only on terminal machine states. -/
def terminalOutput (allowed : String → Prop) : Sentence
  | .finite _ state => ∀ outcome, state.control = .halt outcome → allowed state.memory.stdout
  | .infinite _ _ => True

/-- Absence of infinite executions. This does not conflate fuel exhaustion with
termination, or assert that any particular run returns a defined C value. -/
def terminates : Sentence
  | .finite _ _ => True
  | .infinite _ _ => False

end Silmaril.Cerberus.Institution
