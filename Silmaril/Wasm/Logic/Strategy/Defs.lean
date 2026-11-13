module

public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Games.Composition.Thms

/-!
# Specifications as strategies: definitions

An interface specification `ISpec E` constrains the questions (`pre`) and the
answers (`post`) of a signature `E`. A play of `E ↠ F` is **assume/guarantee
correct** for an import specification `I` (on `E`) and an export specification
`S` (on `F`) (`AG I S`) if, read from the start, every Proponent move is allowed
for as long as every Opponent move so far was: the component's calls to its
imports satisfy `I.pre` and its answers satisfy `S.post`, provided the questions
it was asked satisfied `S.pre` and the answers its imports gave satisfied
`I.post`. Once Opponent breaks its side, nothing more is required.

`agStrat I S : Strategy E F` is the set of legal assume/guarantee correct plays,
a strategy in the sense of `Silmaril.Games.Strategy` (nonempty, prefix-closed,
receptive). It is the largest strategy meeting the specification; a component
meets it when its strategy refines it.

For Wasm, `WCall H` is the signature of function calls on a store (a question is
a function address, a store and arguments; an answer is the final store and the
`Result`: values, an exception or a trap), and `ctxSpec` reads a specification
context (`Silmaril.Wasm.Logic.Hoare.Ctx`) as an interface specification. The
strategy of an open Wasm module and the theorem that it refines the
assume/guarantee strategy of its specifications are in `Silmaril.Wasm.Logic.Open`.

Partial correctness only: strategies of `Silmaril.Games.Strategy` observe safety
(finite plays), which matches the every-run partial-correctness reading of
`HWP`; divergence (`Silmaril.Games.Div`) is not used.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Strategy

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec)

universe u

/-- An interface specification: allowed questions and allowed answers. -/
structure ISpec (E : Sig.{u}) : Type u where
  /-- Allowed questions. -/
  pre : E.Op → Prop
  /-- Allowed answers to a question. -/
  post : (m : E.Op) → E.Ar m → Prop

variable {E F G : Sig.{u}}

/-- An event allowed by the specification. -/
def ISpec.Good (S : ISpec E) : Ev E → Prop
  | .ask m => S.pre m
  | .ans m n => S.post m n

/-- A move allowed by the import and export specifications. -/
def MoveGood (I : ISpec E) (S : ISpec F) : Move E F → Prop
  | .inl e => I.Good e
  | .inr e => S.Good e

/-- **Assume/guarantee correctness** of a play, read from the start. -/
def AG (I : ISpec E) (S : ISpec F) : List (Move E F) → Prop
  | [] => True
  | m :: p => (Move.IsO m → MoveGood I S m → AG I S p) ∧ (Move.IsP m → MoveGood I S m ∧ AG I S p)

theorem AG.of_append {I : ISpec E} {S : ISpec F} :
    ∀ {p q : List (Move E F)}, AG I S (p ++ q) → AG I S p
  | [], _, _ => trivial
  | _ :: _, _, ⟨ho, hp⟩ => ⟨fun h hg => AG.of_append (ho h hg), fun h => ⟨(hp h).1, AG.of_append (hp h).2⟩⟩

theorem Move.isO_or_isP (m : Move E F) : Move.IsO m ∨ Move.IsP m := by
  rcases m with (_ | _) | (_ | _) <;> simp [Move.IsO, Move.IsP]

theorem Move.not_isO_of_isP' {m : Move E F} (hp : Move.IsP m) : ¬ Move.IsO m := by
  rcases m with (_ | _) | (_ | _) <;> simp_all [Move.IsO, Move.IsP]

theorem AG.append_O {I : ISpec E} {S : ISpec F} {o : Move E F} (ho : Move.IsO o) :
    ∀ {p : List (Move E F)}, AG I S p → AG I S (p ++ [o])
  | [], _ => ⟨fun _ _ => trivial, fun h => absurd ho (Move.not_isO_of_isP' h)⟩
  | _ :: _, ⟨hO, hP⟩ => ⟨fun h hg => AG.append_O ho (hO h hg), fun h => ⟨(hP h).1, AG.append_O ho (hP h).2⟩⟩

/-- **The assume/guarantee strategy** of an import and an export specification. -/
def agStrat (I : ISpec E) (S : ISpec F) : Strategy E F where
  plays := {p | Legal p ∧ AG I S p}
  nil_mem := ⟨Legal.nil, trivial⟩
  legal h := h.1
  of_prefix := fun ⟨hl, ha⟩ ⟨u, hu⟩ => ⟨hl.of_prefix ⟨u, hu⟩, AG.of_append (hu ▸ ha)⟩
  receptive := fun ⟨_, ha⟩ hx hxy ho => ⟨⟨_, hx.append (Path.single hxy)⟩, AG.append_O ho ha⟩

/-! ## Wasm calls -/

/-- The signature of Wasm function calls over stores with host data `H`: a
question is a function address, a store and arguments, an answer the final store
and the result. -/
abbrev WCall (H : Type) : Sig.{0} := ⟨Nat × Store H × List Val, fun _ => Store H × Result⟩

/-- The outcome of a call that ended with a result. -/
def resultOutcome : Result → Outcome
  | .values vs => .normal vs
  | .throw a => .throw a
  | .trap => .trap

/-- A specification context as an interface specification: a call is allowed when
the callee has a specification whose precondition holds; an answer is allowed
when it satisfies every specification of the callee. -/
def ctxSpec {H : Type} (Γ : Ctx H) : ISpec (WCall H) where
  pre q := ∃ S, Γ q.1 = some S ∧ S.pre q.2.1 q.2.2
  post q r := ∀ S, Γ q.1 = some S → S.post q.2.1 q.2.2 r.1 (resultOutcome r.2)

end Silmaril.Wasm.Logic.Strategy
