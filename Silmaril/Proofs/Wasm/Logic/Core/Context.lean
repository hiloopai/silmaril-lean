module

public import Silmaril.Wasm.Logic.Core.Defs

/-!
# Runs in evaluation contexts

Lifting runs (`Steps P host`) of Wasm Core 3.0 code through evaluation contexts:
a value prefix and a code suffix (`Steps.ctx`, `Steps.append`), a label
(`Steps.label`) and a frame (`Steps.frame`). These are the generic forms, for
any profile `P` and host semantics `host`, of the lemmas silmaril's `is_sorted` proof
introduced for the deterministic profile; they are the base of the
weakest-precondition calculus (`Silmaril.Wasm.Logic.Core.Thms`).

Also: runs inside an exception handler (`Steps.handler`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- One step in a context of values `vs` before and code `rest` after. -/
theorem Step.ctx {s s' : Store H} {f f' : Frame} {is is' : List Admin} (vs : List Val)
    (rest : List Admin) (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Step P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h hne
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using h

/-- Lift a run through a map on configurations that lifts every step. -/
theorem Steps.map {g : Config H → Config H}
    (hg : ∀ a b, Step P host a b → Step P host (g a) (g b))
    {a b : Config H} (h : Steps P host a b) : Steps P host (g a) (g b) := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact .tail ih (hg _ _ st)

/-- A run in a context of values `vs` before and code `rest` after. -/
theorem Steps.ctx {s s' : Store H} {f f' : Frame} {is is' : List Admin} (vs : List Val)
    (rest : List Admin) (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ :=
  Steps.map
    (g := fun c : Config H => (⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact Step.ctx vs rest st) h

/-- Run code followed by more code. -/
theorem Steps.append {s s' : Store H} {f f' : Frame} {is is' : List Admin} (rest : List Admin)
    (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Steps.ctx [] rest h

/-- A run inside a label. -/
theorem Steps.label {s s' : Store H} {f f' : Frame} {is is' : List Admin} (n : Nat)
    (cont : List Instr) (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ :=
  Steps.map (g := fun c : Config H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact .ctxtLabel st) h

/-- A run inside a frame; the outer frame `f` is untouched. -/
theorem Steps.frame {s s' : Store H} {f fi fi' : Frame} {is is' : List Admin} (n : Nat)
    (h : Steps P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Steps P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ :=
  Steps.map (g := fun c : Config H => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact .ctxtFrame st) h

/-- A run inside an exception handler. -/
theorem Steps.handler {s s' : Store H} {f f' : Frame} {is is' : List Admin} (n : Nat)
    (cs : List Catch) (h : Steps P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P host ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ :=
  Steps.map (g := fun c : Config H => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun a b st => by
      rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩; exact .ctxtHandler st) h

theorem Steps.of_eq {c c' : Config H} (h : c = c') : Steps P host c c' :=
  h ▸ .refl

end Silmaril.Wasm.Logic.Core
