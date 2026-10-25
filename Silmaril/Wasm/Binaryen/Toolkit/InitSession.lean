module

public import Silmaril.Wasm.Binaryen.GrowOOMRun

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Execution.Core.Sim Numerics
open GrowWrapper (Forced)
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type} {P : Profile}

/-- A reusable constructor boundary: once an actual initialization is forced to
finish, its module observations are exactly a successful initialization followed
by sessions from that final store. It assumes neither whole-store equality to
another module nor any particular constructor syntax. -/
theorem moduleObs_iff_of_forced_initialization
    (s : Store H) (imports : List ExternAddr) (m : Module)
    (initial final : Config H)
    (initialization : ∀ c, Instantiate P closedHost s m imports c ↔ imports = [] ∧ c = initial)
    (forced : Forced (P := P) initial final) (finished : final.code = [])
    (script : List Call) (bs : List (Behaviour Val)) :
    bs ∈ moduleObs P closedHost s imports m script ↔
      imports = [] ∧ ∃ tail,
        Session P closedHost initial.frame.module final.store script tail ∧
          bs = .returns [] :: tail := by
  have terminal : final.Terminal := ⟨.values [], finished⟩
  have no_step : ∀ c, ¬ Step P closedHost final c :=
    fun _ h => BehaviourRefinement.not_step_of_terminal terminal h
  constructor
  · rintro ⟨c, hi, ho⟩
    obtain ⟨rfl, rfl⟩ := (initialization c).mp hi
    refine ⟨rfl, ?_⟩
    rcases ho with ⟨c', tail, run, hc, session, he⟩ |
      ⟨c', result, run, hr, hn, _⟩ | ⟨hd, _⟩
    · obtain rfl := forced.terminal_eq no_step run ⟨.values [], hc⟩
      exact ⟨tail, session, he⟩
    · obtain rfl := forced.terminal_eq no_step run ⟨result, hr⟩
      have he := (BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
        (BehaviourRefinement.outcome?_eq_some_of_code (r := .values []) finished)
      exact (hn (Option.some.inj he)).elim
    · exact (forced.not_diverges no_step hd).elim
  · rintro ⟨empty, tail, session, rfl⟩
    exact ⟨initial, (initialization initial).mpr ⟨empty, rfl⟩,
      .inl ⟨final, tail, forced.steps, finished, session, rfl⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit
