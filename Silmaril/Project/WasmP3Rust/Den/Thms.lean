module

public import Silmaril.Project.WasmP3Rust.Den.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Play.Thms

/-!
# The semantics of async components: plays are runs

`Strategy.ofLTS` closes the traces of a transition system under prefixes and one more Opponent
move. For the transition system of a reduction semantics (`Reduction.toLTS`), that closure adds
nothing (`mem_traces_of_mem_ofLTS`): after a call the system waits for any answer, and between
questions it accepts any question. So a property of the runs of `red K c` is a property of the
plays of `den`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.Den

open Silmaril.Games

universe u

variable {E F : Sig.{u}} {R : Reduction E F}

/-- The game position of a state of a reduction semantics. -/
def statePos : R.State → Pos E F
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

/-- Silent steps keep the position; visible steps are moves of the game. -/
theorem step_pos {x y : R.State} {l : Option (Move E F)} (h : R.Step x l y) :
    (l = none → statePos x = statePos y) ∧ ∀ o, l = some o → Step (statePos x) o (statePos y) := by
  cases h with
  | ask q => exact ⟨nofun, fun _ e => by cases e; exact .ask q⟩
  | tau _ => exact ⟨fun _ => rfl, nofun⟩
  | call _ => exact ⟨nofun, fun _ e => by cases e; exact .call _ _⟩
  | resume q m k n => exact ⟨nofun, fun _ e => by cases e; exact .reply q m n⟩
  | ret _ => exact ⟨nofun, fun _ e => by cases e; exact .ret _ _⟩

/-- A run is a path of the game. -/
theorem run_path : ∀ {x y : R.State} {s : List (Move E F)}, R.toLTS.Run x s y →
    Path (statePos x) s (statePos y)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .tau hs r => ((step_pos hs).1 rfl) ▸ run_path r
  | _, _, _, .vis hs r => .cons ((step_pos hs).2 _ rfl) (run_path r)

/-- **Receptiveness**: a run extends by every legal Opponent move. -/
theorem run_snoc_O {y : R.State} {s : List (Move E F)} {o : Move E F}
    (h : R.toLTS.Run .idle s y) (hl : Legal (s ++ [o])) (ho : o.IsO) :
    s ++ [o] ∈ R.toLTS.Traces := by
  obtain ⟨z, hz⟩ := hl
  obtain ⟨P, hP, hPz⟩ := Path.concat_iff.1 hz
  have hPy : P = statePos y := Path.det hP (run_path h)
  subst hPy
  cases y with
  | idle =>
    cases hPz with
    | ask q => exact ⟨_, LTS.Run.append h (LTS.Run.of_step (L := R.toLTS) (Reduction.Step.ask q))⟩
  | run q c =>
    cases hPz <;> exact absurd ho id
  | wait q m k =>
    cases hPz with
    | reply _ _ n =>
      exact ⟨_, LTS.Run.append h (LTS.Run.of_step (L := R.toLTS) (Reduction.Step.resume q m k n))⟩

/-- **The plays of the strategy of a reduction semantics are its traces.** -/
theorem mem_traces_of_mem_ofLTS {s : List (Move E F)} (hs : s ∈ Strategy.ofLTS R.toLTS) :
    s ∈ R.toLTS.Traces := by
  obtain ⟨hl, u, hu, hp⟩ := hs
  have hpre : ∀ p, p <+: u → p ∈ R.toLTS.Traces := fun p hp' => by
    rcases hu with rfl | ⟨hu, -⟩
    · rw [List.prefix_nil.1 hp']; exact ⟨_, .nil _⟩
    · exact LTS.traces_of_prefix hu hp'
  rcases hp with hp | ⟨p₀, o, rfl, hp₀, ho⟩
  · exact hpre s hp
  · obtain ⟨y, hy⟩ := hpre p₀ hp₀
    exact run_snoc_O hy hl ho

end Silmaril.Project.WasmP3Rust.Den

end
