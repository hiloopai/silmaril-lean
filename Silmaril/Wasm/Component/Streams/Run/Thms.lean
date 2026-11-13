module

public import Silmaril.Wasm.Component.Streams.Run.Defs
public import Silmaril.Wasm.Component.Streams.Proc.Thms

/-!
# Running the pipeline: soundness of the drivers

* `stepBy_step`, `firstStep_step`: a driver step is a pipeline step.
* `runRandom_steps`: a random run is a sequence of pipeline steps.
* **`runRandom_correct`**: if a random run from `start T cs` ends with all three components
  finished, the consumer holds `T.run cs.flatten` (by `Proc.pipeline_correct`). So every test of
  `tools/wasm-streams` that finishes is covered by the theorem; the tests add the evidence that
  the runs do finish (no deadlock) under the schedules tried.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Run

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Proc

variable {σ : Type}

theorem stepBy_step (T : Tr σ Val Val) (N : Nat) (ch : Choice) (s s' : Sys σ)
    (h : stepBy T N ch s = some s') : Step T N s s' := by
  cases ch with
  | prod =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Step.prod hq
  | trans =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Step.trans hq
  | cons n =>
    by_cases hn : 0 < n
    · have h' : (cStep n s.st s.c).map (fun q => { s with st := q.1, c := q.2 }) = some s' := by
        simpa only [stepBy, hn, ↓reduceIte] using h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h'
      exact Step.cons n hn hq
    · simp [stepBy, hn] at h

theorem firstStep_step (T : Tr σ Val Val) (N : Nat) (s s' : Sys σ) :
    ∀ chs, firstStep T N s chs = some s' → Step T N s s'
  | [], h => by cases h
  | ch :: chs, h => by
    unfold firstStep at h
    split at h
    · rename_i s'' hs
      cases h
      exact stepBy_step T N ch s _ hs
    · exact firstStep_step T N s s' chs h

theorem runRandom_steps (T : Tr σ Val Val) (N maxRead : Nat) :
    ∀ fuel seed (s : Sys σ), Steps T N s (runRandom T N maxRead fuel seed s).1
  | 0, _, s => Steps.refl s
  | fuel + 1, seed, s => by
    unfold runRandom
    split
    · rename_i s' hs
      exact steps_head (firstStep_step T N s s' _ hs) (runRandom_steps T N maxRead fuel (lcg seed) s')
    · exact Steps.refl s
where
  steps_head {a b c : Sys σ} (h : Step T N a b) (hs : Steps T N b c) : Steps T N a c := by
    induction hs with
    | refl => exact Steps.tail (Steps.refl a) h
    | tail _ h' ih => exact Steps.tail ih h'

/-- **A finished random run computes `T.run` of the input.** -/
theorem runRandom_correct (T : Tr σ Val Val) (N maxRead fuel seed : Nat) (cs : List (List Val))
    (s₀ : Sys σ) (h0 : start T cs = some s₀) (acc : List Val)
    (hf : finished (runRandom T N maxRead fuel seed s₀).1 = some acc) :
    acc = T.run cs.flatten := by
  obtain ⟨st₀, hst, rfl⟩ := Option.map_eq_some_iff.mp h0
  have hR : Reach T N cs (runRandom T N maxRead fuel seed _).1 :=
    ⟨st₀, hst, runRandom_steps T N maxRead fuel seed _⟩
  unfold finished at hf
  split at hf
  · rename_i hp ht hc
    cases hf
    exact pipeline_correct T N cs _ hR hp ht _ hc
  · cases hf

end Silmaril.Wasm.Component.Streams.Run
