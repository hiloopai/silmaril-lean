module

public import Silmaril.Wasm.Jco.Bridge.State.Thms

/-!
# The stateful bridge on a counter

`counter` is the stateful module exporting `next : [] → [i32]`. It returns its state and
increments it. `nextMeta` is the world `next: func() -> u32`.

* `counter_ir`: the IR strategy of the module contains the play in which two calls of `next`
  are answered `0` and then `1`. It contains no play in which both are answered `0`
  (`counter_ir_not`).
* `counter_wrap`, `counter_step`: `wrap nextMeta` over the module's instance is `RM.ofFun` of the
  state-passing call, which in state `0` returns `0` and moves to state `1` (by evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Bridge.Example

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Jco (PTy PVal Meta wrap)

/-- The `next` function: return the state, then increment it. -/
def nextFn : String → List Flat → Nat → Option (List Flat × Nat)
  | "next", [], s => some ([Flat.i32 (BitVec.ofNat 32 s)], s + 1)
  | _, _, _ => none

/-- A counter. -/
def counter : SMod Nat := ⟨[("next", ⟨[], [.int .i32]⟩)], 0, nextFn⟩

/-- The world `next: func() -> u32`. -/
def nextMeta : Meta := { world := [⟨"next", [], some (.val .u32)⟩] }

theorem nextMeta_memFree : nextMeta.memFree = true := rfl

/-- The question "call `next`". -/
def qNext : counter.Q := (⟨0, by decide⟩, .flat [])

/-- Two calls are answered `0`, then `1`. -/
theorem counter_ir :
    counter.plays [qNext, qNext]
        [some (.flat [Flat.i32 0]), some (.flat [Flat.i32 1])] ∈ (smodSem Nat).sem counter :=
  (mem_sem_iff counter _ _ rfl).2 rfl

/-- They are not both answered `0`. -/
theorem counter_ir_not :
    counter.plays [qNext, qNext]
        [some (.flat [Flat.i32 0]), some (.flat [Flat.i32 0])] ∉ (smodSem Nat).sem counter := by
  rw [mem_sem_iff counter _ _ rfl]
  intro h
  have e : (counter.answers counter.init [qNext, qNext]).1 =
      [some (.flat [Flat.i32 0]), some (.flat [Flat.i32 1])] := rfl
  rw [e] at h
  have h1 : Flat.i32 (0 : BitVec 32) = Flat.i32 1 := by
    simpa using h
  obtain ⟨-, h2⟩ := Silmaril.Wasm.Execution.Runtime.Value.mk.inj h1
  exact absurd (eq_of_heq h2 : (0 : BitVec 32) = 1) (by decide)

/-- `wrap nextMeta` over the counter is the state-passing call. -/
theorem counter_wrap :
    (wrap nextMeta).callExport counter.inst "next" (([] : List Val).map PVal.val) =
      Silmaril.Wasm.Jco.RM.ofFun (stateCall counter ⟨"next", [], some (.val .u32)⟩ []) := by
  rw [wrap_state nextMeta counter nextMeta_memFree]
  rfl

/-- In state `0` it returns `0` and moves to state `1`. -/
theorem counter_step :
    stateCall counter ⟨"next", [], some (.val .u32)⟩ [] 0 = some (some (.val (.u32 0)), 1) := by
  rfl

end Silmaril.Wasm.Jco.Bridge.Example
