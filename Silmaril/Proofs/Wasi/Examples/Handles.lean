module

public import Silmaril.Wasi.Examples.Defs
public import Silmaril.Wasi.Comp.Thms

/-!
# Client handle protocols: steps used by the example components

`Has d q`: the handle state `q` of `handleProto _ .client` has `d` live, or is the absorbing
environment-fault state. Allocations always succeed and keep every handle; a use of a live
handle keeps the state; a drop of a live handle succeeds; `skip` changes nothing. The same for
lists of events (`run_allocs`, for the several allocations of `get-directories`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Examples

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol HEv handleProto handleStep Role)

/-- `d` is live, or the environment broke the protocol. -/
def Has (d : BitVec 32) (q : Option (List (BitVec 32))) : Prop :=
  q = none ∨ ∃ L, q = some L ∧ d ∈ L

/-- An allocation by the environment always succeeds, makes `d` live and keeps every handle. -/
theorem alloc_step (q : Option (List (BitVec 32))) (d : BitVec 32) :
    ∃ q', handleStep .client q (.alloc d) = some q' ∧ Has d q' ∧ ∀ x, Has x q → Has x q' := by
  cases q with
  | none => exact ⟨none, rfl, .inl rfl, fun _ _ => .inl rfl⟩
  | some L =>
    by_cases hd : d ∈ L
    · exact ⟨none, by simp [handleStep, hd, Silmaril.Wasm.Resource.fault], .inl rfl, fun _ _ => .inl rfl⟩
    · refine ⟨some (d :: L), by simp [handleStep, hd], .inr ⟨_, rfl, List.mem_cons_self⟩, ?_⟩
      rintro x (h | ⟨L', hL', hx⟩)
      · exact absurd h (by simp)
      · exact .inr ⟨_, rfl, List.mem_cons_of_mem _ ((Option.some.inj hL') ▸ hx)⟩

/-- A use of a live handle keeps the state. -/
theorem use_step {q : Option (List (BitVec 32))} {d : BitVec 32} (h : Has d q) :
    handleStep .client q (.use d) = some q := by
  rcases h with rfl | ⟨L, rfl, hd⟩
  · rfl
  · simp [handleStep, hd]

/-- A drop of a live handle succeeds. -/
theorem free_step {q : Option (List (BitVec 32))} {d : BitVec 32} (h : Has d q) :
    ∃ q', handleStep .client q (.free d) = some q' := by
  rcases h with rfl | ⟨L, rfl, hd⟩
  · exact ⟨none, rfl⟩
  · exact ⟨some (L.erase d), by simp [handleStep, hd]⟩

/-- `skip` changes nothing. -/
theorem skip_step (q : Option (List (BitVec 32))) : handleStep .client q .skip = some q := by
  cases q <;> rfl

/-- Runs of allocations succeed and keep every live handle. -/
theorem run_allocs {l : List (HEv (BitVec 32))} (hl : ∀ e ∈ l, ∃ h, e = .alloc h)
    (q : Option (List (BitVec 32))) :
    ∃ q', (handleProto (BitVec 32) .client).run q l = some q' ∧ ∀ x, Has x q → Has x q' := by
  induction l generalizing q with
  | nil => exact ⟨q, rfl, fun _ h => h⟩
  | cons e l ih =>
    obtain ⟨d, rfl⟩ := hl e List.mem_cons_self
    obtain ⟨q₁, h₁, -, hk₁⟩ := alloc_step q d
    obtain ⟨q₂, h₂, hk₂⟩ := ih (fun e he => hl e (List.mem_cons_of_mem _ he)) q₁
    refine ⟨q₂, ?_, fun x hx => hk₂ x (hk₁ x hx)⟩
    show (handleStep .client q (.alloc d)).bind _ = _
    rw [h₁]
    exact h₂

/-- The step of `stdoutHandles`. -/
theorem stdoutHandles_step (q : Option (List (BitVec 32))) (e : WEv) :
    stdoutHandles.step q e = handleStep .client q (stdoutHEv e) := rfl

/-- The step of `fsHandles`. -/
theorem fsHandles_step (q : Option (List (BitVec 32))) (e : WEv) :
    fsHandles.step q e = (handleProto (BitVec 32) .client).run q (fsHEv e) := rfl

end Silmaril.Wasi.Examples
