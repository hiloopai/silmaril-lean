module

public import Silmaril.Machine.Abi.Thunk.Defs
public import Silmaril.Machine.Abi.Thms
/-! # Composition theorem for cross-ABI thunks

* `Thunk.Simulates.sound`: a callee that satisfies `B`'s translation of a strict
  C contract and provides the guarantee, reached through a simulating `A`-to-`B`
  thunk, satisfies `A`'s translation of the same C contract on entry states that
  meet the thunk's room assumption.
* `Thunk.Simulates.sound_reduce`: the same at C level, through both
  satisfaction conditions (when the room assumption is trivial).
* `Thunk.Correct.simulates`: C1's `Correct` thunks simulate, with trivial room
  and guarantee.
-/

@[expose] public section
namespace Silmaril.Machine.Abi

open Silmaril.Logic.Institution.Bridges

namespace Convention

variable {V : Vocab} {St D : Type}

/-- A state is improper exactly when its observation can be `none`. -/
theorem observe_none_iff (B : Convention V St D) (p : V.Proto) (s₁ s₂ : St) :
    B.Observe p s₁ s₂ none ↔ ¬ B.Proper p s₁ s₂ := Iff.rfl

/-- Under a strict contract, every final state of a callee that satisfies the
translated contract is well behaved. -/
theorem proper_of_sat {B : Convention V St D} {p : V.Proto}
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))} (strict : Strict c)
    {model : Contracts.Model St St} (callee : Contracts.Sat model (B.translate p c))
    {a : V.Args p} {s₁ : St} (entry : B.Entry p a s₁) (pre : c.pre a) {s₂ : St}
    (ran : s₂ ∈ model s₁) : B.Proper p s₁ s₂ := by
  by_contra improper
  exact strict a pre ((callee s₁ ⟨a, entry, pre⟩).2 s₂ ran a entry pre none improper)

/-- **Composition theorem.** A thunk that simulates `B` callees as `A` callees
transports a `B`-verified callee to the `A`-translated contract, on caller
states that meet the thunk's room assumption. -/
theorem Thunk.Simulates.sound {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    {room : St → Prop} {guar : St → St → Prop} (sim : t.Simulates room guar)
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))} (strict : Strict c)
    {model : Contracts.Model St St} (callee : Contracts.Sat model (B.translate p c))
    (guaranteed : B.Guarantees p c model guar) :
    Contracts.Sat (t.wrap model) (within (A.translate p c) room) := by
  rintro s ⟨⟨a, entry, pre⟩, roomy⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨s₁, entered⟩ := sim.enter_progress a s entry roomy
    have entry₁ := sim.enter_entry a s entry roomy s₁ entered
    obtain ⟨s₂, ran⟩ := (callee s₁ ⟨a, entry₁, pre⟩).1
    have proper := proper_of_sat strict callee entry₁ pre ran
    obtain ⟨s₃, left⟩ := sim.leave_progress a s entry roomy s₁ entered s₂ proper
      (guaranteed a s₁ entry₁ pre s₂ ran)
    exact ⟨s₃, s₁, entered, s₂, ran, left⟩
  · rintro s₃ ⟨s₁, entered, s₂, ran, left⟩ a' entry' pre' o observed
    have entry₁ := sim.enter_entry a' s entry' roomy s₁ entered
    have proper := proper_of_sat strict callee entry₁ pre' ran
    have g := guaranteed a' s₁ entry₁ pre' s₂ ran
    have ret := sim.leave_return a' s entry' roomy s₁ entered s₂ proper g s₃ left
    obtain ⟨⟨r, at_⟩, reflect⟩ := sim.leave_result a' s entry' roomy s₁ entered s₂ proper g s₃ left
    have post := (callee s₁ ⟨a', entry₁, pre'⟩).2 s₂ ran a' entry₁ pre'
    cases o with
    | none => exact absurd ⟨ret, r, at_⟩ observed
    | some r' => exact post (some r') ⟨proper.1, reflect r' observed.2⟩

/-- A trivial room assumption leaves the translated contract unchanged. -/
theorem within_true {Input Obs : Type} (c : Contracts.Contract Input Obs) (model : Contracts.Model Input Obs) :
    Contracts.Sat model (within c fun _ => True) ↔ Contracts.Sat model c :=
  ⟨fun h input pre => h input ⟨pre, trivial⟩, fun h input pre => h input pre.1⟩

/-- The composition theorem read at C level, through both satisfaction
conditions, for thunks without a room assumption. -/
theorem Thunk.Simulates.sound_reduce {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    {guar : St → St → Prop} (sim : t.Simulates (fun _ => True) guar)
    {c : Contracts.Contract (V.Args p) (Option (V.Ret p))} (strict : Strict c)
    {model : Contracts.Model St St} (callee : Contracts.Sat (B.reduce p model) c)
    (guaranteed : B.Guarantees p c model guar) :
    Contracts.Sat (A.reduce p (t.wrap model)) c := by
  have machine := (B.sat_translate p model c).2 callee
  exact (A.sat_translate p _ c).1 ((within_true _ _).1 (sim.sound strict machine guaranteed))

/-- C1's `Correct` thunks are simulations with no room assumption and no callee
guarantee. -/
theorem Thunk.Correct.simulates {A B : Convention V St D} {p : V.Proto} {t : Thunk A B p}
    (correct : t.Correct) (room : St → Prop) (guar : St → St → Prop) :
    t.Simulates room guar where
  enter_entry a s entry _ := correct.enter_entry a s entry
  enter_progress a s entry _ := correct.enter_progress a s entry
  leave_progress a s entry _ _ _ s₂ _ _ := correct.leave_progress a s entry s₂
  leave_return a s entry _ s₁ entered s₂ proper _ s₃ left := by
    by_contra bad
    exact (correct.observe a s entry s₁ entered s₂ s₃ left none
      (fun h => bad h.1)) proper
  leave_result a s entry _ s₁ entered s₂ proper _ s₃ left := by
    refine ⟨?_, fun r at_ => ?_⟩
    · by_contra bad
      exact (correct.observe a s entry s₁ entered s₂ s₃ left none
        (fun h => bad h.2)) proper
    · have ret : A.Return p s s₃ := by
        by_contra bad
        exact (correct.observe a s entry s₁ entered s₂ s₃ left none
          (fun h => bad h.1)) proper
      exact (correct.observe a s entry s₁ entered s₂ s₃ left (some r) ⟨ret, at_⟩).2

end Convention

end Silmaril.Machine.Abi
