module

public import Silmaril.Formats.Compression.Inflate.Defs
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawEmission

/-!
Proofs of the per-call output bounds of `Silmaril.Formats.Compression.Inflate.Thms`
for the member machine: every call only appends to the logical output, and
appends at most the call's output capacity. The raw machine's laws are
`RawEmission.call_output` and `RawEmission.call_emitted_capacity`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.InflateOutput

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Inflate
open Silmaril.Formats.Compression.Inflate.Stream

theorem member_feed_output (m : MemberMachine) (input : List UInt8) :
    (m.feed input).output = m.output := by
  cases m with
  | body k c =>
    change (c.machine.feed input).output = c.machine.output
    exact RawMachine.feed_output _ _
  | _ => rfl

theorem member_step_extension (version : Version) (m : MemberMachine) (fuel capacity : Nat) :
    ∃ emitted, (MemberMachine.step version m fuel capacity).output = m.output ++ emitted ∧
      emitted.length ≤ capacity := by
  cases m with
  | header kind p s =>
    refine ⟨[], ?_, Nat.zero_le _⟩
    simp only [MemberMachine.step]
    split <;> rfl
  | gzipHeader g =>
    refine ⟨[], ?_, Nat.zero_le _⟩
    simp only [MemberMachine.step]
    split
    · rfl
    split <;> rfl
  | body kind checked =>
    cases hM : checked.machine with
    | done st =>
      refine ⟨[], ?_, Nat.zero_le _⟩
      simp only [MemberMachine.step, hM, List.append_nil]
      change st.output = checked.machine.output
      rw [hM]; rfl
    | bad e st =>
      refine ⟨[], ?_, Nat.zero_le _⟩
      simp only [MemberMachine.step, hM, List.append_nil]
      change st.output = checked.machine.output
      rw [hM]; rfl
    | _ =>
      obtain ⟨e, he, hle⟩ := RawEmission.step_extension version checked.machine fuel capacity
      refine ⟨e, ?_, hle⟩
      simp only [MemberMachine.step, hM]
      exact he
  | trailer p st =>
    refine ⟨[], ?_, Nat.zero_le _⟩
    simp only [MemberMachine.step, List.append_nil]
    split <;> rfl
  | done st => exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩
  | bad e st => exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩

/-- One call of the member machine appends at most its output capacity. -/
theorem member_call_extension (version : Version) (m : MemberMachine) (call : RawMachine.Call) :
    ∃ emitted, (MemberMachine.applyCall version m call).output = m.output ++ emitted ∧
      emitted.length ≤ call.capacity := by
  obtain ⟨e, he, hle⟩ := member_step_extension version (m.feed call.input) call.schedulerFuel
    call.capacity
  exact ⟨e, by rw [MemberMachine.applyCall, he, member_feed_output], hle⟩

/-- A schedule appends at most the sum of its calls' output capacities. -/
theorem member_run_extension (version : Version) (m : MemberMachine) (calls : List RawMachine.Call) :
    ∃ emitted, (MemberMachine.runCalls version m calls).output = m.output ++ emitted ∧
      emitted.length ≤ (calls.map RawMachine.Call.capacity).sum := by
  induction calls generalizing m with
  | nil => exact ⟨[], (List.append_nil _).symm, Nat.le_refl _⟩
  | cons call calls ih =>
    obtain ⟨e1, h1, b1⟩ := member_call_extension version m call
    obtain ⟨e2, h2, b2⟩ := ih (MemberMachine.applyCall version m call)
    refine ⟨e1 ++ e2, ?_, ?_⟩
    · change (MemberMachine.runCalls version (MemberMachine.applyCall version m call) calls).output = _
      rw [h2, h1, List.append_assoc]
    · simp only [List.length_append, List.map_cons, List.sum_cons]
      omega

end Silmaril.Proofs.Formats.Compression.InflateOutput
