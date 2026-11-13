module

public import Silmaril.Machine.X86.Open.Defs

/-!
# The open machine: agreement with `Ext`/`Ext8` and the listing law

Proofs behind `Silmaril.Machine.X86.Open.Thms`. The decoder lemmas (`decode_none_append`,
`fetch_undecodable_of`, `decode_new`) are copied, with the `syscall` clause removed, from
public silmaril-lean `Silmaril/Apps/Sha256sum/X86Sys/SegVC8.lean` (rev `35a6f60`), where they
are stated for the Linux process machine.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Open

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (parseRaw PResult Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86.Open

/-! ## Fetch -/

theorem ext_fetch_of_ext8_decoded {memory : Memory} {address : Nat}
    {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : Silmaril.X86.Ext8.fetch memory address = .inl (.decoded i n)) :
    Silmaril.X86.Ext.fetch memory address = .decoded i n := by
  unfold Silmaril.X86.Ext8.fetch at h
  cases hx : Silmaril.X86.Ext.fetch memory address with
  | undecodable =>
    rw [hx] at h
    simp only at h
    split at h
    · split at h <;> cases h
    · cases h
  | truncated => rw [hx] at h; cases h
  | decoded i' n' => rw [hx] at h; cases h; rfl

/-! ## Agreement with `Ext.step` and `Ext8.step` for every designated exit -/

/-- The decoded case of the open step. -/
theorem step_decoded {m : MState} {i : Silmaril.X86.Ext.Instr} {l : Nat}
    (hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl (.decoded i l)) :
    step m = ofResult (Silmaril.X86.Ext.exec i m.core m.memory) := by
  simp only [step, hf]

/-- One `Ext8` step that retires, or that returns to the designated exit, is an open step. -/
theorem step_of_ext8 {exit : Word} {m n : MState}
    (h : Silmaril.X86.Ext8.step exit m = .ext (.retired n) ∨
      Silmaril.X86.Ext8.step exit m = .ext (.returned n) ∨
      Silmaril.X86.Ext8.step exit m = .retired n) :
    step m = some n := by
  unfold Silmaril.X86.Ext8.step at h
  cases hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | inl f =>
    cases f with
    | undecodable => simp [hf] at h
    | truncated => simp [hf] at h
    | decoded i l =>
      rw [hf] at h
      simp only at h
      have he := ext_fetch_of_ext8_decoded hf
      rw [step_decoded hf]
      unfold Silmaril.X86.Ext.step at h
      rw [he] at h
      simp only at h
      cases hx : Silmaril.X86.Ext.exec i m.core m.memory with
      | ok c mem =>
        simp only [hx] at h
        simp only [ofResult]
        by_cases hc : i = .ret ∧ c.rip = exit
        · simp only [hc, and_self, ite_true] at h
          simp at h
          rw [h]
        · simp only [hc, ite_false] at h
          simp at h
          rw [h]
      | _ => simp [hx] at h
  | inr p =>
    obtain ⟨i, l⟩ := p
    rw [hf] at h
    simp only at h
    simp only [step, hf]
    cases hx : Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) with
    | ok c mem =>
      rw [hx] at h
      simp only at h
      rcases h with h | h | h <;> cases h
      rfl
    | _ => rw [hx] at h; simp at h

/-- A retirement of `Ext8.stepOpt exit` is an open step. -/
theorem step_of_ext8_stepOpt {exit : Word} {m n : MState}
    (h : Silmaril.X86.Ext8.stepOpt exit m = some n) : step m = some n := by
  unfold Silmaril.X86.Ext8.stepOpt at h
  split at h
  · cases h; exact step_of_ext8 (exit := exit) (.inl (by assumption))
  · cases h; exact step_of_ext8 (exit := exit) (.inr (.inr (by assumption)))
  · cases h

/-- The return to the designated exit is an open step. -/
theorem step_of_ext8_returned {exit : Word} {m n : MState}
    (h : Silmaril.X86.Ext8.step exit m = .ext (.returned n)) : step m = some n :=
  step_of_ext8 (exit := exit) (.inr (.inl h))

/-- Conversely, an open step is, for every designated exit, a retirement of `Ext8.stepOpt
exit` or the return to `exit`. -/
theorem ext8_of_step {exit : Word} {m n : MState} (h : step m = some n) :
    Silmaril.X86.Ext8.stepOpt exit m = some n ∨
      Silmaril.X86.Ext8.step exit m = .ext (.returned n) := by
  unfold step at h
  unfold Silmaril.X86.Ext8.stepOpt Silmaril.X86.Ext8.step
  cases hf : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | inl f =>
    cases f with
    | undecodable => rw [hf] at h; cases h
    | truncated => rw [hf] at h; cases h
    | decoded i l =>
      rw [hf] at h
      simp only at h ⊢
      unfold Silmaril.X86.Ext.step
      rw [ext_fetch_of_ext8_decoded hf]
      simp only
      cases hx : Silmaril.X86.Ext.exec i m.core m.memory with
      | ok c mem =>
        rw [hx] at h
        simp only [ofResult, Option.some.injEq] at h
        subst h
        by_cases hc : i = .ret ∧ c.rip = exit
        · simp [hc]
        · simp [hc]
      | _ => rw [hx] at h; simp [ofResult] at h
  | inr p =>
    obtain ⟨i, l⟩ := p
    rw [hf] at h
    simp only at h ⊢
    cases hx : Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) with
    | ok c mem =>
      rw [hx] at h
      simp only [ofResult, Option.some.injEq] at h
      subst h
      simp
    | _ => rw [hx] at h; simp [ofResult] at h

/-! ## Runs -/

theorem run_of_ext8 {exit : Word} : ∀ (n : Nat) {a b : MState},
    run (Silmaril.X86.Ext8.stepOpt exit) n a = some b → run step n a = some b
  | 0, _, _, h => h
  | n + 1, a, b, h => by
    simp only [run] at h ⊢
    cases e : Silmaril.X86.Ext8.stepOpt exit a with
    | none => simp [e] at h
    | some mid =>
      rw [e] at h
      simp only [Option.bind_some] at h
      rw [step_of_ext8_stepOpt e]
      exact run_of_ext8 n h

theorem reaches_of_ext8 {exit : Word} {a b : MState}
    (h : Reaches (Silmaril.X86.Ext8.stepOpt exit) a b) : Reaches step a b := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, run_of_ext8 n hn⟩

/-- The state after a `ret` that `Ext.step exit` reports as the return has `rip = exit`. -/
theorem rip_of_ext_returned {exit : Word} {m fin : MState}
    (h : Silmaril.X86.Ext.step exit m = .returned fin) : fin.core.rip = exit := by
  unfold Silmaril.X86.Ext.step at h
  split at h
  · cases h
  · cases h
  · split at h
    · split at h
      · cases h; rename_i hh; exact hh.2
      · cases h
    all_goals cases h

theorem rip_of_ext8_returned {exit : Word} {m fin : MState}
    (h : Silmaril.X86.Ext8.step exit m = .ext (.returned fin)) : fin.core.rip = exit := by
  unfold Silmaril.X86.Ext8.step at h
  split at h
  · cases h
  · cases h
  · simp only [Silmaril.X86.Ext8.Outcome.ext.injEq] at h
    exact rip_of_ext_returned h
  · split at h <;> cases h

/-- **Returning runs are open runs.** An `Ext8.Returns R` run (finitely many retirements,
then the `ret` that pops `R`) is a run of the open machine ending with `rip = R`. -/
theorem returns_open {R : Word} {m m' : MState} (h : Silmaril.X86.Ext8.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R := by
  obtain ⟨n, mid, hrun, hlast⟩ := h
  refine ⟨(reaches_of_ext8 ⟨n, hrun⟩).trans ⟨1, ?_⟩, rip_of_ext8_returned hlast⟩
  simp [run, step_of_ext8_returned hlast]

/-- The same for an `X86.Ext` returning run (`Ext8.returns_of_ext`). -/
theorem returns_open_ext {R : Word} {m m' : MState} (h : Silmaril.X86.Ext.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  returns_open (Silmaril.X86.Ext8.returns_of_ext h)

end Silmaril.Proofs.Machine.X86.Open
